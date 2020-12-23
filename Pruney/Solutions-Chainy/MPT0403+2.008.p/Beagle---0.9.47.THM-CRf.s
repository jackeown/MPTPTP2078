%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:42 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  42 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_setfam_1,type,(
    k2_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k2_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(A,k2_setfam_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [E_59,F_60,A_61,B_62] :
      ( r2_hidden(k2_xboole_0(E_59,F_60),k2_setfam_1(A_61,B_62))
      | ~ r2_hidden(F_60,B_62)
      | ~ r2_hidden(E_59,A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    ! [A_63,A_64,B_65] :
      ( r2_hidden(A_63,k2_setfam_1(A_64,B_65))
      | ~ r2_hidden(A_63,B_65)
      | ~ r2_hidden(A_63,A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_73])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_194,plain,(
    ! [A_128,A_129,B_130] :
      ( r1_tarski(A_128,k2_setfam_1(A_129,B_130))
      | ~ r2_hidden('#skF_1'(A_128,k2_setfam_1(A_129,B_130)),B_130)
      | ~ r2_hidden('#skF_1'(A_128,k2_setfam_1(A_129,B_130)),A_129) ) ),
    inference(resolution,[status(thm)],[c_80,c_4])).

tff(c_212,plain,(
    ! [A_136,A_137] :
      ( ~ r2_hidden('#skF_1'(A_136,k2_setfam_1(A_137,A_136)),A_137)
      | r1_tarski(A_136,k2_setfam_1(A_137,A_136)) ) ),
    inference(resolution,[status(thm)],[c_6,c_194])).

tff(c_228,plain,(
    ! [A_138] : r1_tarski(A_138,k2_setfam_1(A_138,A_138)) ),
    inference(resolution,[status(thm)],[c_6,c_212])).

tff(c_34,plain,(
    ! [A_42,B_43] :
      ( r1_setfam_1(A_42,B_43)
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_243,plain,(
    ! [A_138] : r1_setfam_1(A_138,k2_setfam_1(A_138,A_138)) ),
    inference(resolution,[status(thm)],[c_228,c_34])).

tff(c_36,plain,(
    ~ r1_setfam_1('#skF_8',k2_setfam_1('#skF_8','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:15:02 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.34  
% 2.18/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.34  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 2.18/1.34  
% 2.18/1.34  %Foreground sorts:
% 2.18/1.34  
% 2.18/1.34  
% 2.18/1.34  %Background operators:
% 2.18/1.34  
% 2.18/1.34  
% 2.18/1.34  %Foreground operators:
% 2.18/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.34  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.18/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.18/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.34  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.18/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.34  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.18/1.34  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.18/1.34  tff('#skF_8', type, '#skF_8': $i).
% 2.18/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.34  tff(k2_setfam_1, type, k2_setfam_1: ($i * $i) > $i).
% 2.18/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.18/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.18/1.34  
% 2.18/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.18/1.35  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.18/1.35  tff(f_46, axiom, (![A, B, C]: ((C = k2_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k2_xboole_0(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_setfam_1)).
% 2.18/1.35  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_setfam_1)).
% 2.18/1.35  tff(f_53, negated_conjecture, ~(![A]: r1_setfam_1(A, k2_setfam_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_setfam_1)).
% 2.18/1.35  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.35  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.18/1.35  tff(c_73, plain, (![E_59, F_60, A_61, B_62]: (r2_hidden(k2_xboole_0(E_59, F_60), k2_setfam_1(A_61, B_62)) | ~r2_hidden(F_60, B_62) | ~r2_hidden(E_59, A_61))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.18/1.35  tff(c_80, plain, (![A_63, A_64, B_65]: (r2_hidden(A_63, k2_setfam_1(A_64, B_65)) | ~r2_hidden(A_63, B_65) | ~r2_hidden(A_63, A_64))), inference(superposition, [status(thm), theory('equality')], [c_8, c_73])).
% 2.18/1.35  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.35  tff(c_194, plain, (![A_128, A_129, B_130]: (r1_tarski(A_128, k2_setfam_1(A_129, B_130)) | ~r2_hidden('#skF_1'(A_128, k2_setfam_1(A_129, B_130)), B_130) | ~r2_hidden('#skF_1'(A_128, k2_setfam_1(A_129, B_130)), A_129))), inference(resolution, [status(thm)], [c_80, c_4])).
% 2.18/1.35  tff(c_212, plain, (![A_136, A_137]: (~r2_hidden('#skF_1'(A_136, k2_setfam_1(A_137, A_136)), A_137) | r1_tarski(A_136, k2_setfam_1(A_137, A_136)))), inference(resolution, [status(thm)], [c_6, c_194])).
% 2.18/1.35  tff(c_228, plain, (![A_138]: (r1_tarski(A_138, k2_setfam_1(A_138, A_138)))), inference(resolution, [status(thm)], [c_6, c_212])).
% 2.18/1.35  tff(c_34, plain, (![A_42, B_43]: (r1_setfam_1(A_42, B_43) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.35  tff(c_243, plain, (![A_138]: (r1_setfam_1(A_138, k2_setfam_1(A_138, A_138)))), inference(resolution, [status(thm)], [c_228, c_34])).
% 2.18/1.35  tff(c_36, plain, (~r1_setfam_1('#skF_8', k2_setfam_1('#skF_8', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.18/1.35  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_243, c_36])).
% 2.18/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.35  
% 2.18/1.35  Inference rules
% 2.18/1.35  ----------------------
% 2.18/1.35  #Ref     : 0
% 2.18/1.35  #Sup     : 49
% 2.18/1.35  #Fact    : 0
% 2.18/1.35  #Define  : 0
% 2.18/1.35  #Split   : 0
% 2.18/1.35  #Chain   : 0
% 2.18/1.35  #Close   : 0
% 2.18/1.35  
% 2.18/1.35  Ordering : KBO
% 2.18/1.35  
% 2.18/1.35  Simplification rules
% 2.18/1.35  ----------------------
% 2.18/1.35  #Subsume      : 3
% 2.18/1.35  #Demod        : 1
% 2.18/1.35  #Tautology    : 7
% 2.18/1.35  #SimpNegUnit  : 0
% 2.18/1.35  #BackRed      : 1
% 2.18/1.35  
% 2.18/1.35  #Partial instantiations: 0
% 2.18/1.35  #Strategies tried      : 1
% 2.18/1.35  
% 2.18/1.35  Timing (in seconds)
% 2.18/1.35  ----------------------
% 2.18/1.35  Preprocessing        : 0.30
% 2.18/1.35  Parsing              : 0.15
% 2.18/1.35  CNF conversion       : 0.03
% 2.18/1.35  Main loop            : 0.24
% 2.18/1.35  Inferencing          : 0.10
% 2.18/1.35  Reduction            : 0.05
% 2.18/1.35  Demodulation         : 0.03
% 2.18/1.35  BG Simplification    : 0.02
% 2.18/1.35  Subsumption          : 0.06
% 2.18/1.35  Abstraction          : 0.01
% 2.18/1.35  MUC search           : 0.00
% 2.18/1.35  Cooper               : 0.00
% 2.18/1.35  Total                : 0.57
% 2.18/1.35  Index Insertion      : 0.00
% 2.18/1.35  Index Deletion       : 0.00
% 2.18/1.35  Index Matching       : 0.00
% 2.18/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
