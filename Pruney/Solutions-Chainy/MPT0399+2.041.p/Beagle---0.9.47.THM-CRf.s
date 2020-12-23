%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:37 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden('#skF_4'(A_45,B_46,C_47),B_46)
      | ~ r2_hidden(C_47,A_45)
      | ~ r1_setfam_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    ! [A_25,B_26,C_27] :
      ( ~ r1_xboole_0(A_25,B_26)
      | ~ r2_hidden(C_27,k3_xboole_0(A_25,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_39,plain,(
    ! [A_8,C_27] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_27,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_42,plain,(
    ! [C_27] : ~ r2_hidden(C_27,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_39])).

tff(c_115,plain,(
    ! [C_52,A_53] :
      ( ~ r2_hidden(C_52,A_53)
      | ~ r1_setfam_1(A_53,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_91,c_42])).

tff(c_132,plain,(
    ! [A_54] :
      ( ~ r1_setfam_1(A_54,k1_xboole_0)
      | k1_xboole_0 = A_54 ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_143,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_132])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n018.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.15  
% 1.72/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1
% 1.72/1.15  
% 1.72/1.15  %Foreground sorts:
% 1.72/1.15  
% 1.72/1.15  
% 1.72/1.15  %Background operators:
% 1.72/1.15  
% 1.72/1.15  
% 1.72/1.15  %Foreground operators:
% 1.72/1.15  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.72/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.15  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.72/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.72/1.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.72/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.72/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.72/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.72/1.15  
% 1.72/1.16  tff(f_68, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.72/1.16  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.72/1.16  tff(f_63, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.72/1.16  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.72/1.16  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.72/1.16  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.72/1.16  tff(c_20, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.72/1.16  tff(c_22, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.72/1.16  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.72/1.16  tff(c_91, plain, (![A_45, B_46, C_47]: (r2_hidden('#skF_4'(A_45, B_46, C_47), B_46) | ~r2_hidden(C_47, A_45) | ~r1_setfam_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.72/1.16  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.72/1.16  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.72/1.16  tff(c_32, plain, (![A_25, B_26, C_27]: (~r1_xboole_0(A_25, B_26) | ~r2_hidden(C_27, k3_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.16  tff(c_39, plain, (![A_8, C_27]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_32])).
% 1.72/1.16  tff(c_42, plain, (![C_27]: (~r2_hidden(C_27, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_39])).
% 1.72/1.16  tff(c_115, plain, (![C_52, A_53]: (~r2_hidden(C_52, A_53) | ~r1_setfam_1(A_53, k1_xboole_0))), inference(resolution, [status(thm)], [c_91, c_42])).
% 1.72/1.16  tff(c_132, plain, (![A_54]: (~r1_setfam_1(A_54, k1_xboole_0) | k1_xboole_0=A_54)), inference(resolution, [status(thm)], [c_6, c_115])).
% 1.72/1.16  tff(c_143, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_132])).
% 1.72/1.16  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_143])).
% 1.72/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.16  
% 1.72/1.16  Inference rules
% 1.72/1.16  ----------------------
% 1.72/1.16  #Ref     : 0
% 1.72/1.16  #Sup     : 25
% 1.72/1.16  #Fact    : 0
% 1.72/1.16  #Define  : 0
% 1.72/1.16  #Split   : 0
% 1.72/1.16  #Chain   : 0
% 1.72/1.16  #Close   : 0
% 1.72/1.16  
% 1.72/1.16  Ordering : KBO
% 1.72/1.16  
% 1.72/1.16  Simplification rules
% 1.72/1.16  ----------------------
% 1.72/1.16  #Subsume      : 1
% 1.72/1.16  #Demod        : 5
% 1.72/1.16  #Tautology    : 8
% 1.72/1.16  #SimpNegUnit  : 2
% 1.72/1.16  #BackRed      : 0
% 1.72/1.16  
% 1.72/1.16  #Partial instantiations: 0
% 1.72/1.16  #Strategies tried      : 1
% 1.72/1.16  
% 1.72/1.16  Timing (in seconds)
% 1.72/1.16  ----------------------
% 1.72/1.17  Preprocessing        : 0.28
% 1.72/1.17  Parsing              : 0.15
% 1.72/1.17  CNF conversion       : 0.02
% 1.72/1.17  Main loop            : 0.13
% 1.72/1.17  Inferencing          : 0.06
% 1.72/1.17  Reduction            : 0.03
% 1.72/1.17  Demodulation         : 0.03
% 1.72/1.17  BG Simplification    : 0.01
% 1.72/1.17  Subsumption          : 0.02
% 1.72/1.17  Abstraction          : 0.01
% 1.72/1.17  MUC search           : 0.00
% 1.72/1.17  Cooper               : 0.00
% 1.72/1.17  Total                : 0.44
% 1.72/1.17  Index Insertion      : 0.00
% 1.72/1.17  Index Deletion       : 0.00
% 1.72/1.17  Index Matching       : 0.00
% 1.72/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
