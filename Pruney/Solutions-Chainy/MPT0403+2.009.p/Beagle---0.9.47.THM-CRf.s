%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:42 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   42 (  45 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 (  48 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_tarski > k2_setfam_1 > #nlpp > k3_tarski > k1_tarski > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_36,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k2_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(A,k2_setfam_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_7] : k3_tarski(k1_tarski(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [A_6] : k3_tarski(k1_tarski(A_6)) = k2_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_60])).

tff(c_72,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_108,plain,(
    ! [E_65,F_66,A_67,B_68] :
      ( r2_hidden(k2_xboole_0(E_65,F_66),k2_setfam_1(A_67,B_68))
      | ~ r2_hidden(F_66,B_68)
      | ~ r2_hidden(E_65,A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_115,plain,(
    ! [A_69,A_70,B_71] :
      ( r2_hidden(A_69,k2_setfam_1(A_70,B_71))
      | ~ r2_hidden(A_69,B_71)
      | ~ r2_hidden(A_69,A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_108])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_222,plain,(
    ! [A_136,A_137,B_138] :
      ( r1_tarski(A_136,k2_setfam_1(A_137,B_138))
      | ~ r2_hidden('#skF_1'(A_136,k2_setfam_1(A_137,B_138)),B_138)
      | ~ r2_hidden('#skF_1'(A_136,k2_setfam_1(A_137,B_138)),A_137) ) ),
    inference(resolution,[status(thm)],[c_115,c_4])).

tff(c_235,plain,(
    ! [A_139,A_140] :
      ( ~ r2_hidden('#skF_1'(A_139,k2_setfam_1(A_140,A_139)),A_140)
      | r1_tarski(A_139,k2_setfam_1(A_140,A_139)) ) ),
    inference(resolution,[status(thm)],[c_6,c_222])).

tff(c_251,plain,(
    ! [A_141] : r1_tarski(A_141,k2_setfam_1(A_141,A_141)) ),
    inference(resolution,[status(thm)],[c_6,c_235])).

tff(c_38,plain,(
    ! [A_44,B_45] :
      ( r1_setfam_1(A_44,B_45)
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_266,plain,(
    ! [A_141] : r1_setfam_1(A_141,k2_setfam_1(A_141,A_141)) ),
    inference(resolution,[status(thm)],[c_251,c_38])).

tff(c_40,plain,(
    ~ r1_setfam_1('#skF_8',k2_setfam_1('#skF_8','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:33:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.33  
% 2.41/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.33  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_tarski > k2_setfam_1 > #nlpp > k3_tarski > k1_tarski > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 2.41/1.33  
% 2.41/1.33  %Foreground sorts:
% 2.41/1.33  
% 2.41/1.33  
% 2.41/1.33  %Background operators:
% 2.41/1.33  
% 2.41/1.33  
% 2.41/1.33  %Foreground operators:
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.33  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.41/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.41/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.41/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.41/1.33  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.41/1.33  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.41/1.33  tff('#skF_8', type, '#skF_8': $i).
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.41/1.33  tff(k2_setfam_1, type, k2_setfam_1: ($i * $i) > $i).
% 2.41/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.41/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.41/1.33  
% 2.41/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.41/1.34  tff(f_36, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.41/1.34  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.41/1.34  tff(f_38, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 2.41/1.34  tff(f_50, axiom, (![A, B, C]: ((C = k2_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k2_xboole_0(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_setfam_1)).
% 2.41/1.34  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_setfam_1)).
% 2.41/1.34  tff(f_57, negated_conjecture, ~(![A]: r1_setfam_1(A, k2_setfam_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_setfam_1)).
% 2.41/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.41/1.34  tff(c_10, plain, (![A_7]: (k3_tarski(k1_tarski(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.41/1.34  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.41/1.34  tff(c_60, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.41/1.34  tff(c_69, plain, (![A_6]: (k3_tarski(k1_tarski(A_6))=k2_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_60])).
% 2.41/1.34  tff(c_72, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_69])).
% 2.41/1.34  tff(c_108, plain, (![E_65, F_66, A_67, B_68]: (r2_hidden(k2_xboole_0(E_65, F_66), k2_setfam_1(A_67, B_68)) | ~r2_hidden(F_66, B_68) | ~r2_hidden(E_65, A_67))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.34  tff(c_115, plain, (![A_69, A_70, B_71]: (r2_hidden(A_69, k2_setfam_1(A_70, B_71)) | ~r2_hidden(A_69, B_71) | ~r2_hidden(A_69, A_70))), inference(superposition, [status(thm), theory('equality')], [c_72, c_108])).
% 2.41/1.34  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.41/1.34  tff(c_222, plain, (![A_136, A_137, B_138]: (r1_tarski(A_136, k2_setfam_1(A_137, B_138)) | ~r2_hidden('#skF_1'(A_136, k2_setfam_1(A_137, B_138)), B_138) | ~r2_hidden('#skF_1'(A_136, k2_setfam_1(A_137, B_138)), A_137))), inference(resolution, [status(thm)], [c_115, c_4])).
% 2.41/1.34  tff(c_235, plain, (![A_139, A_140]: (~r2_hidden('#skF_1'(A_139, k2_setfam_1(A_140, A_139)), A_140) | r1_tarski(A_139, k2_setfam_1(A_140, A_139)))), inference(resolution, [status(thm)], [c_6, c_222])).
% 2.41/1.34  tff(c_251, plain, (![A_141]: (r1_tarski(A_141, k2_setfam_1(A_141, A_141)))), inference(resolution, [status(thm)], [c_6, c_235])).
% 2.41/1.34  tff(c_38, plain, (![A_44, B_45]: (r1_setfam_1(A_44, B_45) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.34  tff(c_266, plain, (![A_141]: (r1_setfam_1(A_141, k2_setfam_1(A_141, A_141)))), inference(resolution, [status(thm)], [c_251, c_38])).
% 2.41/1.34  tff(c_40, plain, (~r1_setfam_1('#skF_8', k2_setfam_1('#skF_8', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.41/1.34  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_266, c_40])).
% 2.41/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.34  
% 2.41/1.34  Inference rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Ref     : 0
% 2.41/1.34  #Sup     : 54
% 2.41/1.34  #Fact    : 0
% 2.41/1.34  #Define  : 0
% 2.41/1.34  #Split   : 0
% 2.41/1.34  #Chain   : 0
% 2.41/1.34  #Close   : 0
% 2.41/1.34  
% 2.41/1.34  Ordering : KBO
% 2.41/1.34  
% 2.41/1.34  Simplification rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Subsume      : 3
% 2.41/1.34  #Demod        : 2
% 2.41/1.34  #Tautology    : 11
% 2.41/1.34  #SimpNegUnit  : 0
% 2.41/1.34  #BackRed      : 1
% 2.41/1.34  
% 2.41/1.34  #Partial instantiations: 0
% 2.41/1.34  #Strategies tried      : 1
% 2.41/1.34  
% 2.41/1.34  Timing (in seconds)
% 2.41/1.34  ----------------------
% 2.41/1.34  Preprocessing        : 0.32
% 2.41/1.34  Parsing              : 0.16
% 2.41/1.34  CNF conversion       : 0.03
% 2.41/1.34  Main loop            : 0.25
% 2.41/1.34  Inferencing          : 0.11
% 2.41/1.34  Reduction            : 0.05
% 2.41/1.34  Demodulation         : 0.04
% 2.41/1.34  BG Simplification    : 0.02
% 2.41/1.34  Subsumption          : 0.05
% 2.41/1.34  Abstraction          : 0.02
% 2.41/1.34  MUC search           : 0.00
% 2.41/1.34  Cooper               : 0.00
% 2.41/1.34  Total                : 0.60
% 2.41/1.34  Index Insertion      : 0.00
% 2.41/1.34  Index Deletion       : 0.00
% 2.41/1.34  Index Matching       : 0.00
% 2.41/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
