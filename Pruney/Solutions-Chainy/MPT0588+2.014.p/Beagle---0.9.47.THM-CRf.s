%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:05 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   30 (  40 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  39 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(B_15,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_4,plain,(
    ! [A_3,B_4] : k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [B_15,A_14] : k3_xboole_0(B_15,A_14) = k3_xboole_0(A_14,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_4])).

tff(c_8,plain,(
    ! [A_8] :
      ( k7_relat_1(A_8,k1_relat_1(A_8)) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_128,plain,(
    ! [C_18,A_19,B_20] :
      ( k7_relat_1(k7_relat_1(C_18,A_19),B_20) = k7_relat_1(C_18,k3_xboole_0(A_19,B_20))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_154,plain,(
    ! [A_21,B_22] :
      ( k7_relat_1(A_21,k3_xboole_0(k1_relat_1(A_21),B_22)) = k7_relat_1(A_21,B_22)
      | ~ v1_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_128])).

tff(c_182,plain,(
    ! [A_23,B_24] :
      ( k7_relat_1(A_23,k3_xboole_0(B_24,k1_relat_1(A_23))) = k7_relat_1(A_23,B_24)
      | ~ v1_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_154])).

tff(c_10,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_93,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10])).

tff(c_199,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_93])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:46:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.17  
% 1.62/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.18  %$ v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.62/1.18  
% 1.62/1.18  %Foreground sorts:
% 1.62/1.18  
% 1.62/1.18  
% 1.62/1.18  %Background operators:
% 1.62/1.18  
% 1.62/1.18  
% 1.62/1.18  %Foreground operators:
% 1.62/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.62/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.62/1.18  
% 1.88/1.19  tff(f_42, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 1.88/1.19  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.88/1.19  tff(f_29, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.88/1.19  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.88/1.19  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.88/1.19  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.19  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.19  tff(c_46, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.19  tff(c_70, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(B_15, A_14))), inference(superposition, [status(thm), theory('equality')], [c_2, c_46])).
% 1.88/1.19  tff(c_4, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.19  tff(c_76, plain, (![B_15, A_14]: (k3_xboole_0(B_15, A_14)=k3_xboole_0(A_14, B_15))), inference(superposition, [status(thm), theory('equality')], [c_70, c_4])).
% 1.88/1.19  tff(c_8, plain, (![A_8]: (k7_relat_1(A_8, k1_relat_1(A_8))=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.19  tff(c_128, plain, (![C_18, A_19, B_20]: (k7_relat_1(k7_relat_1(C_18, A_19), B_20)=k7_relat_1(C_18, k3_xboole_0(A_19, B_20)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.19  tff(c_154, plain, (![A_21, B_22]: (k7_relat_1(A_21, k3_xboole_0(k1_relat_1(A_21), B_22))=k7_relat_1(A_21, B_22) | ~v1_relat_1(A_21) | ~v1_relat_1(A_21))), inference(superposition, [status(thm), theory('equality')], [c_8, c_128])).
% 1.88/1.19  tff(c_182, plain, (![A_23, B_24]: (k7_relat_1(A_23, k3_xboole_0(B_24, k1_relat_1(A_23)))=k7_relat_1(A_23, B_24) | ~v1_relat_1(A_23) | ~v1_relat_1(A_23))), inference(superposition, [status(thm), theory('equality')], [c_76, c_154])).
% 1.88/1.19  tff(c_10, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.19  tff(c_93, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_10])).
% 1.88/1.19  tff(c_199, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_182, c_93])).
% 1.88/1.19  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_199])).
% 1.88/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  Inference rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Ref     : 0
% 1.88/1.19  #Sup     : 52
% 1.88/1.19  #Fact    : 0
% 1.88/1.19  #Define  : 0
% 1.88/1.19  #Split   : 0
% 1.88/1.19  #Chain   : 0
% 1.88/1.19  #Close   : 0
% 1.88/1.19  
% 1.88/1.19  Ordering : KBO
% 1.88/1.19  
% 1.88/1.19  Simplification rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Subsume      : 1
% 1.88/1.19  #Demod        : 5
% 1.88/1.19  #Tautology    : 31
% 1.88/1.19  #SimpNegUnit  : 0
% 1.88/1.19  #BackRed      : 1
% 1.88/1.19  
% 1.88/1.19  #Partial instantiations: 0
% 1.88/1.19  #Strategies tried      : 1
% 1.88/1.19  
% 1.88/1.19  Timing (in seconds)
% 1.88/1.19  ----------------------
% 1.88/1.19  Preprocessing        : 0.25
% 1.88/1.19  Parsing              : 0.14
% 1.88/1.19  CNF conversion       : 0.01
% 1.88/1.19  Main loop            : 0.16
% 1.88/1.19  Inferencing          : 0.07
% 1.88/1.19  Reduction            : 0.05
% 1.88/1.19  Demodulation         : 0.04
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.02
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.44
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
