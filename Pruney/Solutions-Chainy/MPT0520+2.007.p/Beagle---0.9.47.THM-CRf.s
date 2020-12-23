%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:08 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  35 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k2_relat_1(B))
         => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_10,plain,(
    k2_relat_1(k8_relat_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    ! [A_15,B_16] : k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(B_16,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [B_16,A_15] : k3_xboole_0(B_16,A_15) = k3_xboole_0(A_15,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_6])).

tff(c_128,plain,(
    ! [B_19,A_20] :
      ( k3_xboole_0(k2_relat_1(B_19),A_20) = k2_relat_1(k8_relat_1(A_20,B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    ! [B_21,B_22] :
      ( k3_xboole_0(B_21,k2_relat_1(B_22)) = k2_relat_1(k8_relat_1(B_21,B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_128])).

tff(c_12,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_48,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_48])).

tff(c_168,plain,
    ( k2_relat_1(k8_relat_1('#skF_1','#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_52])).

tff(c_189,plain,(
    k2_relat_1(k8_relat_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_168])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.17  
% 1.67/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.17  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_1
% 1.67/1.17  
% 1.67/1.17  %Foreground sorts:
% 1.67/1.17  
% 1.67/1.17  
% 1.67/1.17  %Background operators:
% 1.67/1.17  
% 1.67/1.17  
% 1.67/1.17  %Foreground operators:
% 1.67/1.17  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.67/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.67/1.17  
% 1.67/1.18  tff(f_44, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 1.67/1.18  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.67/1.18  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.67/1.18  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 1.67/1.18  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.67/1.18  tff(c_10, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.18  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.18  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.18  tff(c_53, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.18  tff(c_72, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(B_16, A_15))), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 1.67/1.18  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.18  tff(c_78, plain, (![B_16, A_15]: (k3_xboole_0(B_16, A_15)=k3_xboole_0(A_15, B_16))), inference(superposition, [status(thm), theory('equality')], [c_72, c_6])).
% 1.67/1.18  tff(c_128, plain, (![B_19, A_20]: (k3_xboole_0(k2_relat_1(B_19), A_20)=k2_relat_1(k8_relat_1(A_20, B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.18  tff(c_152, plain, (![B_21, B_22]: (k3_xboole_0(B_21, k2_relat_1(B_22))=k2_relat_1(k8_relat_1(B_21, B_22)) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_78, c_128])).
% 1.67/1.18  tff(c_12, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.18  tff(c_48, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.18  tff(c_52, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_12, c_48])).
% 1.67/1.18  tff(c_168, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_152, c_52])).
% 1.67/1.18  tff(c_189, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_168])).
% 1.67/1.18  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_189])).
% 1.67/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.18  
% 1.67/1.18  Inference rules
% 1.67/1.18  ----------------------
% 1.67/1.18  #Ref     : 0
% 1.67/1.18  #Sup     : 45
% 1.67/1.18  #Fact    : 0
% 1.67/1.18  #Define  : 0
% 1.67/1.18  #Split   : 0
% 1.67/1.18  #Chain   : 0
% 1.67/1.18  #Close   : 0
% 1.67/1.18  
% 1.67/1.18  Ordering : KBO
% 1.67/1.18  
% 1.67/1.18  Simplification rules
% 1.67/1.18  ----------------------
% 1.67/1.18  #Subsume      : 3
% 1.67/1.18  #Demod        : 4
% 1.67/1.18  #Tautology    : 28
% 1.67/1.18  #SimpNegUnit  : 1
% 1.67/1.18  #BackRed      : 0
% 1.67/1.18  
% 1.67/1.18  #Partial instantiations: 0
% 1.67/1.18  #Strategies tried      : 1
% 1.67/1.18  
% 1.67/1.18  Timing (in seconds)
% 1.67/1.18  ----------------------
% 1.90/1.18  Preprocessing        : 0.28
% 1.90/1.18  Parsing              : 0.15
% 1.90/1.18  CNF conversion       : 0.02
% 1.90/1.18  Main loop            : 0.14
% 1.90/1.18  Inferencing          : 0.06
% 1.90/1.18  Reduction            : 0.04
% 1.90/1.18  Demodulation         : 0.04
% 1.90/1.18  BG Simplification    : 0.01
% 1.90/1.18  Subsumption          : 0.02
% 1.90/1.18  Abstraction          : 0.01
% 1.90/1.18  MUC search           : 0.00
% 1.90/1.18  Cooper               : 0.00
% 1.90/1.18  Total                : 0.45
% 1.90/1.18  Index Insertion      : 0.00
% 1.90/1.18  Index Deletion       : 0.00
% 1.90/1.18  Index Matching       : 0.00
% 1.90/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
