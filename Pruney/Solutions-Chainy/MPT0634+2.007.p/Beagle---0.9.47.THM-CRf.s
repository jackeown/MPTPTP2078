%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:20 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   34 (  46 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   28 (  44 expanded)
%              Number of equality atoms :   17 (  28 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k1_relat_1(k5_relat_1(k6_relat_1(A),B)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_135,plain,(
    ! [B_19,A_20] :
      ( k3_xboole_0(k1_relat_1(B_19),A_20) = k1_relat_1(k7_relat_1(B_19,A_20))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [B_13,A_14] : k1_setfam_1(k2_tarski(B_13,A_14)) = k3_xboole_0(A_14,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_4,plain,(
    ! [A_3,B_4] : k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [B_13,A_14] : k3_xboole_0(B_13,A_14) = k3_xboole_0(A_14,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_4])).

tff(c_158,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,k1_relat_1(B_22)) = k1_relat_1(k7_relat_1(B_22,A_21))
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_69])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k5_relat_1(k6_relat_1(A_7),B_8) = k7_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) != k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_129,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) != k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_132,plain,
    ( k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) != k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_129])).

tff(c_134,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) != k1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_132])).

tff(c_168,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_134])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.26  % Computer   : n012.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % DateTime   : Tue Dec  1 19:23:22 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.06  
% 1.52/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.06  %$ v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.52/1.06  
% 1.52/1.06  %Foreground sorts:
% 1.52/1.06  
% 1.52/1.06  
% 1.52/1.06  %Background operators:
% 1.52/1.06  
% 1.52/1.06  
% 1.52/1.06  %Foreground operators:
% 1.52/1.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.06  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.52/1.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.52/1.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.52/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.52/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.52/1.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.52/1.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.52/1.06  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.52/1.06  
% 1.69/1.07  tff(f_44, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k1_relat_1(k5_relat_1(k6_relat_1(A), B)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_1)).
% 1.69/1.07  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 1.69/1.07  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.69/1.07  tff(f_29, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.69/1.07  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.69/1.07  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.69/1.07  tff(c_135, plain, (![B_19, A_20]: (k3_xboole_0(k1_relat_1(B_19), A_20)=k1_relat_1(k7_relat_1(B_19, A_20)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.07  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.69/1.07  tff(c_48, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.07  tff(c_63, plain, (![B_13, A_14]: (k1_setfam_1(k2_tarski(B_13, A_14))=k3_xboole_0(A_14, B_13))), inference(superposition, [status(thm), theory('equality')], [c_2, c_48])).
% 1.69/1.07  tff(c_4, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.07  tff(c_69, plain, (![B_13, A_14]: (k3_xboole_0(B_13, A_14)=k3_xboole_0(A_14, B_13))), inference(superposition, [status(thm), theory('equality')], [c_63, c_4])).
% 1.69/1.07  tff(c_158, plain, (![A_21, B_22]: (k3_xboole_0(A_21, k1_relat_1(B_22))=k1_relat_1(k7_relat_1(B_22, A_21)) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_135, c_69])).
% 1.69/1.07  tff(c_8, plain, (![A_7, B_8]: (k5_relat_1(k6_relat_1(A_7), B_8)=k7_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.69/1.07  tff(c_10, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))!=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.69/1.07  tff(c_129, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))!=k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_10])).
% 1.69/1.07  tff(c_132, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))!=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8, c_129])).
% 1.69/1.07  tff(c_134, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))!=k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_132])).
% 1.69/1.07  tff(c_168, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_158, c_134])).
% 1.69/1.07  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_168])).
% 1.69/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.07  
% 1.69/1.07  Inference rules
% 1.69/1.07  ----------------------
% 1.69/1.07  #Ref     : 0
% 1.69/1.07  #Sup     : 44
% 1.69/1.07  #Fact    : 0
% 1.69/1.07  #Define  : 0
% 1.69/1.07  #Split   : 0
% 1.69/1.07  #Chain   : 0
% 1.69/1.07  #Close   : 0
% 1.69/1.07  
% 1.69/1.07  Ordering : KBO
% 1.69/1.07  
% 1.69/1.07  Simplification rules
% 1.69/1.07  ----------------------
% 1.69/1.07  #Subsume      : 1
% 1.69/1.07  #Demod        : 6
% 1.69/1.07  #Tautology    : 28
% 1.69/1.07  #SimpNegUnit  : 0
% 1.69/1.07  #BackRed      : 0
% 1.69/1.07  
% 1.69/1.07  #Partial instantiations: 0
% 1.69/1.07  #Strategies tried      : 1
% 1.69/1.07  
% 1.69/1.07  Timing (in seconds)
% 1.69/1.07  ----------------------
% 1.69/1.08  Preprocessing        : 0.30
% 1.69/1.08  Parsing              : 0.16
% 1.69/1.08  CNF conversion       : 0.02
% 1.69/1.08  Main loop            : 0.12
% 1.69/1.08  Inferencing          : 0.05
% 1.69/1.08  Reduction            : 0.04
% 1.69/1.08  Demodulation         : 0.03
% 1.69/1.08  BG Simplification    : 0.01
% 1.69/1.08  Subsumption          : 0.01
% 1.69/1.08  Abstraction          : 0.01
% 1.69/1.08  MUC search           : 0.00
% 1.69/1.08  Cooper               : 0.00
% 1.69/1.08  Total                : 0.44
% 1.69/1.08  Index Insertion      : 0.00
% 1.69/1.08  Index Deletion       : 0.00
% 1.69/1.08  Index Matching       : 0.00
% 1.69/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
