%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:38 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k2_wellord1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7,D_9] : k3_xboole_0(k2_zfmisc_1(A_6,C_8),k2_zfmisc_1(B_7,D_9)) = k2_zfmisc_1(k3_xboole_0(A_6,B_7),k3_xboole_0(C_8,D_9)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_12,B_14] :
      ( k3_xboole_0(A_12,k2_zfmisc_1(B_14,B_14)) = k2_wellord1(A_12,B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_45,plain,(
    ! [A_25,B_26,C_27] : k3_xboole_0(k3_xboole_0(A_25,B_26),C_27) = k3_xboole_0(A_25,k3_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_93,plain,(
    ! [A_32,B_33,C_34] :
      ( k3_xboole_0(A_32,k3_xboole_0(k2_zfmisc_1(B_33,B_33),C_34)) = k3_xboole_0(k2_wellord1(A_32,B_33),C_34)
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_45])).

tff(c_369,plain,(
    ! [A_49,C_50,B_51,D_52] :
      ( k3_xboole_0(A_49,k2_zfmisc_1(k3_xboole_0(C_50,B_51),k3_xboole_0(C_50,D_52))) = k3_xboole_0(k2_wellord1(A_49,C_50),k2_zfmisc_1(B_51,D_52))
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_93])).

tff(c_496,plain,(
    ! [A_53,C_54,D_55] :
      ( k3_xboole_0(k2_wellord1(A_53,C_54),k2_zfmisc_1(D_55,D_55)) = k2_wellord1(A_53,k3_xboole_0(C_54,D_55))
      | ~ v1_relat_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_10])).

tff(c_607,plain,(
    ! [A_59,C_60,D_61] :
      ( k2_wellord1(k2_wellord1(A_59,C_60),D_61) = k2_wellord1(A_59,k3_xboole_0(C_60,D_61))
      | ~ v1_relat_1(k2_wellord1(A_59,C_60))
      | ~ v1_relat_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_10])).

tff(c_611,plain,(
    ! [A_62,B_63,D_64] :
      ( k2_wellord1(k2_wellord1(A_62,B_63),D_64) = k2_wellord1(A_62,k3_xboole_0(B_63,D_64))
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_12,c_607])).

tff(c_14,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_623,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_14])).

tff(c_637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.37  
% 2.58/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.37  %$ v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.58/1.37  
% 2.58/1.37  %Foreground sorts:
% 2.58/1.37  
% 2.58/1.37  
% 2.58/1.37  %Background operators:
% 2.58/1.37  
% 2.58/1.37  
% 2.58/1.37  %Foreground operators:
% 2.58/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.58/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.37  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.58/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.58/1.37  
% 2.58/1.38  tff(f_47, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 2.58/1.38  tff(f_42, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k2_wellord1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 2.58/1.38  tff(f_31, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 2.58/1.38  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 2.58/1.38  tff(f_27, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.58/1.38  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.58/1.38  tff(c_12, plain, (![A_15, B_16]: (v1_relat_1(k2_wellord1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.58/1.38  tff(c_6, plain, (![A_6, C_8, B_7, D_9]: (k3_xboole_0(k2_zfmisc_1(A_6, C_8), k2_zfmisc_1(B_7, D_9))=k2_zfmisc_1(k3_xboole_0(A_6, B_7), k3_xboole_0(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.38  tff(c_10, plain, (![A_12, B_14]: (k3_xboole_0(A_12, k2_zfmisc_1(B_14, B_14))=k2_wellord1(A_12, B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.38  tff(c_45, plain, (![A_25, B_26, C_27]: (k3_xboole_0(k3_xboole_0(A_25, B_26), C_27)=k3_xboole_0(A_25, k3_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.38  tff(c_93, plain, (![A_32, B_33, C_34]: (k3_xboole_0(A_32, k3_xboole_0(k2_zfmisc_1(B_33, B_33), C_34))=k3_xboole_0(k2_wellord1(A_32, B_33), C_34) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_10, c_45])).
% 2.58/1.38  tff(c_369, plain, (![A_49, C_50, B_51, D_52]: (k3_xboole_0(A_49, k2_zfmisc_1(k3_xboole_0(C_50, B_51), k3_xboole_0(C_50, D_52)))=k3_xboole_0(k2_wellord1(A_49, C_50), k2_zfmisc_1(B_51, D_52)) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_6, c_93])).
% 2.58/1.38  tff(c_496, plain, (![A_53, C_54, D_55]: (k3_xboole_0(k2_wellord1(A_53, C_54), k2_zfmisc_1(D_55, D_55))=k2_wellord1(A_53, k3_xboole_0(C_54, D_55)) | ~v1_relat_1(A_53) | ~v1_relat_1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_369, c_10])).
% 2.58/1.38  tff(c_607, plain, (![A_59, C_60, D_61]: (k2_wellord1(k2_wellord1(A_59, C_60), D_61)=k2_wellord1(A_59, k3_xboole_0(C_60, D_61)) | ~v1_relat_1(k2_wellord1(A_59, C_60)) | ~v1_relat_1(A_59) | ~v1_relat_1(A_59))), inference(superposition, [status(thm), theory('equality')], [c_496, c_10])).
% 2.58/1.38  tff(c_611, plain, (![A_62, B_63, D_64]: (k2_wellord1(k2_wellord1(A_62, B_63), D_64)=k2_wellord1(A_62, k3_xboole_0(B_63, D_64)) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_12, c_607])).
% 2.58/1.38  tff(c_14, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.58/1.38  tff(c_623, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_611, c_14])).
% 2.58/1.38  tff(c_637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_623])).
% 2.58/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.38  
% 2.58/1.38  Inference rules
% 2.58/1.38  ----------------------
% 2.58/1.38  #Ref     : 0
% 2.58/1.38  #Sup     : 166
% 2.58/1.38  #Fact    : 0
% 2.58/1.38  #Define  : 0
% 2.58/1.38  #Split   : 0
% 2.58/1.38  #Chain   : 0
% 2.58/1.38  #Close   : 0
% 2.58/1.38  
% 2.58/1.38  Ordering : KBO
% 2.58/1.38  
% 2.58/1.38  Simplification rules
% 2.58/1.38  ----------------------
% 2.58/1.38  #Subsume      : 7
% 2.58/1.38  #Demod        : 63
% 2.58/1.38  #Tautology    : 30
% 2.58/1.38  #SimpNegUnit  : 0
% 2.58/1.38  #BackRed      : 0
% 2.58/1.38  
% 2.58/1.38  #Partial instantiations: 0
% 2.58/1.38  #Strategies tried      : 1
% 2.58/1.38  
% 2.58/1.38  Timing (in seconds)
% 2.58/1.38  ----------------------
% 2.58/1.38  Preprocessing        : 0.28
% 2.58/1.38  Parsing              : 0.15
% 2.58/1.38  CNF conversion       : 0.02
% 2.58/1.38  Main loop            : 0.35
% 2.58/1.38  Inferencing          : 0.15
% 2.58/1.38  Reduction            : 0.10
% 2.58/1.38  Demodulation         : 0.08
% 2.58/1.38  BG Simplification    : 0.03
% 2.58/1.38  Subsumption          : 0.05
% 2.58/1.38  Abstraction          : 0.03
% 2.58/1.38  MUC search           : 0.00
% 2.58/1.38  Cooper               : 0.00
% 2.58/1.38  Total                : 0.65
% 2.58/1.38  Index Insertion      : 0.00
% 2.58/1.38  Index Deletion       : 0.00
% 2.58/1.38  Index Matching       : 0.00
% 2.58/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
