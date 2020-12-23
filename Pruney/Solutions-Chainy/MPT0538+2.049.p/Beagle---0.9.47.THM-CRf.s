%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:29 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_21,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_25,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_10])).

tff(c_130,plain,(
    ! [B_24,A_25] :
      ( k5_relat_1(B_24,k6_relat_1(A_25)) = k8_relat_1(A_25,B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    ! [A_16] :
      ( k5_relat_1(k1_xboole_0,A_16) = k1_xboole_0
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [A_3] : k5_relat_1(k1_xboole_0,k6_relat_1(A_3)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_137,plain,(
    ! [A_25] :
      ( k8_relat_1(A_25,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_85])).

tff(c_146,plain,(
    ! [A_25] : k8_relat_1(A_25,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_137])).

tff(c_18,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.11  
% 1.63/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.12  %$ v1_relat_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1
% 1.63/1.12  
% 1.63/1.12  %Foreground sorts:
% 1.63/1.12  
% 1.63/1.12  
% 1.63/1.12  %Background operators:
% 1.63/1.12  
% 1.63/1.12  
% 1.63/1.12  %Foreground operators:
% 1.63/1.12  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.12  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.63/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.63/1.12  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.12  
% 1.73/1.12  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.73/1.12  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.73/1.12  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.73/1.12  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.73/1.12  tff(f_45, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 1.73/1.12  tff(f_48, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 1.73/1.12  tff(c_21, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.12  tff(c_10, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.73/1.12  tff(c_25, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_21, c_10])).
% 1.73/1.12  tff(c_130, plain, (![B_24, A_25]: (k5_relat_1(B_24, k6_relat_1(A_25))=k8_relat_1(A_25, B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.73/1.12  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.73/1.12  tff(c_72, plain, (![A_16]: (k5_relat_1(k1_xboole_0, A_16)=k1_xboole_0 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.73/1.12  tff(c_85, plain, (![A_3]: (k5_relat_1(k1_xboole_0, k6_relat_1(A_3))=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_72])).
% 1.73/1.12  tff(c_137, plain, (![A_25]: (k8_relat_1(A_25, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_130, c_85])).
% 1.73/1.12  tff(c_146, plain, (![A_25]: (k8_relat_1(A_25, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_25, c_137])).
% 1.73/1.12  tff(c_18, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.73/1.12  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_18])).
% 1.73/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.12  
% 1.73/1.12  Inference rules
% 1.73/1.12  ----------------------
% 1.73/1.12  #Ref     : 0
% 1.73/1.12  #Sup     : 34
% 1.73/1.12  #Fact    : 0
% 1.73/1.12  #Define  : 0
% 1.73/1.12  #Split   : 0
% 1.73/1.12  #Chain   : 0
% 1.73/1.12  #Close   : 0
% 1.73/1.12  
% 1.73/1.12  Ordering : KBO
% 1.73/1.12  
% 1.73/1.12  Simplification rules
% 1.73/1.12  ----------------------
% 1.73/1.12  #Subsume      : 0
% 1.73/1.12  #Demod        : 9
% 1.73/1.12  #Tautology    : 26
% 1.73/1.12  #SimpNegUnit  : 0
% 1.73/1.12  #BackRed      : 1
% 1.73/1.12  
% 1.73/1.12  #Partial instantiations: 0
% 1.73/1.12  #Strategies tried      : 1
% 1.73/1.12  
% 1.73/1.12  Timing (in seconds)
% 1.73/1.12  ----------------------
% 1.73/1.13  Preprocessing        : 0.25
% 1.73/1.13  Parsing              : 0.14
% 1.73/1.13  CNF conversion       : 0.02
% 1.73/1.13  Main loop            : 0.11
% 1.73/1.13  Inferencing          : 0.05
% 1.73/1.13  Reduction            : 0.03
% 1.73/1.13  Demodulation         : 0.03
% 1.73/1.13  BG Simplification    : 0.01
% 1.73/1.13  Subsumption          : 0.02
% 1.73/1.13  Abstraction          : 0.01
% 1.73/1.13  MUC search           : 0.00
% 1.73/1.13  Cooper               : 0.00
% 1.73/1.13  Total                : 0.39
% 1.73/1.13  Index Insertion      : 0.00
% 1.73/1.13  Index Deletion       : 0.00
% 1.73/1.13  Index Matching       : 0.00
% 1.73/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
