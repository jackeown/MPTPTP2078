%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:22 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  22 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

tff(c_12,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [B_11,A_12] :
      ( k3_xboole_0(B_11,k2_zfmisc_1(k1_relat_1(B_11),A_12)) = k8_relat_1(A_12,B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [B_11] :
      ( k8_relat_1(k1_xboole_0,B_11) = k3_xboole_0(B_11,k1_xboole_0)
      | ~ v1_relat_1(B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_55])).

tff(c_69,plain,(
    ! [B_13] :
      ( k8_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_65])).

tff(c_72,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.10  
% 1.61/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.10  %$ v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.61/1.10  
% 1.61/1.10  %Foreground sorts:
% 1.61/1.10  
% 1.61/1.10  
% 1.61/1.10  %Background operators:
% 1.61/1.10  
% 1.61/1.10  
% 1.61/1.10  %Foreground operators:
% 1.61/1.10  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.61/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.61/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.61/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.61/1.10  
% 1.61/1.11  tff(f_42, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 1.61/1.11  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.61/1.11  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.61/1.11  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 1.61/1.11  tff(c_12, plain, (k8_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.11  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.11  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.61/1.11  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.11  tff(c_55, plain, (![B_11, A_12]: (k3_xboole_0(B_11, k2_zfmisc_1(k1_relat_1(B_11), A_12))=k8_relat_1(A_12, B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.61/1.11  tff(c_65, plain, (![B_11]: (k8_relat_1(k1_xboole_0, B_11)=k3_xboole_0(B_11, k1_xboole_0) | ~v1_relat_1(B_11))), inference(superposition, [status(thm), theory('equality')], [c_6, c_55])).
% 1.61/1.11  tff(c_69, plain, (![B_13]: (k8_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_65])).
% 1.61/1.11  tff(c_72, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_69])).
% 1.61/1.11  tff(c_76, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_72])).
% 1.61/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.11  
% 1.61/1.11  Inference rules
% 1.61/1.11  ----------------------
% 1.61/1.11  #Ref     : 0
% 1.61/1.11  #Sup     : 14
% 1.61/1.11  #Fact    : 0
% 1.61/1.11  #Define  : 0
% 1.61/1.11  #Split   : 0
% 1.61/1.11  #Chain   : 0
% 1.61/1.11  #Close   : 0
% 1.61/1.11  
% 1.61/1.11  Ordering : KBO
% 1.61/1.11  
% 1.61/1.11  Simplification rules
% 1.61/1.11  ----------------------
% 1.61/1.11  #Subsume      : 0
% 1.61/1.11  #Demod        : 1
% 1.61/1.11  #Tautology    : 12
% 1.61/1.11  #SimpNegUnit  : 1
% 1.61/1.11  #BackRed      : 0
% 1.61/1.11  
% 1.61/1.11  #Partial instantiations: 0
% 1.61/1.11  #Strategies tried      : 1
% 1.61/1.11  
% 1.61/1.11  Timing (in seconds)
% 1.61/1.11  ----------------------
% 1.61/1.11  Preprocessing        : 0.26
% 1.61/1.11  Parsing              : 0.15
% 1.61/1.11  CNF conversion       : 0.01
% 1.61/1.11  Main loop            : 0.09
% 1.61/1.11  Inferencing          : 0.04
% 1.61/1.11  Reduction            : 0.02
% 1.61/1.12  Demodulation         : 0.02
% 1.61/1.12  BG Simplification    : 0.01
% 1.61/1.12  Subsumption          : 0.01
% 1.61/1.12  Abstraction          : 0.00
% 1.61/1.12  MUC search           : 0.00
% 1.61/1.12  Cooper               : 0.00
% 1.61/1.12  Total                : 0.37
% 1.61/1.12  Index Insertion      : 0.00
% 1.61/1.12  Index Deletion       : 0.00
% 1.61/1.12  Index Matching       : 0.00
% 1.61/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
