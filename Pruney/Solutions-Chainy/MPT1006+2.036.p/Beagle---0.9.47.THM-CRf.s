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
% DateTime   : Thu Dec  3 10:14:07 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  30 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_164,plain,(
    ! [A_41,B_42,D_43,C_44] :
      ( r1_tarski(k8_relset_1(A_41,B_42,D_43,C_44),A_41)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(D_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_168,plain,(
    ! [C_44] :
      ( r1_tarski(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_44),k1_xboole_0)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_164])).

tff(c_209,plain,(
    ! [C_49] : r1_tarski(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_49),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_168])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_213,plain,(
    ! [C_49] : k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_49) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_18,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:50:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.19  
% 1.80/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.19  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.80/1.19  
% 1.80/1.19  %Foreground sorts:
% 1.80/1.19  
% 1.80/1.19  
% 1.80/1.19  %Background operators:
% 1.80/1.19  
% 1.80/1.19  
% 1.80/1.19  %Foreground operators:
% 1.80/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.80/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.19  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.80/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.19  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 1.80/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.80/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.19  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.80/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.80/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.80/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.80/1.19  
% 1.80/1.20  tff(f_60, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.80/1.20  tff(f_51, axiom, (![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_2)).
% 1.80/1.20  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.80/1.20  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.20  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.20  tff(c_164, plain, (![A_41, B_42, D_43, C_44]: (r1_tarski(k8_relset_1(A_41, B_42, D_43, C_44), A_41) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(D_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.80/1.20  tff(c_168, plain, (![C_44]: (r1_tarski(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_44), k1_xboole_0) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_164])).
% 1.80/1.20  tff(c_209, plain, (![C_49]: (r1_tarski(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_49), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_168])).
% 1.80/1.20  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.20  tff(c_213, plain, (![C_49]: (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_209, c_2])).
% 1.80/1.20  tff(c_18, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.20  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_213, c_18])).
% 1.80/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.20  
% 1.80/1.20  Inference rules
% 1.80/1.20  ----------------------
% 1.80/1.20  #Ref     : 0
% 1.80/1.20  #Sup     : 48
% 1.80/1.20  #Fact    : 0
% 1.80/1.20  #Define  : 0
% 1.80/1.20  #Split   : 0
% 1.80/1.20  #Chain   : 0
% 1.80/1.20  #Close   : 0
% 1.80/1.20  
% 1.80/1.20  Ordering : KBO
% 1.80/1.20  
% 1.80/1.20  Simplification rules
% 1.80/1.20  ----------------------
% 1.80/1.20  #Subsume      : 0
% 1.80/1.20  #Demod        : 8
% 1.80/1.20  #Tautology    : 35
% 1.80/1.20  #SimpNegUnit  : 0
% 1.80/1.20  #BackRed      : 3
% 1.80/1.20  
% 1.80/1.20  #Partial instantiations: 0
% 1.80/1.20  #Strategies tried      : 1
% 1.80/1.20  
% 1.80/1.20  Timing (in seconds)
% 1.80/1.20  ----------------------
% 1.80/1.20  Preprocessing        : 0.25
% 1.80/1.20  Parsing              : 0.14
% 1.80/1.20  CNF conversion       : 0.02
% 1.80/1.21  Main loop            : 0.14
% 1.80/1.21  Inferencing          : 0.06
% 1.80/1.21  Reduction            : 0.04
% 1.80/1.21  Demodulation         : 0.03
% 1.80/1.21  BG Simplification    : 0.01
% 1.80/1.21  Subsumption          : 0.02
% 1.80/1.21  Abstraction          : 0.01
% 1.80/1.21  MUC search           : 0.00
% 1.80/1.21  Cooper               : 0.00
% 1.80/1.21  Total                : 0.42
% 1.80/1.21  Index Insertion      : 0.00
% 1.80/1.21  Index Deletion       : 0.00
% 1.80/1.21  Index Matching       : 0.00
% 1.80/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
