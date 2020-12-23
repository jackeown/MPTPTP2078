%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:11 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  44 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
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

tff(c_18,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_54,plain,(
    ! [A_13,B_14,D_15,C_16] :
      ( r1_tarski(k8_relset_1(A_13,B_14,D_15,C_16),A_13)
      | ~ m1_subset_1(D_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(D_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [B_23,D_24,C_25] :
      ( r1_tarski(k8_relset_1(k1_xboole_0,B_23,D_24,C_25),k1_xboole_0)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(D_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_54])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [B_26,D_27,C_28] :
      ( k8_relset_1(k1_xboole_0,B_26,D_27,C_28) = k1_xboole_0
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(D_27) ) ),
    inference(resolution,[status(thm)],[c_88,c_2])).

tff(c_100,plain,(
    ! [B_26,C_28] :
      ( k8_relset_1(k1_xboole_0,B_26,'#skF_3',C_28) = k1_xboole_0
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_19,c_98])).

tff(c_103,plain,(
    ! [B_26,C_28] : k8_relset_1(k1_xboole_0,B_26,'#skF_3',C_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_100])).

tff(c_12,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.13  
% 1.75/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.14  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.75/1.14  
% 1.75/1.14  %Foreground sorts:
% 1.75/1.14  
% 1.75/1.14  
% 1.75/1.14  %Background operators:
% 1.75/1.14  
% 1.75/1.14  
% 1.75/1.14  %Foreground operators:
% 1.75/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.14  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.75/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.75/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.75/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.75/1.14  
% 1.75/1.15  tff(f_50, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.75/1.15  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.75/1.15  tff(f_41, axiom, (![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_2)).
% 1.75/1.15  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.75/1.15  tff(c_18, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.15  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.75/1.15  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.15  tff(c_19, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 1.75/1.15  tff(c_54, plain, (![A_13, B_14, D_15, C_16]: (r1_tarski(k8_relset_1(A_13, B_14, D_15, C_16), A_13) | ~m1_subset_1(D_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(D_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.75/1.15  tff(c_88, plain, (![B_23, D_24, C_25]: (r1_tarski(k8_relset_1(k1_xboole_0, B_23, D_24, C_25), k1_xboole_0) | ~m1_subset_1(D_24, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(D_24))), inference(superposition, [status(thm), theory('equality')], [c_8, c_54])).
% 1.75/1.15  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.15  tff(c_98, plain, (![B_26, D_27, C_28]: (k8_relset_1(k1_xboole_0, B_26, D_27, C_28)=k1_xboole_0 | ~m1_subset_1(D_27, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(D_27))), inference(resolution, [status(thm)], [c_88, c_2])).
% 1.75/1.15  tff(c_100, plain, (![B_26, C_28]: (k8_relset_1(k1_xboole_0, B_26, '#skF_3', C_28)=k1_xboole_0 | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_19, c_98])).
% 1.75/1.15  tff(c_103, plain, (![B_26, C_28]: (k8_relset_1(k1_xboole_0, B_26, '#skF_3', C_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_100])).
% 1.75/1.15  tff(c_12, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.15  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_12])).
% 1.75/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.15  
% 1.75/1.15  Inference rules
% 1.75/1.15  ----------------------
% 1.75/1.15  #Ref     : 0
% 1.75/1.15  #Sup     : 19
% 1.75/1.15  #Fact    : 0
% 1.75/1.15  #Define  : 0
% 1.75/1.15  #Split   : 0
% 1.75/1.15  #Chain   : 0
% 1.75/1.15  #Close   : 0
% 1.75/1.15  
% 1.75/1.15  Ordering : KBO
% 1.75/1.15  
% 1.75/1.15  Simplification rules
% 1.75/1.15  ----------------------
% 1.75/1.15  #Subsume      : 1
% 1.75/1.15  #Demod        : 10
% 1.75/1.15  #Tautology    : 13
% 1.75/1.15  #SimpNegUnit  : 0
% 1.75/1.15  #BackRed      : 1
% 1.75/1.15  
% 1.75/1.15  #Partial instantiations: 0
% 1.75/1.15  #Strategies tried      : 1
% 1.75/1.15  
% 1.75/1.15  Timing (in seconds)
% 1.75/1.15  ----------------------
% 1.75/1.15  Preprocessing        : 0.27
% 1.75/1.15  Parsing              : 0.15
% 1.75/1.15  CNF conversion       : 0.02
% 1.75/1.15  Main loop            : 0.12
% 1.75/1.15  Inferencing          : 0.05
% 1.75/1.15  Reduction            : 0.04
% 1.75/1.15  Demodulation         : 0.03
% 1.75/1.15  BG Simplification    : 0.01
% 1.75/1.15  Subsumption          : 0.02
% 1.75/1.15  Abstraction          : 0.00
% 1.75/1.15  MUC search           : 0.00
% 1.75/1.15  Cooper               : 0.00
% 1.75/1.15  Total                : 0.41
% 1.75/1.15  Index Insertion      : 0.00
% 1.75/1.15  Index Deletion       : 0.00
% 1.75/1.15  Index Matching       : 0.00
% 1.75/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
