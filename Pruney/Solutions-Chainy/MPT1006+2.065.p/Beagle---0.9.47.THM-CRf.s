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
% DateTime   : Thu Dec  3 10:14:11 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  39 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_tarski(A,k3_zfmisc_1(A,B,C))
          & ~ r1_tarski(A,k3_zfmisc_1(B,C,A))
          & ~ r1_tarski(A,k3_zfmisc_1(C,A,B)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_118,plain,(
    ! [A_30,B_31,D_32,C_33] :
      ( r1_tarski(k8_relset_1(A_30,B_31,D_32,C_33),A_30)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_1(D_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_120,plain,(
    ! [C_33] :
      ( r1_tarski(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_33),k1_xboole_0)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_118])).

tff(c_124,plain,(
    ! [C_34] : r1_tarski(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_34),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_120])).

tff(c_8,plain,(
    ! [B_2,C_3] : k3_zfmisc_1(k1_xboole_0,B_2,C_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    ! [A_17,C_18,B_19] :
      ( ~ r1_tarski(A_17,k3_zfmisc_1(C_18,A_17,B_19))
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    ! [B_2] :
      ( ~ r1_tarski(B_2,k1_xboole_0)
      | k1_xboole_0 = B_2 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_70])).

tff(c_128,plain,(
    ! [C_34] : k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_34) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_76])).

tff(c_18,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:11:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.17  
% 1.76/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.18  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.76/1.18  
% 1.76/1.18  %Foreground sorts:
% 1.76/1.18  
% 1.76/1.18  
% 1.76/1.18  %Background operators:
% 1.76/1.18  
% 1.76/1.18  
% 1.76/1.18  %Foreground operators:
% 1.76/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.18  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.76/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.76/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.18  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.76/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.76/1.18  
% 1.76/1.19  tff(f_64, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.76/1.19  tff(f_55, axiom, (![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_2)).
% 1.76/1.19  tff(f_37, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 1.76/1.19  tff(f_49, axiom, (![A, B, C]: (~((~r1_tarski(A, k3_zfmisc_1(A, B, C)) & ~r1_tarski(A, k3_zfmisc_1(B, C, A))) & ~r1_tarski(A, k3_zfmisc_1(C, A, B))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_mcart_1)).
% 1.76/1.19  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.76/1.19  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.76/1.19  tff(c_118, plain, (![A_30, B_31, D_32, C_33]: (r1_tarski(k8_relset_1(A_30, B_31, D_32, C_33), A_30) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_1(D_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.76/1.19  tff(c_120, plain, (![C_33]: (r1_tarski(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_33), k1_xboole_0) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_118])).
% 1.76/1.19  tff(c_124, plain, (![C_34]: (r1_tarski(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_34), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_120])).
% 1.76/1.19  tff(c_8, plain, (![B_2, C_3]: (k3_zfmisc_1(k1_xboole_0, B_2, C_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.76/1.19  tff(c_70, plain, (![A_17, C_18, B_19]: (~r1_tarski(A_17, k3_zfmisc_1(C_18, A_17, B_19)) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.76/1.19  tff(c_76, plain, (![B_2]: (~r1_tarski(B_2, k1_xboole_0) | k1_xboole_0=B_2)), inference(superposition, [status(thm), theory('equality')], [c_8, c_70])).
% 1.76/1.19  tff(c_128, plain, (![C_34]: (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_124, c_76])).
% 1.76/1.19  tff(c_18, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.76/1.19  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_18])).
% 1.76/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.19  
% 1.76/1.19  Inference rules
% 1.76/1.19  ----------------------
% 1.76/1.19  #Ref     : 0
% 1.76/1.19  #Sup     : 26
% 1.76/1.19  #Fact    : 0
% 1.76/1.19  #Define  : 0
% 1.76/1.19  #Split   : 0
% 1.76/1.19  #Chain   : 0
% 1.76/1.19  #Close   : 0
% 1.76/1.19  
% 1.76/1.19  Ordering : KBO
% 1.76/1.19  
% 1.76/1.19  Simplification rules
% 1.76/1.19  ----------------------
% 1.76/1.19  #Subsume      : 7
% 1.76/1.19  #Demod        : 3
% 1.76/1.19  #Tautology    : 16
% 1.76/1.19  #SimpNegUnit  : 0
% 1.76/1.19  #BackRed      : 2
% 1.76/1.19  
% 1.76/1.19  #Partial instantiations: 0
% 1.76/1.19  #Strategies tried      : 1
% 1.76/1.19  
% 1.76/1.19  Timing (in seconds)
% 1.76/1.19  ----------------------
% 1.76/1.19  Preprocessing        : 0.28
% 1.76/1.19  Parsing              : 0.15
% 1.76/1.19  CNF conversion       : 0.02
% 1.76/1.19  Main loop            : 0.11
% 1.76/1.19  Inferencing          : 0.04
% 1.76/1.19  Reduction            : 0.03
% 1.76/1.19  Demodulation         : 0.02
% 1.76/1.19  BG Simplification    : 0.01
% 1.76/1.19  Subsumption          : 0.02
% 1.76/1.19  Abstraction          : 0.00
% 1.76/1.19  MUC search           : 0.00
% 1.76/1.19  Cooper               : 0.00
% 1.76/1.19  Total                : 0.42
% 1.76/1.19  Index Insertion      : 0.00
% 1.76/1.19  Index Deletion       : 0.00
% 1.76/1.19  Index Matching       : 0.00
% 1.76/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
