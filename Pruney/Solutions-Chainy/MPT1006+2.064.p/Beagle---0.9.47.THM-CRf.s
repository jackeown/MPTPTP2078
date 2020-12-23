%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:11 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  36 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    ! [A_16,B_17,D_18,C_19] :
      ( r1_tarski(k8_relset_1(A_16,B_17,D_18,C_19),A_16)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_funct_1(D_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [C_19] :
      ( r1_tarski(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_19),k1_xboole_0)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_46])).

tff(c_52,plain,(
    ! [C_20] : r1_tarski(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_20),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_48])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    ! [C_21] : k2_xboole_0(k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_21),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_24])).

tff(c_62,plain,(
    ! [C_21] : k8_relset_1(k1_xboole_0,'#skF_1','#skF_3',C_21) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_33])).

tff(c_10,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:18:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.70/1.16  
% 1.70/1.16  %Foreground sorts:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Background operators:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Foreground operators:
% 1.70/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.16  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.70/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.70/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.70/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.70/1.16  
% 1.70/1.17  tff(f_48, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.70/1.17  tff(f_39, axiom, (![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_2)).
% 1.70/1.17  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.70/1.17  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.70/1.17  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.70/1.17  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.70/1.17  tff(c_12, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.70/1.17  tff(c_46, plain, (![A_16, B_17, D_18, C_19]: (r1_tarski(k8_relset_1(A_16, B_17, D_18, C_19), A_16) | ~m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~v1_funct_1(D_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.70/1.17  tff(c_48, plain, (![C_19]: (r1_tarski(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_19), k1_xboole_0) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_46])).
% 1.70/1.17  tff(c_52, plain, (![C_20]: (r1_tarski(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_20), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_48])).
% 1.70/1.17  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.17  tff(c_57, plain, (![C_21]: (k2_xboole_0(k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_21), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_2])).
% 1.70/1.17  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.17  tff(c_24, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k3_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.17  tff(c_33, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(superposition, [status(thm), theory('equality')], [c_6, c_24])).
% 1.70/1.17  tff(c_62, plain, (![C_21]: (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', C_21)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_57, c_33])).
% 1.70/1.17  tff(c_10, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.70/1.17  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_10])).
% 1.70/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  Inference rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Ref     : 0
% 1.70/1.17  #Sup     : 13
% 1.70/1.17  #Fact    : 0
% 1.70/1.17  #Define  : 0
% 1.70/1.17  #Split   : 0
% 1.70/1.17  #Chain   : 0
% 1.70/1.17  #Close   : 0
% 1.70/1.17  
% 1.70/1.17  Ordering : KBO
% 1.70/1.17  
% 1.70/1.17  Simplification rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Subsume      : 0
% 1.70/1.17  #Demod        : 5
% 1.70/1.17  #Tautology    : 9
% 1.70/1.17  #SimpNegUnit  : 0
% 1.70/1.17  #BackRed      : 3
% 1.70/1.17  
% 1.70/1.17  #Partial instantiations: 0
% 1.70/1.17  #Strategies tried      : 1
% 1.70/1.17  
% 1.70/1.17  Timing (in seconds)
% 1.70/1.17  ----------------------
% 1.70/1.17  Preprocessing        : 0.25
% 1.70/1.17  Parsing              : 0.14
% 1.70/1.17  CNF conversion       : 0.02
% 1.70/1.17  Main loop            : 0.10
% 1.70/1.17  Inferencing          : 0.05
% 1.70/1.17  Reduction            : 0.03
% 1.70/1.17  Demodulation         : 0.02
% 1.70/1.17  BG Simplification    : 0.01
% 1.70/1.17  Subsumption          : 0.01
% 1.70/1.17  Abstraction          : 0.00
% 1.70/1.17  MUC search           : 0.00
% 1.70/1.17  Cooper               : 0.00
% 1.70/1.17  Total                : 0.37
% 1.70/1.17  Index Insertion      : 0.00
% 1.70/1.17  Index Deletion       : 0.00
% 1.70/1.17  Index Matching       : 0.00
% 1.70/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
