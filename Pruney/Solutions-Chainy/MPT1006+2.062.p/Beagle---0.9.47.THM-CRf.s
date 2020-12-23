%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:10 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  49 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_21,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_17,B_18,D_19,C_20] :
      ( r1_tarski(k8_relset_1(A_17,B_18,D_19,C_20),A_17)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_1(D_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_73,plain,(
    ! [B_24,D_25,C_26] :
      ( r1_tarski(k8_relset_1(k1_xboole_0,B_24,D_25,C_26),k1_xboole_0)
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(D_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_63])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [B_24,D_25,C_26] :
      ( k3_xboole_0(k8_relset_1(k1_xboole_0,B_24,D_25,C_26),k1_xboole_0) = k8_relset_1(k1_xboole_0,B_24,D_25,C_26)
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(D_25) ) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_79,plain,(
    ! [B_27,D_28,C_29] :
      ( k8_relset_1(k1_xboole_0,B_27,D_28,C_29) = k1_xboole_0
      | ~ m1_subset_1(D_28,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(D_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_76])).

tff(c_81,plain,(
    ! [B_27,C_29] :
      ( k8_relset_1(k1_xboole_0,B_27,'#skF_3',C_29) = k1_xboole_0
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_21,c_79])).

tff(c_84,plain,(
    ! [B_27,C_29] : k8_relset_1(k1_xboole_0,B_27,'#skF_3',C_29) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_81])).

tff(c_14,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.10  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.62/1.10  
% 1.62/1.10  %Foreground sorts:
% 1.62/1.10  
% 1.62/1.10  
% 1.62/1.10  %Background operators:
% 1.62/1.10  
% 1.62/1.10  
% 1.62/1.10  %Foreground operators:
% 1.62/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.10  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.62/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.62/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.62/1.10  
% 1.62/1.11  tff(f_52, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 1.62/1.11  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.62/1.11  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.62/1.11  tff(f_43, axiom, (![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_2)).
% 1.62/1.11  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.62/1.11  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.62/1.11  tff(c_10, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.11  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.62/1.11  tff(c_21, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 1.62/1.11  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.11  tff(c_63, plain, (![A_17, B_18, D_19, C_20]: (r1_tarski(k8_relset_1(A_17, B_18, D_19, C_20), A_17) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_1(D_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.62/1.11  tff(c_73, plain, (![B_24, D_25, C_26]: (r1_tarski(k8_relset_1(k1_xboole_0, B_24, D_25, C_26), k1_xboole_0) | ~m1_subset_1(D_25, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(D_25))), inference(superposition, [status(thm), theory('equality')], [c_10, c_63])).
% 1.62/1.11  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.11  tff(c_76, plain, (![B_24, D_25, C_26]: (k3_xboole_0(k8_relset_1(k1_xboole_0, B_24, D_25, C_26), k1_xboole_0)=k8_relset_1(k1_xboole_0, B_24, D_25, C_26) | ~m1_subset_1(D_25, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(D_25))), inference(resolution, [status(thm)], [c_73, c_2])).
% 1.62/1.11  tff(c_79, plain, (![B_27, D_28, C_29]: (k8_relset_1(k1_xboole_0, B_27, D_28, C_29)=k1_xboole_0 | ~m1_subset_1(D_28, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(D_28))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_76])).
% 1.62/1.11  tff(c_81, plain, (![B_27, C_29]: (k8_relset_1(k1_xboole_0, B_27, '#skF_3', C_29)=k1_xboole_0 | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_21, c_79])).
% 1.62/1.11  tff(c_84, plain, (![B_27, C_29]: (k8_relset_1(k1_xboole_0, B_27, '#skF_3', C_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_81])).
% 1.62/1.11  tff(c_14, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.62/1.11  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_14])).
% 1.62/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.11  
% 1.62/1.11  Inference rules
% 1.62/1.11  ----------------------
% 1.62/1.11  #Ref     : 0
% 1.62/1.11  #Sup     : 15
% 1.62/1.11  #Fact    : 0
% 1.62/1.11  #Define  : 0
% 1.62/1.11  #Split   : 0
% 1.62/1.11  #Chain   : 0
% 1.62/1.11  #Close   : 0
% 1.62/1.11  
% 1.62/1.11  Ordering : KBO
% 1.62/1.11  
% 1.62/1.11  Simplification rules
% 1.62/1.11  ----------------------
% 1.62/1.11  #Subsume      : 0
% 1.62/1.11  #Demod        : 4
% 1.62/1.11  #Tautology    : 10
% 1.62/1.11  #SimpNegUnit  : 0
% 1.62/1.11  #BackRed      : 1
% 1.62/1.11  
% 1.62/1.11  #Partial instantiations: 0
% 1.62/1.11  #Strategies tried      : 1
% 1.62/1.11  
% 1.62/1.11  Timing (in seconds)
% 1.62/1.11  ----------------------
% 1.62/1.12  Preprocessing        : 0.26
% 1.62/1.12  Parsing              : 0.15
% 1.62/1.12  CNF conversion       : 0.02
% 1.62/1.12  Main loop            : 0.10
% 1.62/1.12  Inferencing          : 0.04
% 1.62/1.12  Reduction            : 0.03
% 1.62/1.12  Demodulation         : 0.02
% 1.62/1.12  BG Simplification    : 0.01
% 1.62/1.12  Subsumption          : 0.01
% 1.62/1.12  Abstraction          : 0.00
% 1.62/1.12  MUC search           : 0.00
% 1.62/1.12  Cooper               : 0.00
% 1.62/1.12  Total                : 0.38
% 1.62/1.12  Index Insertion      : 0.00
% 1.62/1.12  Index Deletion       : 0.00
% 1.62/1.12  Index Matching       : 0.00
% 1.62/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
