%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:33 EST 2020

% Result     : Theorem 14.89s
% Output     : CNFRefutation 14.98s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 175 expanded)
%              Number of leaves         :   33 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 200 expanded)
%              Number of equality atoms :   27 ( 121 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(k4_xboole_0(A_9,C_11),B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_469,plain,(
    ! [A_74,B_75] : k5_xboole_0(k5_xboole_0(A_74,B_75),k2_xboole_0(A_74,B_75)) = k3_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_518,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,A_18)) = k3_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_469])).

tff(c_524,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,A_18) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_518])).

tff(c_194,plain,(
    ! [A_65,B_66,C_67] : k5_xboole_0(k5_xboole_0(A_65,B_66),C_67) = k5_xboole_0(A_65,k5_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_224,plain,(
    ! [A_18,C_67] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_67)) = k5_xboole_0(k1_xboole_0,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_194])).

tff(c_624,plain,(
    ! [A_81,C_82] : k5_xboole_0(A_81,k5_xboole_0(A_81,C_82)) = C_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_224])).

tff(c_691,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_624])).

tff(c_208,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k5_xboole_0(B_66,k5_xboole_0(A_65,B_66))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_20])).

tff(c_674,plain,(
    ! [B_66,A_65] : k5_xboole_0(B_66,k5_xboole_0(A_65,B_66)) = k5_xboole_0(A_65,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_624])).

tff(c_860,plain,(
    ! [B_89,A_90] : k5_xboole_0(B_89,k5_xboole_0(A_90,B_89)) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_674])).

tff(c_929,plain,(
    ! [A_7,B_8] : k5_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_860])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] : k5_xboole_0(k5_xboole_0(A_15,B_16),C_17) = k5_xboole_0(A_15,k5_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_762,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_tarski(k5_xboole_0(A_84,C_85),B_86)
      | ~ r1_tarski(C_85,B_86)
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5810,plain,(
    ! [A_219,B_220,C_221,B_222] :
      ( r1_tarski(k5_xboole_0(A_219,k5_xboole_0(B_220,C_221)),B_222)
      | ~ r1_tarski(C_221,B_222)
      | ~ r1_tarski(k5_xboole_0(A_219,B_220),B_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_762])).

tff(c_6020,plain,(
    ! [A_219,B_222,A_18] :
      ( r1_tarski(k5_xboole_0(A_219,k1_xboole_0),B_222)
      | ~ r1_tarski(A_18,B_222)
      | ~ r1_tarski(k5_xboole_0(A_219,A_18),B_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5810])).

tff(c_17129,plain,(
    ! [A_320,B_321,A_322] :
      ( r1_tarski(A_320,B_321)
      | ~ r1_tarski(A_322,B_321)
      | ~ r1_tarski(k5_xboole_0(A_320,A_322),B_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_6020])).

tff(c_17337,plain,(
    ! [A_323,A_324] :
      ( r1_tarski(A_323,k5_xboole_0(A_323,A_324))
      | ~ r1_tarski(A_324,k5_xboole_0(A_323,A_324)) ) ),
    inference(resolution,[status(thm)],[c_10,c_17129])).

tff(c_17425,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k3_xboole_0(A_7,B_8),k5_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)))
      | ~ r1_tarski(k4_xboole_0(A_7,B_8),A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_929,c_17337])).

tff(c_33431,plain,(
    ! [A_391,B_392] :
      ( r1_tarski(k3_xboole_0(A_391,B_392),A_391)
      | ~ r1_tarski(k4_xboole_0(A_391,B_392),A_391) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_17425])).

tff(c_33447,plain,(
    ! [B_10,C_11] :
      ( r1_tarski(k3_xboole_0(B_10,C_11),B_10)
      | ~ r1_tarski(B_10,B_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_33431])).

tff(c_33459,plain,(
    ! [B_10,C_11] : r1_tarski(k3_xboole_0(B_10,C_11),B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_33447])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_943,plain,(
    ! [A_91,B_92,C_93] :
      ( k9_subset_1(A_91,B_92,C_93) = k3_xboole_0(B_92,C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1328,plain,(
    ! [B_103] : k9_subset_1('#skF_1',B_103,'#skF_3') = k3_xboole_0(B_103,'#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_943])).

tff(c_30,plain,(
    ! [A_28,B_29,C_30] :
      ( m1_subset_1(k9_subset_1(A_28,B_29,C_30),k1_zfmisc_1(A_28))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1334,plain,(
    ! [B_103] :
      ( m1_subset_1(k3_xboole_0(B_103,'#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1328,c_30])).

tff(c_1340,plain,(
    ! [B_103] : m1_subset_1(k3_xboole_0(B_103,'#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1334])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    ! [A_34,C_37,B_35] :
      ( r1_tarski(k3_subset_1(A_34,C_37),k3_subset_1(A_34,B_35))
      | ~ r1_tarski(B_35,C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_951,plain,(
    ! [B_92] : k9_subset_1('#skF_1',B_92,'#skF_3') = k3_xboole_0(B_92,'#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_943])).

tff(c_38,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k9_subset_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1327,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_951,c_38])).

tff(c_1504,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_1327])).

tff(c_1507,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1340,c_42,c_1504])).

tff(c_33501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33459,c_1507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.89/8.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.89/8.06  
% 14.89/8.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.89/8.06  %$ r1_tarski > m1_subset_1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 14.89/8.06  
% 14.89/8.06  %Foreground sorts:
% 14.89/8.06  
% 14.89/8.06  
% 14.89/8.06  %Background operators:
% 14.89/8.06  
% 14.89/8.06  
% 14.89/8.06  %Foreground operators:
% 14.89/8.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.89/8.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.89/8.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.89/8.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.89/8.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.89/8.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.89/8.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.89/8.06  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.89/8.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.89/8.06  tff('#skF_2', type, '#skF_2': $i).
% 14.89/8.06  tff('#skF_3', type, '#skF_3': $i).
% 14.89/8.06  tff('#skF_1', type, '#skF_1': $i).
% 14.89/8.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.89/8.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.89/8.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.89/8.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.89/8.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.89/8.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.89/8.06  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 14.89/8.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.89/8.06  
% 14.98/8.07  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.98/8.07  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 14.98/8.07  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.98/8.07  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 14.98/8.07  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 14.98/8.07  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 14.98/8.07  tff(f_53, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 14.98/8.07  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 14.98/8.07  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 14.98/8.07  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 14.98/8.07  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 14.98/8.07  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 14.98/8.08  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 14.98/8.08  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.98/8.08  tff(c_14, plain, (![A_9, C_11, B_10]: (r1_tarski(k4_xboole_0(A_9, C_11), B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.98/8.08  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.98/8.08  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.98/8.08  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.98/8.08  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.98/8.08  tff(c_469, plain, (![A_74, B_75]: (k5_xboole_0(k5_xboole_0(A_74, B_75), k2_xboole_0(A_74, B_75))=k3_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.98/8.08  tff(c_518, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, A_18))=k3_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_469])).
% 14.98/8.08  tff(c_524, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, A_18)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_518])).
% 14.98/8.08  tff(c_194, plain, (![A_65, B_66, C_67]: (k5_xboole_0(k5_xboole_0(A_65, B_66), C_67)=k5_xboole_0(A_65, k5_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.98/8.08  tff(c_224, plain, (![A_18, C_67]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_67))=k5_xboole_0(k1_xboole_0, C_67))), inference(superposition, [status(thm), theory('equality')], [c_20, c_194])).
% 14.98/8.08  tff(c_624, plain, (![A_81, C_82]: (k5_xboole_0(A_81, k5_xboole_0(A_81, C_82))=C_82)), inference(demodulation, [status(thm), theory('equality')], [c_524, c_224])).
% 14.98/8.08  tff(c_691, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_20, c_624])).
% 14.98/8.08  tff(c_208, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k5_xboole_0(B_66, k5_xboole_0(A_65, B_66)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_194, c_20])).
% 14.98/8.08  tff(c_674, plain, (![B_66, A_65]: (k5_xboole_0(B_66, k5_xboole_0(A_65, B_66))=k5_xboole_0(A_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_208, c_624])).
% 14.98/8.08  tff(c_860, plain, (![B_89, A_90]: (k5_xboole_0(B_89, k5_xboole_0(A_90, B_89))=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_691, c_674])).
% 14.98/8.08  tff(c_929, plain, (![A_7, B_8]: (k5_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=A_7)), inference(superposition, [status(thm), theory('equality')], [c_12, c_860])).
% 14.98/8.08  tff(c_18, plain, (![A_15, B_16, C_17]: (k5_xboole_0(k5_xboole_0(A_15, B_16), C_17)=k5_xboole_0(A_15, k5_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.98/8.08  tff(c_762, plain, (![A_84, C_85, B_86]: (r1_tarski(k5_xboole_0(A_84, C_85), B_86) | ~r1_tarski(C_85, B_86) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.98/8.08  tff(c_5810, plain, (![A_219, B_220, C_221, B_222]: (r1_tarski(k5_xboole_0(A_219, k5_xboole_0(B_220, C_221)), B_222) | ~r1_tarski(C_221, B_222) | ~r1_tarski(k5_xboole_0(A_219, B_220), B_222))), inference(superposition, [status(thm), theory('equality')], [c_18, c_762])).
% 14.98/8.08  tff(c_6020, plain, (![A_219, B_222, A_18]: (r1_tarski(k5_xboole_0(A_219, k1_xboole_0), B_222) | ~r1_tarski(A_18, B_222) | ~r1_tarski(k5_xboole_0(A_219, A_18), B_222))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5810])).
% 14.98/8.08  tff(c_17129, plain, (![A_320, B_321, A_322]: (r1_tarski(A_320, B_321) | ~r1_tarski(A_322, B_321) | ~r1_tarski(k5_xboole_0(A_320, A_322), B_321))), inference(demodulation, [status(thm), theory('equality')], [c_691, c_6020])).
% 14.98/8.08  tff(c_17337, plain, (![A_323, A_324]: (r1_tarski(A_323, k5_xboole_0(A_323, A_324)) | ~r1_tarski(A_324, k5_xboole_0(A_323, A_324)))), inference(resolution, [status(thm)], [c_10, c_17129])).
% 14.98/8.08  tff(c_17425, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), k5_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))) | ~r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(superposition, [status(thm), theory('equality')], [c_929, c_17337])).
% 14.98/8.08  tff(c_33431, plain, (![A_391, B_392]: (r1_tarski(k3_xboole_0(A_391, B_392), A_391) | ~r1_tarski(k4_xboole_0(A_391, B_392), A_391))), inference(demodulation, [status(thm), theory('equality')], [c_929, c_17425])).
% 14.98/8.08  tff(c_33447, plain, (![B_10, C_11]: (r1_tarski(k3_xboole_0(B_10, C_11), B_10) | ~r1_tarski(B_10, B_10))), inference(resolution, [status(thm)], [c_14, c_33431])).
% 14.98/8.08  tff(c_33459, plain, (![B_10, C_11]: (r1_tarski(k3_xboole_0(B_10, C_11), B_10))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_33447])).
% 14.98/8.08  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.98/8.08  tff(c_943, plain, (![A_91, B_92, C_93]: (k9_subset_1(A_91, B_92, C_93)=k3_xboole_0(B_92, C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.98/8.08  tff(c_1328, plain, (![B_103]: (k9_subset_1('#skF_1', B_103, '#skF_3')=k3_xboole_0(B_103, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_943])).
% 14.98/8.08  tff(c_30, plain, (![A_28, B_29, C_30]: (m1_subset_1(k9_subset_1(A_28, B_29, C_30), k1_zfmisc_1(A_28)) | ~m1_subset_1(C_30, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.98/8.08  tff(c_1334, plain, (![B_103]: (m1_subset_1(k3_xboole_0(B_103, '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1328, c_30])).
% 14.98/8.08  tff(c_1340, plain, (![B_103]: (m1_subset_1(k3_xboole_0(B_103, '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1334])).
% 14.98/8.08  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.98/8.08  tff(c_36, plain, (![A_34, C_37, B_35]: (r1_tarski(k3_subset_1(A_34, C_37), k3_subset_1(A_34, B_35)) | ~r1_tarski(B_35, C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(A_34)) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.98/8.08  tff(c_951, plain, (![B_92]: (k9_subset_1('#skF_1', B_92, '#skF_3')=k3_xboole_0(B_92, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_943])).
% 14.98/8.08  tff(c_38, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k9_subset_1('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.98/8.08  tff(c_1327, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_951, c_38])).
% 14.98/8.08  tff(c_1504, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_1327])).
% 14.98/8.08  tff(c_1507, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1340, c_42, c_1504])).
% 14.98/8.08  tff(c_33501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33459, c_1507])).
% 14.98/8.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.98/8.08  
% 14.98/8.08  Inference rules
% 14.98/8.08  ----------------------
% 14.98/8.08  #Ref     : 0
% 14.98/8.08  #Sup     : 8956
% 14.98/8.08  #Fact    : 0
% 14.98/8.08  #Define  : 0
% 14.98/8.08  #Split   : 0
% 14.98/8.08  #Chain   : 0
% 14.98/8.08  #Close   : 0
% 14.98/8.08  
% 14.98/8.08  Ordering : KBO
% 14.98/8.08  
% 14.98/8.08  Simplification rules
% 14.98/8.08  ----------------------
% 14.98/8.08  #Subsume      : 596
% 14.98/8.08  #Demod        : 9704
% 14.98/8.08  #Tautology    : 2780
% 14.98/8.08  #SimpNegUnit  : 0
% 14.98/8.08  #BackRed      : 9
% 14.98/8.08  
% 14.98/8.08  #Partial instantiations: 0
% 14.98/8.08  #Strategies tried      : 1
% 14.98/8.08  
% 14.98/8.08  Timing (in seconds)
% 14.98/8.08  ----------------------
% 14.98/8.08  Preprocessing        : 0.39
% 14.98/8.08  Parsing              : 0.22
% 14.98/8.08  CNF conversion       : 0.02
% 14.98/8.08  Main loop            : 6.81
% 14.98/8.08  Inferencing          : 1.02
% 14.98/8.08  Reduction            : 4.58
% 14.98/8.08  Demodulation         : 4.29
% 14.98/8.08  BG Simplification    : 0.18
% 14.98/8.08  Subsumption          : 0.84
% 14.98/8.08  Abstraction          : 0.27
% 14.98/8.08  MUC search           : 0.00
% 14.98/8.08  Cooper               : 0.00
% 14.98/8.08  Total                : 7.23
% 14.98/8.08  Index Insertion      : 0.00
% 14.98/8.08  Index Deletion       : 0.00
% 14.98/8.08  Index Matching       : 0.00
% 14.98/8.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
