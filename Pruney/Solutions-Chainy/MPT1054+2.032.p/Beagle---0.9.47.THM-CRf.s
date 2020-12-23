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
% DateTime   : Thu Dec  3 10:17:16 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 151 expanded)
%              Number of leaves         :   38 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 187 expanded)
%              Number of equality atoms :   35 (  94 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_72,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(c_38,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    ! [A_19] : v1_relat_1(k6_partfun1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22])).

tff(c_18,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [A_18] : k1_relat_1(k6_partfun1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_18])).

tff(c_30,plain,(
    ! [B_25,A_24] : k5_relat_1(k6_relat_1(B_25),k6_relat_1(A_24)) = k6_relat_1(k3_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_43,plain,(
    ! [B_25,A_24] : k5_relat_1(k6_partfun1(B_25),k6_partfun1(A_24)) = k6_partfun1(k3_xboole_0(A_24,B_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_38,c_30])).

tff(c_292,plain,(
    ! [A_87,B_88] :
      ( k10_relat_1(A_87,k1_relat_1(B_88)) = k1_relat_1(k5_relat_1(A_87,B_88))
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_301,plain,(
    ! [A_87,A_18] :
      ( k1_relat_1(k5_relat_1(A_87,k6_partfun1(A_18))) = k10_relat_1(A_87,A_18)
      | ~ v1_relat_1(k6_partfun1(A_18))
      | ~ v1_relat_1(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_292])).

tff(c_306,plain,(
    ! [A_89,A_90] :
      ( k1_relat_1(k5_relat_1(A_89,k6_partfun1(A_90))) = k10_relat_1(A_89,A_90)
      | ~ v1_relat_1(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_301])).

tff(c_318,plain,(
    ! [A_24,B_25] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_24,B_25))) = k10_relat_1(k6_partfun1(B_25),A_24)
      | ~ v1_relat_1(k6_partfun1(B_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_306])).

tff(c_322,plain,(
    ! [B_25,A_24] : k10_relat_1(k6_partfun1(B_25),A_24) = k3_xboole_0(A_24,B_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_318])).

tff(c_36,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_445,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k8_relset_1(A_112,B_113,C_114,D_115) = k10_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_447,plain,(
    ! [A_30,D_115] : k8_relset_1(A_30,A_30,k6_partfun1(A_30),D_115) = k10_relat_1(k6_partfun1(A_30),D_115) ),
    inference(resolution,[status(thm)],[c_36,c_445])).

tff(c_452,plain,(
    ! [A_30,D_115] : k8_relset_1(A_30,A_30,k6_partfun1(A_30),D_115) = k3_xboole_0(D_115,A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_447])).

tff(c_40,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_454,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_40])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_100,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_112,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_100])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_140,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,C_56)
      | ~ r1_tarski(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_150,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,'#skF_1')
      | ~ r1_tarski(A_58,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_112,c_140])).

tff(c_155,plain,(
    ! [B_2] : r1_tarski(k3_xboole_0('#skF_2',B_2),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_150])).

tff(c_24,plain,(
    ! [A_19] : v1_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_45,plain,(
    ! [A_19] : v1_funct_1(k6_partfun1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_24])).

tff(c_20,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_47,plain,(
    ! [A_18] : k2_relat_1(k6_partfun1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20])).

tff(c_522,plain,(
    ! [B_127,A_128] :
      ( k9_relat_1(B_127,k10_relat_1(B_127,A_128)) = A_128
      | ~ r1_tarski(A_128,k2_relat_1(B_127))
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_536,plain,(
    ! [A_18,A_128] :
      ( k9_relat_1(k6_partfun1(A_18),k10_relat_1(k6_partfun1(A_18),A_128)) = A_128
      | ~ r1_tarski(A_128,A_18)
      | ~ v1_funct_1(k6_partfun1(A_18))
      | ~ v1_relat_1(k6_partfun1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_522])).

tff(c_543,plain,(
    ! [A_129,A_130] :
      ( k9_relat_1(k6_partfun1(A_129),k3_xboole_0(A_130,A_129)) = A_130
      | ~ r1_tarski(A_130,A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_45,c_322,c_536])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( k9_relat_1(k6_relat_1(A_22),B_23) = B_23
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_123,plain,(
    ! [A_53,B_54] :
      ( k9_relat_1(k6_partfun1(A_53),B_54) = B_54
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28])).

tff(c_134,plain,(
    ! [B_14,A_13] :
      ( k9_relat_1(k6_partfun1(B_14),A_13) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_123])).

tff(c_559,plain,(
    ! [A_131,A_132] :
      ( k3_xboole_0(A_131,A_132) = A_131
      | ~ r1_tarski(k3_xboole_0(A_131,A_132),A_132)
      | ~ r1_tarski(A_131,A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_134])).

tff(c_599,plain,
    ( k3_xboole_0('#skF_2','#skF_1') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_155,c_559])).

tff(c_627,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_599])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_454,c_627])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.42  
% 2.51/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.42  %$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.51/1.42  
% 2.51/1.42  %Foreground sorts:
% 2.51/1.42  
% 2.51/1.42  
% 2.51/1.42  %Background operators:
% 2.51/1.42  
% 2.51/1.42  
% 2.51/1.42  %Foreground operators:
% 2.51/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.51/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.42  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.51/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.51/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.51/1.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.51/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.42  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.51/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.51/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.51/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.51/1.42  
% 2.89/1.44  tff(f_82, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.89/1.44  tff(f_58, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.89/1.44  tff(f_54, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.89/1.44  tff(f_72, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.89/1.44  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.89/1.44  tff(f_80, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.89/1.44  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.89/1.44  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.89/1.44  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.89/1.44  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.89/1.44  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.89/1.44  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.89/1.44  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.89/1.44  tff(c_38, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.89/1.44  tff(c_22, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.89/1.44  tff(c_46, plain, (![A_19]: (v1_relat_1(k6_partfun1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_22])).
% 2.89/1.44  tff(c_18, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.89/1.44  tff(c_48, plain, (![A_18]: (k1_relat_1(k6_partfun1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_18])).
% 2.89/1.44  tff(c_30, plain, (![B_25, A_24]: (k5_relat_1(k6_relat_1(B_25), k6_relat_1(A_24))=k6_relat_1(k3_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.89/1.44  tff(c_43, plain, (![B_25, A_24]: (k5_relat_1(k6_partfun1(B_25), k6_partfun1(A_24))=k6_partfun1(k3_xboole_0(A_24, B_25)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_38, c_30])).
% 2.89/1.44  tff(c_292, plain, (![A_87, B_88]: (k10_relat_1(A_87, k1_relat_1(B_88))=k1_relat_1(k5_relat_1(A_87, B_88)) | ~v1_relat_1(B_88) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.89/1.44  tff(c_301, plain, (![A_87, A_18]: (k1_relat_1(k5_relat_1(A_87, k6_partfun1(A_18)))=k10_relat_1(A_87, A_18) | ~v1_relat_1(k6_partfun1(A_18)) | ~v1_relat_1(A_87))), inference(superposition, [status(thm), theory('equality')], [c_48, c_292])).
% 2.89/1.44  tff(c_306, plain, (![A_89, A_90]: (k1_relat_1(k5_relat_1(A_89, k6_partfun1(A_90)))=k10_relat_1(A_89, A_90) | ~v1_relat_1(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_301])).
% 2.89/1.44  tff(c_318, plain, (![A_24, B_25]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_24, B_25)))=k10_relat_1(k6_partfun1(B_25), A_24) | ~v1_relat_1(k6_partfun1(B_25)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_306])).
% 2.89/1.44  tff(c_322, plain, (![B_25, A_24]: (k10_relat_1(k6_partfun1(B_25), A_24)=k3_xboole_0(A_24, B_25))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_318])).
% 2.89/1.44  tff(c_36, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.89/1.44  tff(c_445, plain, (![A_112, B_113, C_114, D_115]: (k8_relset_1(A_112, B_113, C_114, D_115)=k10_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.89/1.44  tff(c_447, plain, (![A_30, D_115]: (k8_relset_1(A_30, A_30, k6_partfun1(A_30), D_115)=k10_relat_1(k6_partfun1(A_30), D_115))), inference(resolution, [status(thm)], [c_36, c_445])).
% 2.89/1.44  tff(c_452, plain, (![A_30, D_115]: (k8_relset_1(A_30, A_30, k6_partfun1(A_30), D_115)=k3_xboole_0(D_115, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_447])).
% 2.89/1.44  tff(c_40, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.89/1.44  tff(c_454, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_452, c_40])).
% 2.89/1.44  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.89/1.44  tff(c_100, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.44  tff(c_112, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_100])).
% 2.89/1.44  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.89/1.44  tff(c_140, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, C_56) | ~r1_tarski(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.89/1.44  tff(c_150, plain, (![A_58]: (r1_tarski(A_58, '#skF_1') | ~r1_tarski(A_58, '#skF_2'))), inference(resolution, [status(thm)], [c_112, c_140])).
% 2.89/1.44  tff(c_155, plain, (![B_2]: (r1_tarski(k3_xboole_0('#skF_2', B_2), '#skF_1'))), inference(resolution, [status(thm)], [c_2, c_150])).
% 2.89/1.44  tff(c_24, plain, (![A_19]: (v1_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.89/1.44  tff(c_45, plain, (![A_19]: (v1_funct_1(k6_partfun1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_24])).
% 2.89/1.44  tff(c_20, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.89/1.44  tff(c_47, plain, (![A_18]: (k2_relat_1(k6_partfun1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20])).
% 2.89/1.44  tff(c_522, plain, (![B_127, A_128]: (k9_relat_1(B_127, k10_relat_1(B_127, A_128))=A_128 | ~r1_tarski(A_128, k2_relat_1(B_127)) | ~v1_funct_1(B_127) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.89/1.44  tff(c_536, plain, (![A_18, A_128]: (k9_relat_1(k6_partfun1(A_18), k10_relat_1(k6_partfun1(A_18), A_128))=A_128 | ~r1_tarski(A_128, A_18) | ~v1_funct_1(k6_partfun1(A_18)) | ~v1_relat_1(k6_partfun1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_47, c_522])).
% 2.89/1.44  tff(c_543, plain, (![A_129, A_130]: (k9_relat_1(k6_partfun1(A_129), k3_xboole_0(A_130, A_129))=A_130 | ~r1_tarski(A_130, A_129))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_45, c_322, c_536])).
% 2.89/1.44  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.44  tff(c_28, plain, (![A_22, B_23]: (k9_relat_1(k6_relat_1(A_22), B_23)=B_23 | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.89/1.44  tff(c_123, plain, (![A_53, B_54]: (k9_relat_1(k6_partfun1(A_53), B_54)=B_54 | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28])).
% 2.89/1.44  tff(c_134, plain, (![B_14, A_13]: (k9_relat_1(k6_partfun1(B_14), A_13)=A_13 | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_14, c_123])).
% 2.89/1.44  tff(c_559, plain, (![A_131, A_132]: (k3_xboole_0(A_131, A_132)=A_131 | ~r1_tarski(k3_xboole_0(A_131, A_132), A_132) | ~r1_tarski(A_131, A_132))), inference(superposition, [status(thm), theory('equality')], [c_543, c_134])).
% 2.89/1.44  tff(c_599, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_155, c_559])).
% 2.89/1.44  tff(c_627, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_599])).
% 2.89/1.44  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_454, c_627])).
% 2.89/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.44  
% 2.89/1.44  Inference rules
% 2.89/1.44  ----------------------
% 2.89/1.44  #Ref     : 0
% 2.89/1.44  #Sup     : 123
% 2.89/1.44  #Fact    : 0
% 2.89/1.44  #Define  : 0
% 2.89/1.44  #Split   : 0
% 2.89/1.44  #Chain   : 0
% 2.89/1.44  #Close   : 0
% 2.89/1.44  
% 2.89/1.44  Ordering : KBO
% 2.89/1.44  
% 2.89/1.44  Simplification rules
% 2.89/1.44  ----------------------
% 2.89/1.44  #Subsume      : 1
% 2.89/1.44  #Demod        : 48
% 2.89/1.44  #Tautology    : 48
% 2.89/1.44  #SimpNegUnit  : 1
% 2.89/1.44  #BackRed      : 1
% 2.89/1.44  
% 2.89/1.44  #Partial instantiations: 0
% 2.89/1.44  #Strategies tried      : 1
% 2.89/1.44  
% 2.89/1.44  Timing (in seconds)
% 2.89/1.44  ----------------------
% 2.89/1.44  Preprocessing        : 0.32
% 2.89/1.44  Parsing              : 0.18
% 2.89/1.44  CNF conversion       : 0.02
% 2.89/1.44  Main loop            : 0.32
% 2.89/1.44  Inferencing          : 0.12
% 2.89/1.44  Reduction            : 0.10
% 2.89/1.44  Demodulation         : 0.07
% 2.89/1.44  BG Simplification    : 0.02
% 2.89/1.44  Subsumption          : 0.06
% 2.89/1.44  Abstraction          : 0.02
% 2.89/1.44  MUC search           : 0.00
% 2.89/1.44  Cooper               : 0.00
% 2.89/1.44  Total                : 0.67
% 2.89/1.44  Index Insertion      : 0.00
% 2.89/1.44  Index Deletion       : 0.00
% 2.89/1.44  Index Matching       : 0.00
% 2.89/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
