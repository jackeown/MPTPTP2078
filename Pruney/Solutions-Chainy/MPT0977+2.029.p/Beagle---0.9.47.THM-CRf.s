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
% DateTime   : Thu Dec  3 10:11:49 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 137 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 223 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_92,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_53,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_65,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_59])).

tff(c_423,plain,(
    ! [A_114,B_115,D_116] :
      ( r2_relset_1(A_114,B_115,D_116,D_116)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_429,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_423])).

tff(c_302,plain,(
    ! [C_94,B_95,A_96] :
      ( v5_relat_1(C_94,B_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_310,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_302])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_351,plain,(
    ! [A_106,B_107] :
      ( k8_relat_1(A_106,B_107) = B_107
      | ~ r1_tarski(k2_relat_1(B_107),A_106)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_356,plain,(
    ! [A_108,B_109] :
      ( k8_relat_1(A_108,B_109) = B_109
      | ~ v5_relat_1(B_109,A_108)
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_6,c_351])).

tff(c_362,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_310,c_356])).

tff(c_368,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_362])).

tff(c_34,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_partfun1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_32,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_496,plain,(
    ! [E_138,B_137,A_133,D_134,F_136,C_135] :
      ( k4_relset_1(A_133,B_137,C_135,D_134,E_138,F_136) = k5_relat_1(E_138,F_136)
      | ~ m1_subset_1(F_136,k1_zfmisc_1(k2_zfmisc_1(C_135,D_134)))
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(A_133,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_540,plain,(
    ! [A_143,B_144,A_145,E_146] :
      ( k4_relset_1(A_143,B_144,A_145,A_145,E_146,k6_partfun1(A_145)) = k5_relat_1(E_146,k6_partfun1(A_145))
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(resolution,[status(thm)],[c_32,c_496])).

tff(c_546,plain,(
    ! [A_145] : k4_relset_1('#skF_1','#skF_2',A_145,A_145,'#skF_3',k6_partfun1(A_145)) = k5_relat_1('#skF_3',k6_partfun1(A_145)) ),
    inference(resolution,[status(thm)],[c_38,c_540])).

tff(c_172,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_relset_1(A_66,B_67,D_68,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_178,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_172])).

tff(c_70,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_78,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_81,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_14])).

tff(c_84,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_81])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_17,A_16)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_95,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_18])).

tff(c_99,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_95])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = B_15
      | ~ r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_180,plain,(
    ! [A_70,B_71] :
      ( k5_relat_1(k6_partfun1(A_70),B_71) = B_71
      | ~ r1_tarski(k1_relat_1(B_71),A_70)
      | ~ v1_relat_1(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16])).

tff(c_186,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_99,c_180])).

tff(c_195,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_186])).

tff(c_253,plain,(
    ! [C_81,D_80,B_83,E_84,F_82,A_79] :
      ( k4_relset_1(A_79,B_83,C_81,D_80,E_84,F_82) = k5_relat_1(E_84,F_82)
      | ~ m1_subset_1(F_82,k1_zfmisc_1(k2_zfmisc_1(C_81,D_80)))
      | ~ m1_subset_1(E_84,k1_zfmisc_1(k2_zfmisc_1(A_79,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_260,plain,(
    ! [A_85,B_86,E_87] :
      ( k4_relset_1(A_85,B_86,'#skF_1','#skF_2',E_87,'#skF_3') = k5_relat_1(E_87,'#skF_3')
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(resolution,[status(thm)],[c_38,c_253])).

tff(c_267,plain,(
    ! [A_31] : k4_relset_1(A_31,A_31,'#skF_1','#skF_2',k6_partfun1(A_31),'#skF_3') = k5_relat_1(k6_partfun1(A_31),'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_260])).

tff(c_36,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_68,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_273,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_68])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_195,c_273])).

tff(c_277,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_547,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_277])).

tff(c_559,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_547])).

tff(c_562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_429,c_368,c_559])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.41  
% 2.70/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.42  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.70/1.42  
% 2.70/1.42  %Foreground sorts:
% 2.70/1.42  
% 2.70/1.42  
% 2.70/1.42  %Background operators:
% 2.70/1.42  
% 2.70/1.42  
% 2.70/1.42  %Foreground operators:
% 2.70/1.42  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.42  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.70/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.70/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.70/1.42  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.70/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.70/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.42  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.70/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.42  
% 2.70/1.43  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.70/1.43  tff(f_99, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.70/1.43  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.70/1.43  tff(f_86, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.70/1.43  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.70/1.43  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.70/1.43  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.70/1.43  tff(f_92, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.70/1.43  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.70/1.43  tff(f_90, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.70/1.43  tff(f_78, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.70/1.43  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.70/1.43  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.70/1.43  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.70/1.43  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.70/1.43  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.70/1.43  tff(c_53, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.70/1.43  tff(c_59, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.70/1.43  tff(c_65, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_59])).
% 2.70/1.43  tff(c_423, plain, (![A_114, B_115, D_116]: (r2_relset_1(A_114, B_115, D_116, D_116) | ~m1_subset_1(D_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.70/1.43  tff(c_429, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_423])).
% 2.70/1.43  tff(c_302, plain, (![C_94, B_95, A_96]: (v5_relat_1(C_94, B_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.70/1.43  tff(c_310, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_302])).
% 2.70/1.43  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.70/1.43  tff(c_351, plain, (![A_106, B_107]: (k8_relat_1(A_106, B_107)=B_107 | ~r1_tarski(k2_relat_1(B_107), A_106) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.70/1.43  tff(c_356, plain, (![A_108, B_109]: (k8_relat_1(A_108, B_109)=B_109 | ~v5_relat_1(B_109, A_108) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_6, c_351])).
% 2.70/1.43  tff(c_362, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_310, c_356])).
% 2.70/1.43  tff(c_368, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_362])).
% 2.70/1.43  tff(c_34, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.70/1.43  tff(c_10, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.70/1.43  tff(c_40, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_partfun1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10])).
% 2.70/1.43  tff(c_32, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.70/1.43  tff(c_496, plain, (![E_138, B_137, A_133, D_134, F_136, C_135]: (k4_relset_1(A_133, B_137, C_135, D_134, E_138, F_136)=k5_relat_1(E_138, F_136) | ~m1_subset_1(F_136, k1_zfmisc_1(k2_zfmisc_1(C_135, D_134))) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(A_133, B_137))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.70/1.43  tff(c_540, plain, (![A_143, B_144, A_145, E_146]: (k4_relset_1(A_143, B_144, A_145, A_145, E_146, k6_partfun1(A_145))=k5_relat_1(E_146, k6_partfun1(A_145)) | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(resolution, [status(thm)], [c_32, c_496])).
% 2.70/1.43  tff(c_546, plain, (![A_145]: (k4_relset_1('#skF_1', '#skF_2', A_145, A_145, '#skF_3', k6_partfun1(A_145))=k5_relat_1('#skF_3', k6_partfun1(A_145)))), inference(resolution, [status(thm)], [c_38, c_540])).
% 2.70/1.43  tff(c_172, plain, (![A_66, B_67, D_68]: (r2_relset_1(A_66, B_67, D_68, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.70/1.43  tff(c_178, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_172])).
% 2.70/1.43  tff(c_70, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.70/1.43  tff(c_78, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_70])).
% 2.70/1.43  tff(c_14, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.43  tff(c_81, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_14])).
% 2.70/1.43  tff(c_84, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_81])).
% 2.70/1.43  tff(c_18, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(k7_relat_1(B_17, A_16)), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.70/1.43  tff(c_95, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_84, c_18])).
% 2.70/1.43  tff(c_99, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_95])).
% 2.70/1.43  tff(c_16, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.70/1.43  tff(c_180, plain, (![A_70, B_71]: (k5_relat_1(k6_partfun1(A_70), B_71)=B_71 | ~r1_tarski(k1_relat_1(B_71), A_70) | ~v1_relat_1(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16])).
% 2.70/1.43  tff(c_186, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_99, c_180])).
% 2.70/1.43  tff(c_195, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_186])).
% 2.70/1.43  tff(c_253, plain, (![C_81, D_80, B_83, E_84, F_82, A_79]: (k4_relset_1(A_79, B_83, C_81, D_80, E_84, F_82)=k5_relat_1(E_84, F_82) | ~m1_subset_1(F_82, k1_zfmisc_1(k2_zfmisc_1(C_81, D_80))) | ~m1_subset_1(E_84, k1_zfmisc_1(k2_zfmisc_1(A_79, B_83))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.70/1.43  tff(c_260, plain, (![A_85, B_86, E_87]: (k4_relset_1(A_85, B_86, '#skF_1', '#skF_2', E_87, '#skF_3')=k5_relat_1(E_87, '#skF_3') | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(resolution, [status(thm)], [c_38, c_253])).
% 2.70/1.43  tff(c_267, plain, (![A_31]: (k4_relset_1(A_31, A_31, '#skF_1', '#skF_2', k6_partfun1(A_31), '#skF_3')=k5_relat_1(k6_partfun1(A_31), '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_260])).
% 2.70/1.43  tff(c_36, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.70/1.43  tff(c_68, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 2.70/1.43  tff(c_273, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_267, c_68])).
% 2.70/1.43  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_195, c_273])).
% 2.70/1.43  tff(c_277, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.70/1.43  tff(c_547, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_546, c_277])).
% 2.70/1.43  tff(c_559, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_547])).
% 2.70/1.43  tff(c_562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_429, c_368, c_559])).
% 2.70/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.43  
% 2.70/1.43  Inference rules
% 2.70/1.43  ----------------------
% 2.70/1.43  #Ref     : 0
% 2.70/1.43  #Sup     : 112
% 2.70/1.43  #Fact    : 0
% 2.70/1.43  #Define  : 0
% 2.70/1.43  #Split   : 2
% 2.70/1.43  #Chain   : 0
% 2.70/1.43  #Close   : 0
% 2.70/1.43  
% 2.70/1.43  Ordering : KBO
% 2.70/1.43  
% 2.70/1.43  Simplification rules
% 2.70/1.43  ----------------------
% 2.70/1.43  #Subsume      : 0
% 2.70/1.43  #Demod        : 70
% 2.70/1.43  #Tautology    : 64
% 2.70/1.43  #SimpNegUnit  : 0
% 2.70/1.43  #BackRed      : 5
% 2.70/1.43  
% 2.70/1.43  #Partial instantiations: 0
% 2.70/1.43  #Strategies tried      : 1
% 2.70/1.43  
% 2.70/1.43  Timing (in seconds)
% 2.70/1.43  ----------------------
% 2.70/1.44  Preprocessing        : 0.30
% 2.70/1.44  Parsing              : 0.16
% 2.70/1.44  CNF conversion       : 0.02
% 2.70/1.44  Main loop            : 0.28
% 2.70/1.44  Inferencing          : 0.12
% 2.70/1.44  Reduction            : 0.09
% 2.70/1.44  Demodulation         : 0.07
% 2.70/1.44  BG Simplification    : 0.02
% 2.70/1.44  Subsumption          : 0.03
% 2.70/1.44  Abstraction          : 0.02
% 2.70/1.44  MUC search           : 0.00
% 2.70/1.44  Cooper               : 0.00
% 2.70/1.44  Total                : 0.62
% 2.70/1.44  Index Insertion      : 0.00
% 2.70/1.44  Index Deletion       : 0.00
% 2.70/1.44  Index Matching       : 0.00
% 2.70/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
