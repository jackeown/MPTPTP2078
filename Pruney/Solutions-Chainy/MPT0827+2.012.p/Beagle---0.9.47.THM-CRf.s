%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:16 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 110 expanded)
%              Number of leaves         :   34 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  117 ( 176 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2188,plain,(
    ! [A_204,B_205,C_206] :
      ( k2_relset_1(A_204,B_205,C_206) = k2_relat_1(C_206)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2197,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_2188])).

tff(c_28,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_201,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_207,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_201])).

tff(c_211,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_207])).

tff(c_737,plain,(
    ! [A_101] :
      ( r1_tarski(A_101,k2_zfmisc_1(k1_relat_1(A_101),k2_relat_1(A_101)))
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_71,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    k2_xboole_0(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_71])).

tff(c_108,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(k2_xboole_0(A_44,B_46),C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [C_45] :
      ( r1_tarski(k6_relat_1('#skF_3'),C_45)
      | ~ r1_tarski('#skF_4',C_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_108])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_503,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_relat_1(C_78,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_513,plain,(
    ! [A_81,A_82,B_83] :
      ( v4_relat_1(A_81,A_82)
      | ~ r1_tarski(A_81,k2_zfmisc_1(A_82,B_83)) ) ),
    inference(resolution,[status(thm)],[c_14,c_503])).

tff(c_539,plain,(
    ! [A_82,B_83] :
      ( v4_relat_1(k6_relat_1('#skF_3'),A_82)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_82,B_83)) ) ),
    inference(resolution,[status(thm)],[c_111,c_513])).

tff(c_740,plain,
    ( v4_relat_1(k6_relat_1('#skF_3'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_737,c_539])).

tff(c_776,plain,(
    v4_relat_1(k6_relat_1('#skF_3'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_740])).

tff(c_26,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_212,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k1_relat_1(B_58),A_59)
      | ~ v4_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_220,plain,(
    ! [A_21,A_59] :
      ( r1_tarski(A_21,A_59)
      | ~ v4_relat_1(k6_relat_1(A_21),A_59)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_212])).

tff(c_224,plain,(
    ! [A_21,A_59] :
      ( r1_tarski(A_21,A_59)
      | ~ v4_relat_1(k6_relat_1(A_21),A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_220])).

tff(c_796,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_776,c_224])).

tff(c_1024,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_relset_1(A_113,B_114,C_115) = k1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1033,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1024])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_89,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_1044,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1033,c_89])).

tff(c_1047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_1044])).

tff(c_1048,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2235,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2197,c_1048])).

tff(c_1072,plain,(
    ! [B_121,A_122] :
      ( v1_relat_1(B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_122))
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1078,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_1072])).

tff(c_1082,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1078])).

tff(c_30,plain,(
    ! [A_20] :
      ( r1_tarski(A_20,k2_zfmisc_1(k1_relat_1(A_20),k2_relat_1(A_20)))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1083,plain,(
    ! [A_123,C_124,B_125] :
      ( r1_tarski(A_123,C_124)
      | ~ r1_tarski(k2_xboole_0(A_123,B_125),C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1086,plain,(
    ! [C_124] :
      ( r1_tarski(k6_relat_1('#skF_3'),C_124)
      | ~ r1_tarski('#skF_4',C_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_1083])).

tff(c_1604,plain,(
    ! [C_170,B_171,A_172] :
      ( v5_relat_1(C_170,B_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_172,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1614,plain,(
    ! [A_173,B_174,A_175] :
      ( v5_relat_1(A_173,B_174)
      | ~ r1_tarski(A_173,k2_zfmisc_1(A_175,B_174)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1604])).

tff(c_2794,plain,(
    ! [B_234,A_235] :
      ( v5_relat_1(k6_relat_1('#skF_3'),B_234)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_235,B_234)) ) ),
    inference(resolution,[status(thm)],[c_1086,c_1614])).

tff(c_2797,plain,
    ( v5_relat_1(k6_relat_1('#skF_3'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_2794])).

tff(c_2802,plain,(
    v5_relat_1(k6_relat_1('#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_2797])).

tff(c_34,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1439,plain,(
    ! [B_147,A_148] :
      ( r1_tarski(k2_relat_1(B_147),A_148)
      | ~ v5_relat_1(B_147,A_148)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1450,plain,(
    ! [A_21,A_148] :
      ( r1_tarski(A_21,A_148)
      | ~ v5_relat_1(k6_relat_1(A_21),A_148)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1439])).

tff(c_1455,plain,(
    ! [A_21,A_148] :
      ( r1_tarski(A_21,A_148)
      | ~ v5_relat_1(k6_relat_1(A_21),A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1450])).

tff(c_2810,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2802,c_1455])).

tff(c_2815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2235,c_2810])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:19:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.73  
% 3.95/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.73  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.95/1.73  
% 3.95/1.73  %Foreground sorts:
% 3.95/1.73  
% 3.95/1.73  
% 3.95/1.73  %Background operators:
% 3.95/1.73  
% 3.95/1.73  
% 3.95/1.73  %Foreground operators:
% 3.95/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.95/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.95/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.95/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.95/1.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.95/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.95/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.95/1.73  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.95/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.95/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.95/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.95/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.73  
% 3.95/1.75  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 3.95/1.75  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.95/1.75  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.95/1.75  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.95/1.75  tff(f_70, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.95/1.75  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.95/1.75  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.95/1.75  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.95/1.75  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.95/1.75  tff(f_64, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.95/1.75  tff(f_74, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.95/1.75  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.95/1.75  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.95/1.75  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.95/1.75  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.95/1.75  tff(c_2188, plain, (![A_204, B_205, C_206]: (k2_relset_1(A_204, B_205, C_206)=k2_relat_1(C_206) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.95/1.75  tff(c_2197, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_2188])).
% 3.95/1.75  tff(c_28, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.95/1.75  tff(c_201, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.95/1.75  tff(c_207, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_201])).
% 3.95/1.75  tff(c_211, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_207])).
% 3.95/1.75  tff(c_737, plain, (![A_101]: (r1_tarski(A_101, k2_zfmisc_1(k1_relat_1(A_101), k2_relat_1(A_101))) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.95/1.75  tff(c_46, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.95/1.75  tff(c_71, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.75  tff(c_78, plain, (k2_xboole_0(k6_relat_1('#skF_3'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_71])).
% 3.95/1.75  tff(c_108, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(k2_xboole_0(A_44, B_46), C_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.95/1.75  tff(c_111, plain, (![C_45]: (r1_tarski(k6_relat_1('#skF_3'), C_45) | ~r1_tarski('#skF_4', C_45))), inference(superposition, [status(thm), theory('equality')], [c_78, c_108])).
% 3.95/1.75  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.95/1.75  tff(c_503, plain, (![C_78, A_79, B_80]: (v4_relat_1(C_78, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.95/1.75  tff(c_513, plain, (![A_81, A_82, B_83]: (v4_relat_1(A_81, A_82) | ~r1_tarski(A_81, k2_zfmisc_1(A_82, B_83)))), inference(resolution, [status(thm)], [c_14, c_503])).
% 3.95/1.75  tff(c_539, plain, (![A_82, B_83]: (v4_relat_1(k6_relat_1('#skF_3'), A_82) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_82, B_83)))), inference(resolution, [status(thm)], [c_111, c_513])).
% 3.95/1.75  tff(c_740, plain, (v4_relat_1(k6_relat_1('#skF_3'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_737, c_539])).
% 3.95/1.75  tff(c_776, plain, (v4_relat_1(k6_relat_1('#skF_3'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_740])).
% 3.95/1.75  tff(c_26, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.95/1.75  tff(c_32, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.95/1.75  tff(c_212, plain, (![B_58, A_59]: (r1_tarski(k1_relat_1(B_58), A_59) | ~v4_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.95/1.75  tff(c_220, plain, (![A_21, A_59]: (r1_tarski(A_21, A_59) | ~v4_relat_1(k6_relat_1(A_21), A_59) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_212])).
% 3.95/1.75  tff(c_224, plain, (![A_21, A_59]: (r1_tarski(A_21, A_59) | ~v4_relat_1(k6_relat_1(A_21), A_59))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_220])).
% 3.95/1.75  tff(c_796, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_776, c_224])).
% 3.95/1.75  tff(c_1024, plain, (![A_113, B_114, C_115]: (k1_relset_1(A_113, B_114, C_115)=k1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.95/1.75  tff(c_1033, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1024])).
% 3.95/1.75  tff(c_44, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.95/1.75  tff(c_89, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.95/1.75  tff(c_1044, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1033, c_89])).
% 3.95/1.75  tff(c_1047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_796, c_1044])).
% 3.95/1.75  tff(c_1048, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 3.95/1.75  tff(c_2235, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2197, c_1048])).
% 3.95/1.75  tff(c_1072, plain, (![B_121, A_122]: (v1_relat_1(B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(A_122)) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.95/1.75  tff(c_1078, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_1072])).
% 3.95/1.75  tff(c_1082, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1078])).
% 3.95/1.75  tff(c_30, plain, (![A_20]: (r1_tarski(A_20, k2_zfmisc_1(k1_relat_1(A_20), k2_relat_1(A_20))) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.95/1.75  tff(c_1083, plain, (![A_123, C_124, B_125]: (r1_tarski(A_123, C_124) | ~r1_tarski(k2_xboole_0(A_123, B_125), C_124))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.95/1.75  tff(c_1086, plain, (![C_124]: (r1_tarski(k6_relat_1('#skF_3'), C_124) | ~r1_tarski('#skF_4', C_124))), inference(superposition, [status(thm), theory('equality')], [c_78, c_1083])).
% 3.95/1.75  tff(c_1604, plain, (![C_170, B_171, A_172]: (v5_relat_1(C_170, B_171) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_172, B_171))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.95/1.75  tff(c_1614, plain, (![A_173, B_174, A_175]: (v5_relat_1(A_173, B_174) | ~r1_tarski(A_173, k2_zfmisc_1(A_175, B_174)))), inference(resolution, [status(thm)], [c_14, c_1604])).
% 3.95/1.75  tff(c_2794, plain, (![B_234, A_235]: (v5_relat_1(k6_relat_1('#skF_3'), B_234) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_235, B_234)))), inference(resolution, [status(thm)], [c_1086, c_1614])).
% 3.95/1.75  tff(c_2797, plain, (v5_relat_1(k6_relat_1('#skF_3'), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_2794])).
% 3.95/1.75  tff(c_2802, plain, (v5_relat_1(k6_relat_1('#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1082, c_2797])).
% 3.95/1.75  tff(c_34, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.95/1.75  tff(c_1439, plain, (![B_147, A_148]: (r1_tarski(k2_relat_1(B_147), A_148) | ~v5_relat_1(B_147, A_148) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.95/1.75  tff(c_1450, plain, (![A_21, A_148]: (r1_tarski(A_21, A_148) | ~v5_relat_1(k6_relat_1(A_21), A_148) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1439])).
% 3.95/1.75  tff(c_1455, plain, (![A_21, A_148]: (r1_tarski(A_21, A_148) | ~v5_relat_1(k6_relat_1(A_21), A_148))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1450])).
% 3.95/1.75  tff(c_2810, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2802, c_1455])).
% 3.95/1.75  tff(c_2815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2235, c_2810])).
% 3.95/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.75  
% 3.95/1.75  Inference rules
% 3.95/1.75  ----------------------
% 3.95/1.75  #Ref     : 0
% 3.95/1.75  #Sup     : 611
% 3.95/1.75  #Fact    : 0
% 3.95/1.75  #Define  : 0
% 3.95/1.75  #Split   : 21
% 3.95/1.75  #Chain   : 0
% 3.95/1.75  #Close   : 0
% 3.95/1.75  
% 3.95/1.75  Ordering : KBO
% 3.95/1.75  
% 3.95/1.75  Simplification rules
% 3.95/1.75  ----------------------
% 3.95/1.75  #Subsume      : 70
% 3.95/1.75  #Demod        : 306
% 3.95/1.75  #Tautology    : 272
% 3.95/1.75  #SimpNegUnit  : 1
% 3.95/1.75  #BackRed      : 11
% 3.95/1.75  
% 3.95/1.75  #Partial instantiations: 0
% 3.95/1.75  #Strategies tried      : 1
% 3.95/1.75  
% 3.95/1.75  Timing (in seconds)
% 3.95/1.75  ----------------------
% 3.95/1.75  Preprocessing        : 0.31
% 3.95/1.75  Parsing              : 0.16
% 3.95/1.75  CNF conversion       : 0.02
% 3.95/1.75  Main loop            : 0.65
% 3.95/1.75  Inferencing          : 0.23
% 3.95/1.75  Reduction            : 0.23
% 3.95/1.75  Demodulation         : 0.16
% 3.95/1.75  BG Simplification    : 0.02
% 3.95/1.75  Subsumption          : 0.11
% 3.95/1.75  Abstraction          : 0.03
% 3.95/1.75  MUC search           : 0.00
% 3.95/1.75  Cooper               : 0.00
% 3.95/1.75  Total                : 0.99
% 3.95/1.75  Index Insertion      : 0.00
% 3.95/1.75  Index Deletion       : 0.00
% 3.95/1.75  Index Matching       : 0.00
% 3.95/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
