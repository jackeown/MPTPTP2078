%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:47 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 122 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  104 ( 189 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_77,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_333,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( r2_relset_1(A_101,B_102,C_103,C_103)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_352,plain,(
    ! [C_114] :
      ( r2_relset_1('#skF_1','#skF_2',C_114,C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_333])).

tff(c_355,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_352])).

tff(c_230,plain,(
    ! [C_82,B_83,A_84] :
      ( v5_relat_1(C_82,B_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_238,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_230])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_311,plain,(
    ! [A_97,B_98] :
      ( k8_relat_1(A_97,B_98) = B_98
      | ~ r1_tarski(k2_relat_1(B_98),A_97)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_316,plain,(
    ! [A_99,B_100] :
      ( k8_relat_1(A_99,B_100) = B_100
      | ~ v5_relat_1(B_100,A_99)
      | ~ v1_relat_1(B_100) ) ),
    inference(resolution,[status(thm)],[c_4,c_311])).

tff(c_322,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_238,c_316])).

tff(c_328,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_322])).

tff(c_26,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = k8_relat_1(A_3,B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_33,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_partfun1(A_3)) = k8_relat_1(A_3,B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6])).

tff(c_24,plain,(
    ! [A_27] : m1_subset_1(k6_relat_1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_31,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24])).

tff(c_340,plain,(
    ! [D_109,F_108,B_107,C_105,A_106,E_110] :
      ( k4_relset_1(A_106,B_107,C_105,D_109,E_110,F_108) = k5_relat_1(E_110,F_108)
      | ~ m1_subset_1(F_108,k1_zfmisc_1(k2_zfmisc_1(C_105,D_109)))
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_384,plain,(
    ! [A_119,B_120,A_121,E_122] :
      ( k4_relset_1(A_119,B_120,A_121,A_121,E_122,k6_partfun1(A_121)) = k5_relat_1(E_122,k6_partfun1(A_121))
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(resolution,[status(thm)],[c_31,c_340])).

tff(c_390,plain,(
    ! [A_121] : k4_relset_1('#skF_1','#skF_2',A_121,A_121,'#skF_3',k6_partfun1(A_121)) = k5_relat_1('#skF_3',k6_partfun1(A_121)) ),
    inference(resolution,[status(thm)],[c_30,c_384])).

tff(c_165,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( r2_relset_1(A_60,B_61,C_62,C_62)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_176,plain,(
    ! [C_64] :
      ( r2_relset_1('#skF_1','#skF_2',C_64,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_165])).

tff(c_179,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_176])).

tff(c_76,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_76])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k7_relat_1(B_8,A_7) = B_8
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_87,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_10])).

tff(c_90,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_87])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_relat_1(A_9),B_10) = k7_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_partfun1(A_9),B_10) = k7_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12])).

tff(c_180,plain,(
    ! [F_68,B_67,A_66,C_65,E_70,D_69] :
      ( k4_relset_1(A_66,B_67,C_65,D_69,E_70,F_68) = k5_relat_1(E_70,F_68)
      | ~ m1_subset_1(F_68,k1_zfmisc_1(k2_zfmisc_1(C_65,D_69)))
      | ~ m1_subset_1(E_70,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_192,plain,(
    ! [A_74,B_75,E_76] :
      ( k4_relset_1(A_74,B_75,'#skF_1','#skF_2',E_76,'#skF_3') = k5_relat_1(E_76,'#skF_3')
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(resolution,[status(thm)],[c_30,c_180])).

tff(c_199,plain,(
    ! [A_27] : k4_relset_1(A_27,A_27,'#skF_1','#skF_2',k6_partfun1(A_27),'#skF_3') = k5_relat_1(k6_partfun1(A_27),'#skF_3') ),
    inference(resolution,[status(thm)],[c_31,c_192])).

tff(c_28,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_65,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_205,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_65])).

tff(c_224,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_205])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_179,c_90,c_224])).

tff(c_228,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_391,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_228])).

tff(c_403,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_391])).

tff(c_406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_355,c_328,c_403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.40  
% 2.43/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.41  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.43/1.41  
% 2.43/1.41  %Foreground sorts:
% 2.43/1.41  
% 2.43/1.41  
% 2.43/1.41  %Background operators:
% 2.43/1.41  
% 2.43/1.41  
% 2.43/1.41  %Foreground operators:
% 2.43/1.41  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.43/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.41  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.43/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.43/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.43/1.41  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.43/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.43/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.43/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.41  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.43/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.43/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.43/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.41  
% 2.43/1.42  tff(f_84, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.43/1.42  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.43/1.42  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.43/1.42  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.43/1.42  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.43/1.42  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.43/1.42  tff(f_77, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.43/1.42  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.43/1.42  tff(f_75, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.43/1.42  tff(f_67, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.43/1.42  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.43/1.42  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.43/1.42  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.43/1.42  tff(c_44, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.43/1.42  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_44])).
% 2.43/1.42  tff(c_333, plain, (![A_101, B_102, C_103, D_104]: (r2_relset_1(A_101, B_102, C_103, C_103) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.43/1.42  tff(c_352, plain, (![C_114]: (r2_relset_1('#skF_1', '#skF_2', C_114, C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_30, c_333])).
% 2.43/1.42  tff(c_355, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_352])).
% 2.43/1.42  tff(c_230, plain, (![C_82, B_83, A_84]: (v5_relat_1(C_82, B_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.42  tff(c_238, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_230])).
% 2.43/1.42  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.42  tff(c_311, plain, (![A_97, B_98]: (k8_relat_1(A_97, B_98)=B_98 | ~r1_tarski(k2_relat_1(B_98), A_97) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.43/1.42  tff(c_316, plain, (![A_99, B_100]: (k8_relat_1(A_99, B_100)=B_100 | ~v5_relat_1(B_100, A_99) | ~v1_relat_1(B_100))), inference(resolution, [status(thm)], [c_4, c_311])).
% 2.43/1.42  tff(c_322, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_238, c_316])).
% 2.43/1.42  tff(c_328, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_322])).
% 2.43/1.42  tff(c_26, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.43/1.42  tff(c_6, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=k8_relat_1(A_3, B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.42  tff(c_33, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_partfun1(A_3))=k8_relat_1(A_3, B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6])).
% 2.43/1.42  tff(c_24, plain, (![A_27]: (m1_subset_1(k6_relat_1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.42  tff(c_31, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24])).
% 2.43/1.42  tff(c_340, plain, (![D_109, F_108, B_107, C_105, A_106, E_110]: (k4_relset_1(A_106, B_107, C_105, D_109, E_110, F_108)=k5_relat_1(E_110, F_108) | ~m1_subset_1(F_108, k1_zfmisc_1(k2_zfmisc_1(C_105, D_109))) | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.43/1.42  tff(c_384, plain, (![A_119, B_120, A_121, E_122]: (k4_relset_1(A_119, B_120, A_121, A_121, E_122, k6_partfun1(A_121))=k5_relat_1(E_122, k6_partfun1(A_121)) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(resolution, [status(thm)], [c_31, c_340])).
% 2.43/1.42  tff(c_390, plain, (![A_121]: (k4_relset_1('#skF_1', '#skF_2', A_121, A_121, '#skF_3', k6_partfun1(A_121))=k5_relat_1('#skF_3', k6_partfun1(A_121)))), inference(resolution, [status(thm)], [c_30, c_384])).
% 2.43/1.42  tff(c_165, plain, (![A_60, B_61, C_62, D_63]: (r2_relset_1(A_60, B_61, C_62, C_62) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.43/1.42  tff(c_176, plain, (![C_64]: (r2_relset_1('#skF_1', '#skF_2', C_64, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_30, c_165])).
% 2.43/1.42  tff(c_179, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_176])).
% 2.43/1.42  tff(c_76, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.42  tff(c_84, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_76])).
% 2.43/1.42  tff(c_10, plain, (![B_8, A_7]: (k7_relat_1(B_8, A_7)=B_8 | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.43/1.42  tff(c_87, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_10])).
% 2.43/1.42  tff(c_90, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_87])).
% 2.43/1.42  tff(c_12, plain, (![A_9, B_10]: (k5_relat_1(k6_relat_1(A_9), B_10)=k7_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.43/1.42  tff(c_32, plain, (![A_9, B_10]: (k5_relat_1(k6_partfun1(A_9), B_10)=k7_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12])).
% 2.43/1.42  tff(c_180, plain, (![F_68, B_67, A_66, C_65, E_70, D_69]: (k4_relset_1(A_66, B_67, C_65, D_69, E_70, F_68)=k5_relat_1(E_70, F_68) | ~m1_subset_1(F_68, k1_zfmisc_1(k2_zfmisc_1(C_65, D_69))) | ~m1_subset_1(E_70, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.43/1.42  tff(c_192, plain, (![A_74, B_75, E_76]: (k4_relset_1(A_74, B_75, '#skF_1', '#skF_2', E_76, '#skF_3')=k5_relat_1(E_76, '#skF_3') | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(resolution, [status(thm)], [c_30, c_180])).
% 2.43/1.42  tff(c_199, plain, (![A_27]: (k4_relset_1(A_27, A_27, '#skF_1', '#skF_2', k6_partfun1(A_27), '#skF_3')=k5_relat_1(k6_partfun1(A_27), '#skF_3'))), inference(resolution, [status(thm)], [c_31, c_192])).
% 2.43/1.42  tff(c_28, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.43/1.42  tff(c_65, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 2.43/1.42  tff(c_205, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_65])).
% 2.43/1.42  tff(c_224, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_205])).
% 2.43/1.42  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_179, c_90, c_224])).
% 2.43/1.42  tff(c_228, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.43/1.42  tff(c_391, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_228])).
% 2.43/1.42  tff(c_403, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_33, c_391])).
% 2.43/1.42  tff(c_406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_355, c_328, c_403])).
% 2.43/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.42  
% 2.43/1.42  Inference rules
% 2.43/1.42  ----------------------
% 2.43/1.42  #Ref     : 0
% 2.43/1.42  #Sup     : 83
% 2.43/1.42  #Fact    : 0
% 2.43/1.42  #Define  : 0
% 2.43/1.42  #Split   : 1
% 2.43/1.42  #Chain   : 0
% 2.43/1.42  #Close   : 0
% 2.43/1.42  
% 2.43/1.42  Ordering : KBO
% 2.43/1.42  
% 2.43/1.42  Simplification rules
% 2.43/1.42  ----------------------
% 2.43/1.42  #Subsume      : 0
% 2.43/1.42  #Demod        : 37
% 2.43/1.42  #Tautology    : 41
% 2.43/1.42  #SimpNegUnit  : 0
% 2.43/1.42  #BackRed      : 3
% 2.43/1.42  
% 2.43/1.42  #Partial instantiations: 0
% 2.43/1.42  #Strategies tried      : 1
% 2.43/1.42  
% 2.43/1.42  Timing (in seconds)
% 2.43/1.42  ----------------------
% 2.43/1.43  Preprocessing        : 0.36
% 2.43/1.43  Parsing              : 0.19
% 2.43/1.43  CNF conversion       : 0.02
% 2.43/1.43  Main loop            : 0.24
% 2.43/1.43  Inferencing          : 0.10
% 2.43/1.43  Reduction            : 0.07
% 2.43/1.43  Demodulation         : 0.05
% 2.43/1.43  BG Simplification    : 0.02
% 2.43/1.43  Subsumption          : 0.03
% 2.43/1.43  Abstraction          : 0.02
% 2.43/1.43  MUC search           : 0.00
% 2.43/1.43  Cooper               : 0.00
% 2.43/1.43  Total                : 0.64
% 2.43/1.43  Index Insertion      : 0.00
% 2.43/1.43  Index Deletion       : 0.00
% 2.43/1.43  Index Matching       : 0.00
% 2.43/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
