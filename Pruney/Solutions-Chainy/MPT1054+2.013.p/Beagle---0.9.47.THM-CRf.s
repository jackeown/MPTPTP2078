%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:13 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 193 expanded)
%              Number of leaves         :   46 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 252 expanded)
%              Number of equality atoms :   42 ( 109 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_111,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_101,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_122,plain,(
    ! [A_52,B_53] :
      ( r2_hidden(A_52,B_53)
      | v1_xboole_0(B_53)
      | ~ m1_subset_1(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [A_52,A_1] :
      ( r1_tarski(A_52,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_52,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_130,plain,(
    ! [A_54,A_55] :
      ( r1_tarski(A_54,A_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(A_55)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_126])).

tff(c_138,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_130])).

tff(c_56,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_63,plain,(
    ! [A_26] : v1_relat_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_42])).

tff(c_40,plain,(
    ! [A_25] : v1_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_64,plain,(
    ! [A_25] : v1_funct_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_40])).

tff(c_44,plain,(
    ! [A_26] : v2_funct_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    ! [A_26] : v2_funct_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44])).

tff(c_48,plain,(
    ! [A_29] : k2_funct_1(k6_relat_1(A_29)) = k6_relat_1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_61,plain,(
    ! [A_29] : k2_funct_1(k6_partfun1(A_29)) = k6_partfun1(A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_48])).

tff(c_535,plain,(
    ! [B_100,A_101] :
      ( k9_relat_1(k2_funct_1(B_100),A_101) = k10_relat_1(B_100,A_101)
      | ~ v2_funct_1(B_100)
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_544,plain,(
    ! [A_29,A_101] :
      ( k9_relat_1(k6_partfun1(A_29),A_101) = k10_relat_1(k6_partfun1(A_29),A_101)
      | ~ v2_funct_1(k6_partfun1(A_29))
      | ~ v1_funct_1(k6_partfun1(A_29))
      | ~ v1_relat_1(k6_partfun1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_535])).

tff(c_553,plain,(
    ! [A_102,A_103] : k9_relat_1(k6_partfun1(A_102),A_103) = k10_relat_1(k6_partfun1(A_102),A_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_62,c_544])).

tff(c_28,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_70,plain,(
    ! [A_21] : k2_relat_1(k6_partfun1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_28])).

tff(c_34,plain,(
    ! [A_24] : v4_relat_1(k6_relat_1(A_24),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_67,plain,(
    ! [A_24] : v4_relat_1(k6_partfun1(A_24),A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_34])).

tff(c_149,plain,(
    ! [B_59,A_60] :
      ( k7_relat_1(B_59,A_60) = B_59
      | ~ v4_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_152,plain,(
    ! [A_24] :
      ( k7_relat_1(k6_partfun1(A_24),A_24) = k6_partfun1(A_24)
      | ~ v1_relat_1(k6_partfun1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_67,c_149])).

tff(c_156,plain,(
    ! [A_61] : k7_relat_1(k6_partfun1(A_61),A_61) = k6_partfun1(A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_152])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_162,plain,(
    ! [A_61] :
      ( k9_relat_1(k6_partfun1(A_61),A_61) = k2_relat_1(k6_partfun1(A_61))
      | ~ v1_relat_1(k6_partfun1(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_18])).

tff(c_168,plain,(
    ! [A_61] : k9_relat_1(k6_partfun1(A_61),A_61) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_70,c_162])).

tff(c_560,plain,(
    ! [A_103] : k10_relat_1(k6_partfun1(A_103),A_103) = A_103 ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_168])).

tff(c_26,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_71,plain,(
    ! [A_21] : k1_relat_1(k6_partfun1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_26])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( k5_relat_1(k6_relat_1(A_22),B_23) = B_23
      | ~ r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_185,plain,(
    ! [A_66,B_67] :
      ( k5_relat_1(k6_partfun1(A_66),B_67) = B_67
      | ~ r1_tarski(k1_relat_1(B_67),A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_30])).

tff(c_188,plain,(
    ! [A_66,A_21] :
      ( k5_relat_1(k6_partfun1(A_66),k6_partfun1(A_21)) = k6_partfun1(A_21)
      | ~ r1_tarski(A_21,A_66)
      | ~ v1_relat_1(k6_partfun1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_185])).

tff(c_190,plain,(
    ! [A_66,A_21] :
      ( k5_relat_1(k6_partfun1(A_66),k6_partfun1(A_21)) = k6_partfun1(A_21)
      | ~ r1_tarski(A_21,A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_188])).

tff(c_721,plain,(
    ! [B_122,C_123,A_124] :
      ( k10_relat_1(k5_relat_1(B_122,C_123),A_124) = k10_relat_1(B_122,k10_relat_1(C_123,A_124))
      | ~ v1_relat_1(C_123)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_730,plain,(
    ! [A_66,A_21,A_124] :
      ( k10_relat_1(k6_partfun1(A_66),k10_relat_1(k6_partfun1(A_21),A_124)) = k10_relat_1(k6_partfun1(A_21),A_124)
      | ~ v1_relat_1(k6_partfun1(A_21))
      | ~ v1_relat_1(k6_partfun1(A_66))
      | ~ r1_tarski(A_21,A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_721])).

tff(c_756,plain,(
    ! [A_131,A_132,A_133] :
      ( k10_relat_1(k6_partfun1(A_131),k10_relat_1(k6_partfun1(A_132),A_133)) = k10_relat_1(k6_partfun1(A_132),A_133)
      | ~ r1_tarski(A_132,A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_730])).

tff(c_801,plain,(
    ! [A_131,A_103] :
      ( k10_relat_1(k6_partfun1(A_131),A_103) = k10_relat_1(k6_partfun1(A_103),A_103)
      | ~ r1_tarski(A_103,A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_756])).

tff(c_811,plain,(
    ! [A_134,A_135] :
      ( k10_relat_1(k6_partfun1(A_134),A_135) = A_135
      | ~ r1_tarski(A_135,A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_801])).

tff(c_54,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_735,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( k8_relset_1(A_125,B_126,C_127,D_128) = k10_relat_1(C_127,D_128)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_738,plain,(
    ! [A_34,D_128] : k8_relset_1(A_34,A_34,k6_partfun1(A_34),D_128) = k10_relat_1(k6_partfun1(A_34),D_128) ),
    inference(resolution,[status(thm)],[c_54,c_735])).

tff(c_58,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_739,plain,(
    k10_relat_1(k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_58])).

tff(c_824,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_739])).

tff(c_869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_824])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:21:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.40  
% 2.78/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.40  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.78/1.40  
% 2.78/1.40  %Foreground sorts:
% 2.78/1.40  
% 2.78/1.40  
% 2.78/1.40  %Background operators:
% 2.78/1.40  
% 2.78/1.40  
% 2.78/1.40  %Foreground operators:
% 2.78/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.40  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.78/1.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.78/1.40  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.78/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.78/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.78/1.40  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.78/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.78/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.40  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.78/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.78/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.78/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.40  
% 2.78/1.42  tff(f_116, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 2.78/1.42  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.78/1.42  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.78/1.42  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.78/1.42  tff(f_111, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.78/1.42  tff(f_91, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.78/1.42  tff(f_87, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.78/1.42  tff(f_101, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 2.78/1.42  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 2.78/1.42  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.78/1.42  tff(f_83, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.78/1.42  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.78/1.42  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.78/1.42  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.78/1.42  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 2.78/1.42  tff(f_109, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.78/1.42  tff(f_105, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.78/1.42  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.78/1.42  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.78/1.42  tff(c_122, plain, (![A_52, B_53]: (r2_hidden(A_52, B_53) | v1_xboole_0(B_53) | ~m1_subset_1(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.42  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.78/1.42  tff(c_126, plain, (![A_52, A_1]: (r1_tarski(A_52, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_52, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_122, c_2])).
% 2.78/1.42  tff(c_130, plain, (![A_54, A_55]: (r1_tarski(A_54, A_55) | ~m1_subset_1(A_54, k1_zfmisc_1(A_55)))), inference(negUnitSimplification, [status(thm)], [c_14, c_126])).
% 2.78/1.42  tff(c_138, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_130])).
% 2.78/1.42  tff(c_56, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.78/1.42  tff(c_42, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.78/1.42  tff(c_63, plain, (![A_26]: (v1_relat_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_42])).
% 2.78/1.42  tff(c_40, plain, (![A_25]: (v1_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.78/1.42  tff(c_64, plain, (![A_25]: (v1_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_40])).
% 2.78/1.42  tff(c_44, plain, (![A_26]: (v2_funct_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.78/1.42  tff(c_62, plain, (![A_26]: (v2_funct_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_44])).
% 2.78/1.42  tff(c_48, plain, (![A_29]: (k2_funct_1(k6_relat_1(A_29))=k6_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.78/1.42  tff(c_61, plain, (![A_29]: (k2_funct_1(k6_partfun1(A_29))=k6_partfun1(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_48])).
% 2.78/1.42  tff(c_535, plain, (![B_100, A_101]: (k9_relat_1(k2_funct_1(B_100), A_101)=k10_relat_1(B_100, A_101) | ~v2_funct_1(B_100) | ~v1_funct_1(B_100) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.78/1.42  tff(c_544, plain, (![A_29, A_101]: (k9_relat_1(k6_partfun1(A_29), A_101)=k10_relat_1(k6_partfun1(A_29), A_101) | ~v2_funct_1(k6_partfun1(A_29)) | ~v1_funct_1(k6_partfun1(A_29)) | ~v1_relat_1(k6_partfun1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_535])).
% 2.78/1.42  tff(c_553, plain, (![A_102, A_103]: (k9_relat_1(k6_partfun1(A_102), A_103)=k10_relat_1(k6_partfun1(A_102), A_103))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_62, c_544])).
% 2.78/1.42  tff(c_28, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.42  tff(c_70, plain, (![A_21]: (k2_relat_1(k6_partfun1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_28])).
% 2.78/1.42  tff(c_34, plain, (![A_24]: (v4_relat_1(k6_relat_1(A_24), A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.78/1.42  tff(c_67, plain, (![A_24]: (v4_relat_1(k6_partfun1(A_24), A_24))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_34])).
% 2.78/1.42  tff(c_149, plain, (![B_59, A_60]: (k7_relat_1(B_59, A_60)=B_59 | ~v4_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.78/1.42  tff(c_152, plain, (![A_24]: (k7_relat_1(k6_partfun1(A_24), A_24)=k6_partfun1(A_24) | ~v1_relat_1(k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_67, c_149])).
% 2.78/1.42  tff(c_156, plain, (![A_61]: (k7_relat_1(k6_partfun1(A_61), A_61)=k6_partfun1(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_152])).
% 2.78/1.42  tff(c_18, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.78/1.42  tff(c_162, plain, (![A_61]: (k9_relat_1(k6_partfun1(A_61), A_61)=k2_relat_1(k6_partfun1(A_61)) | ~v1_relat_1(k6_partfun1(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_18])).
% 2.78/1.42  tff(c_168, plain, (![A_61]: (k9_relat_1(k6_partfun1(A_61), A_61)=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_70, c_162])).
% 2.78/1.42  tff(c_560, plain, (![A_103]: (k10_relat_1(k6_partfun1(A_103), A_103)=A_103)), inference(superposition, [status(thm), theory('equality')], [c_553, c_168])).
% 2.78/1.42  tff(c_26, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.42  tff(c_71, plain, (![A_21]: (k1_relat_1(k6_partfun1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_26])).
% 2.78/1.42  tff(c_30, plain, (![A_22, B_23]: (k5_relat_1(k6_relat_1(A_22), B_23)=B_23 | ~r1_tarski(k1_relat_1(B_23), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.78/1.42  tff(c_185, plain, (![A_66, B_67]: (k5_relat_1(k6_partfun1(A_66), B_67)=B_67 | ~r1_tarski(k1_relat_1(B_67), A_66) | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_30])).
% 2.78/1.42  tff(c_188, plain, (![A_66, A_21]: (k5_relat_1(k6_partfun1(A_66), k6_partfun1(A_21))=k6_partfun1(A_21) | ~r1_tarski(A_21, A_66) | ~v1_relat_1(k6_partfun1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_185])).
% 2.78/1.42  tff(c_190, plain, (![A_66, A_21]: (k5_relat_1(k6_partfun1(A_66), k6_partfun1(A_21))=k6_partfun1(A_21) | ~r1_tarski(A_21, A_66))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_188])).
% 2.78/1.42  tff(c_721, plain, (![B_122, C_123, A_124]: (k10_relat_1(k5_relat_1(B_122, C_123), A_124)=k10_relat_1(B_122, k10_relat_1(C_123, A_124)) | ~v1_relat_1(C_123) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.78/1.42  tff(c_730, plain, (![A_66, A_21, A_124]: (k10_relat_1(k6_partfun1(A_66), k10_relat_1(k6_partfun1(A_21), A_124))=k10_relat_1(k6_partfun1(A_21), A_124) | ~v1_relat_1(k6_partfun1(A_21)) | ~v1_relat_1(k6_partfun1(A_66)) | ~r1_tarski(A_21, A_66))), inference(superposition, [status(thm), theory('equality')], [c_190, c_721])).
% 2.78/1.42  tff(c_756, plain, (![A_131, A_132, A_133]: (k10_relat_1(k6_partfun1(A_131), k10_relat_1(k6_partfun1(A_132), A_133))=k10_relat_1(k6_partfun1(A_132), A_133) | ~r1_tarski(A_132, A_131))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_63, c_730])).
% 2.78/1.42  tff(c_801, plain, (![A_131, A_103]: (k10_relat_1(k6_partfun1(A_131), A_103)=k10_relat_1(k6_partfun1(A_103), A_103) | ~r1_tarski(A_103, A_131))), inference(superposition, [status(thm), theory('equality')], [c_560, c_756])).
% 2.78/1.42  tff(c_811, plain, (![A_134, A_135]: (k10_relat_1(k6_partfun1(A_134), A_135)=A_135 | ~r1_tarski(A_135, A_134))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_801])).
% 2.78/1.42  tff(c_54, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.78/1.42  tff(c_735, plain, (![A_125, B_126, C_127, D_128]: (k8_relset_1(A_125, B_126, C_127, D_128)=k10_relat_1(C_127, D_128) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.78/1.42  tff(c_738, plain, (![A_34, D_128]: (k8_relset_1(A_34, A_34, k6_partfun1(A_34), D_128)=k10_relat_1(k6_partfun1(A_34), D_128))), inference(resolution, [status(thm)], [c_54, c_735])).
% 2.78/1.42  tff(c_58, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.78/1.42  tff(c_739, plain, (k10_relat_1(k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_738, c_58])).
% 2.78/1.42  tff(c_824, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_811, c_739])).
% 2.78/1.42  tff(c_869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_824])).
% 2.78/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  Inference rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Ref     : 0
% 2.78/1.42  #Sup     : 174
% 2.78/1.42  #Fact    : 0
% 2.78/1.42  #Define  : 0
% 2.78/1.42  #Split   : 1
% 2.78/1.42  #Chain   : 0
% 2.78/1.42  #Close   : 0
% 2.78/1.42  
% 2.78/1.42  Ordering : KBO
% 2.78/1.42  
% 2.78/1.42  Simplification rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Subsume      : 2
% 2.78/1.42  #Demod        : 50
% 2.78/1.42  #Tautology    : 114
% 2.78/1.42  #SimpNegUnit  : 1
% 2.78/1.42  #BackRed      : 5
% 2.78/1.42  
% 2.78/1.42  #Partial instantiations: 0
% 2.78/1.42  #Strategies tried      : 1
% 2.78/1.42  
% 2.78/1.42  Timing (in seconds)
% 2.78/1.42  ----------------------
% 2.78/1.42  Preprocessing        : 0.32
% 2.78/1.42  Parsing              : 0.18
% 2.78/1.42  CNF conversion       : 0.02
% 2.78/1.42  Main loop            : 0.32
% 2.78/1.42  Inferencing          : 0.12
% 2.78/1.42  Reduction            : 0.09
% 2.78/1.42  Demodulation         : 0.07
% 2.78/1.42  BG Simplification    : 0.02
% 2.78/1.42  Subsumption          : 0.05
% 2.78/1.42  Abstraction          : 0.02
% 2.78/1.42  MUC search           : 0.00
% 2.78/1.42  Cooper               : 0.00
% 2.78/1.42  Total                : 0.67
% 2.78/1.42  Index Insertion      : 0.00
% 2.78/1.42  Index Deletion       : 0.00
% 2.78/1.42  Index Matching       : 0.00
% 2.78/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
