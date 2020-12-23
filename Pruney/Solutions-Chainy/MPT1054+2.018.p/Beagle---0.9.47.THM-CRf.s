%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:14 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 195 expanded)
%              Number of leaves         :   45 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 254 expanded)
%              Number of equality atoms :   42 ( 111 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_114,negated_conjecture,(
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

tff(f_109,axiom,(
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

tff(f_107,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | v1_xboole_0(B_52)
      | ~ m1_subset_1(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,(
    ! [A_51,A_1] :
      ( r1_tarski(A_51,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_51,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_128,plain,(
    ! [A_53,A_54] :
      ( r1_tarski(A_53,A_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(A_54)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_124])).

tff(c_136,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_128])).

tff(c_54,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    ! [A_26] : v1_relat_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42])).

tff(c_40,plain,(
    ! [A_25] : v1_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_63,plain,(
    ! [A_25] : v1_funct_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40])).

tff(c_44,plain,(
    ! [A_26] : v2_funct_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_61,plain,(
    ! [A_26] : v2_funct_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44])).

tff(c_48,plain,(
    ! [A_29] : k2_funct_1(k6_relat_1(A_29)) = k6_relat_1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_60,plain,(
    ! [A_29] : k2_funct_1(k6_partfun1(A_29)) = k6_partfun1(A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_48])).

tff(c_534,plain,(
    ! [B_101,A_102] :
      ( k9_relat_1(k2_funct_1(B_101),A_102) = k10_relat_1(B_101,A_102)
      | ~ v2_funct_1(B_101)
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_543,plain,(
    ! [A_29,A_102] :
      ( k9_relat_1(k6_partfun1(A_29),A_102) = k10_relat_1(k6_partfun1(A_29),A_102)
      | ~ v2_funct_1(k6_partfun1(A_29))
      | ~ v1_funct_1(k6_partfun1(A_29))
      | ~ v1_relat_1(k6_partfun1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_534])).

tff(c_552,plain,(
    ! [A_103,A_104] : k9_relat_1(k6_partfun1(A_103),A_104) = k10_relat_1(k6_partfun1(A_103),A_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_63,c_61,c_543])).

tff(c_28,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_69,plain,(
    ! [A_21] : k2_relat_1(k6_partfun1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_28])).

tff(c_34,plain,(
    ! [A_24] : v4_relat_1(k6_relat_1(A_24),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_66,plain,(
    ! [A_24] : v4_relat_1(k6_partfun1(A_24),A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_34])).

tff(c_147,plain,(
    ! [B_58,A_59] :
      ( k7_relat_1(B_58,A_59) = B_58
      | ~ v4_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_150,plain,(
    ! [A_24] :
      ( k7_relat_1(k6_partfun1(A_24),A_24) = k6_partfun1(A_24)
      | ~ v1_relat_1(k6_partfun1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_66,c_147])).

tff(c_154,plain,(
    ! [A_60] : k7_relat_1(k6_partfun1(A_60),A_60) = k6_partfun1(A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_150])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_160,plain,(
    ! [A_60] :
      ( k9_relat_1(k6_partfun1(A_60),A_60) = k2_relat_1(k6_partfun1(A_60))
      | ~ v1_relat_1(k6_partfun1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_18])).

tff(c_166,plain,(
    ! [A_60] : k9_relat_1(k6_partfun1(A_60),A_60) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_69,c_160])).

tff(c_559,plain,(
    ! [A_104] : k10_relat_1(k6_partfun1(A_104),A_104) = A_104 ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_166])).

tff(c_26,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_70,plain,(
    ! [A_21] : k1_relat_1(k6_partfun1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_26])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( k5_relat_1(k6_relat_1(A_22),B_23) = B_23
      | ~ r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_195,plain,(
    ! [A_67,B_68] :
      ( k5_relat_1(k6_partfun1(A_67),B_68) = B_68
      | ~ r1_tarski(k1_relat_1(B_68),A_67)
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_30])).

tff(c_198,plain,(
    ! [A_67,A_21] :
      ( k5_relat_1(k6_partfun1(A_67),k6_partfun1(A_21)) = k6_partfun1(A_21)
      | ~ r1_tarski(A_21,A_67)
      | ~ v1_relat_1(k6_partfun1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_195])).

tff(c_200,plain,(
    ! [A_67,A_21] :
      ( k5_relat_1(k6_partfun1(A_67),k6_partfun1(A_21)) = k6_partfun1(A_21)
      | ~ r1_tarski(A_21,A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_198])).

tff(c_652,plain,(
    ! [B_118,C_119,A_120] :
      ( k10_relat_1(k5_relat_1(B_118,C_119),A_120) = k10_relat_1(B_118,k10_relat_1(C_119,A_120))
      | ~ v1_relat_1(C_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_661,plain,(
    ! [A_67,A_21,A_120] :
      ( k10_relat_1(k6_partfun1(A_67),k10_relat_1(k6_partfun1(A_21),A_120)) = k10_relat_1(k6_partfun1(A_21),A_120)
      | ~ v1_relat_1(k6_partfun1(A_21))
      | ~ v1_relat_1(k6_partfun1(A_67))
      | ~ r1_tarski(A_21,A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_652])).

tff(c_754,plain,(
    ! [A_130,A_131,A_132] :
      ( k10_relat_1(k6_partfun1(A_130),k10_relat_1(k6_partfun1(A_131),A_132)) = k10_relat_1(k6_partfun1(A_131),A_132)
      | ~ r1_tarski(A_131,A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_661])).

tff(c_799,plain,(
    ! [A_130,A_104] :
      ( k10_relat_1(k6_partfun1(A_130),A_104) = k10_relat_1(k6_partfun1(A_104),A_104)
      | ~ r1_tarski(A_104,A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_754])).

tff(c_809,plain,(
    ! [A_133,A_134] :
      ( k10_relat_1(k6_partfun1(A_133),A_134) = A_134
      | ~ r1_tarski(A_134,A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_799])).

tff(c_52,plain,(
    ! [A_34] : m1_subset_1(k6_relat_1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_59,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52])).

tff(c_568,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k8_relset_1(A_105,B_106,C_107,D_108) = k10_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_571,plain,(
    ! [A_34,D_108] : k8_relset_1(A_34,A_34,k6_partfun1(A_34),D_108) = k10_relat_1(k6_partfun1(A_34),D_108) ),
    inference(resolution,[status(thm)],[c_59,c_568])).

tff(c_56,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_638,plain,(
    k10_relat_1(k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_56])).

tff(c_829,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_638])).

tff(c_867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_829])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:22:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.56  
% 2.69/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.56  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.13/1.56  
% 3.13/1.56  %Foreground sorts:
% 3.13/1.56  
% 3.13/1.56  
% 3.13/1.56  %Background operators:
% 3.13/1.56  
% 3.13/1.56  
% 3.13/1.56  %Foreground operators:
% 3.13/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.13/1.56  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.13/1.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.13/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.13/1.56  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.13/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.13/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.13/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.13/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.56  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.13/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.56  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.13/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.13/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.13/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.13/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.56  
% 3.13/1.58  tff(f_114, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 3.13/1.58  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.13/1.58  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.13/1.58  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.13/1.58  tff(f_109, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.13/1.58  tff(f_91, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.13/1.58  tff(f_87, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.13/1.58  tff(f_101, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 3.13/1.58  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 3.13/1.58  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.13/1.58  tff(f_83, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 3.13/1.58  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.13/1.58  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.13/1.58  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 3.13/1.58  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 3.13/1.58  tff(f_107, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.13/1.58  tff(f_105, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.13/1.58  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.13/1.58  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.58  tff(c_120, plain, (![A_51, B_52]: (r2_hidden(A_51, B_52) | v1_xboole_0(B_52) | ~m1_subset_1(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.13/1.58  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.13/1.58  tff(c_124, plain, (![A_51, A_1]: (r1_tarski(A_51, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_51, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_120, c_2])).
% 3.13/1.58  tff(c_128, plain, (![A_53, A_54]: (r1_tarski(A_53, A_54) | ~m1_subset_1(A_53, k1_zfmisc_1(A_54)))), inference(negUnitSimplification, [status(thm)], [c_14, c_124])).
% 3.13/1.58  tff(c_136, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_128])).
% 3.13/1.58  tff(c_54, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.13/1.58  tff(c_42, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.13/1.58  tff(c_62, plain, (![A_26]: (v1_relat_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42])).
% 3.13/1.58  tff(c_40, plain, (![A_25]: (v1_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.13/1.58  tff(c_63, plain, (![A_25]: (v1_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40])).
% 3.13/1.58  tff(c_44, plain, (![A_26]: (v2_funct_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.13/1.58  tff(c_61, plain, (![A_26]: (v2_funct_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_44])).
% 3.13/1.58  tff(c_48, plain, (![A_29]: (k2_funct_1(k6_relat_1(A_29))=k6_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.13/1.58  tff(c_60, plain, (![A_29]: (k2_funct_1(k6_partfun1(A_29))=k6_partfun1(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_48])).
% 3.13/1.58  tff(c_534, plain, (![B_101, A_102]: (k9_relat_1(k2_funct_1(B_101), A_102)=k10_relat_1(B_101, A_102) | ~v2_funct_1(B_101) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.13/1.58  tff(c_543, plain, (![A_29, A_102]: (k9_relat_1(k6_partfun1(A_29), A_102)=k10_relat_1(k6_partfun1(A_29), A_102) | ~v2_funct_1(k6_partfun1(A_29)) | ~v1_funct_1(k6_partfun1(A_29)) | ~v1_relat_1(k6_partfun1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_534])).
% 3.13/1.58  tff(c_552, plain, (![A_103, A_104]: (k9_relat_1(k6_partfun1(A_103), A_104)=k10_relat_1(k6_partfun1(A_103), A_104))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_63, c_61, c_543])).
% 3.13/1.58  tff(c_28, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.13/1.58  tff(c_69, plain, (![A_21]: (k2_relat_1(k6_partfun1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_28])).
% 3.13/1.58  tff(c_34, plain, (![A_24]: (v4_relat_1(k6_relat_1(A_24), A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.13/1.58  tff(c_66, plain, (![A_24]: (v4_relat_1(k6_partfun1(A_24), A_24))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_34])).
% 3.13/1.58  tff(c_147, plain, (![B_58, A_59]: (k7_relat_1(B_58, A_59)=B_58 | ~v4_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.13/1.58  tff(c_150, plain, (![A_24]: (k7_relat_1(k6_partfun1(A_24), A_24)=k6_partfun1(A_24) | ~v1_relat_1(k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_66, c_147])).
% 3.13/1.58  tff(c_154, plain, (![A_60]: (k7_relat_1(k6_partfun1(A_60), A_60)=k6_partfun1(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_150])).
% 3.13/1.58  tff(c_18, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.13/1.58  tff(c_160, plain, (![A_60]: (k9_relat_1(k6_partfun1(A_60), A_60)=k2_relat_1(k6_partfun1(A_60)) | ~v1_relat_1(k6_partfun1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_154, c_18])).
% 3.13/1.58  tff(c_166, plain, (![A_60]: (k9_relat_1(k6_partfun1(A_60), A_60)=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_69, c_160])).
% 3.13/1.58  tff(c_559, plain, (![A_104]: (k10_relat_1(k6_partfun1(A_104), A_104)=A_104)), inference(superposition, [status(thm), theory('equality')], [c_552, c_166])).
% 3.13/1.58  tff(c_26, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.13/1.58  tff(c_70, plain, (![A_21]: (k1_relat_1(k6_partfun1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_26])).
% 3.13/1.58  tff(c_30, plain, (![A_22, B_23]: (k5_relat_1(k6_relat_1(A_22), B_23)=B_23 | ~r1_tarski(k1_relat_1(B_23), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.13/1.58  tff(c_195, plain, (![A_67, B_68]: (k5_relat_1(k6_partfun1(A_67), B_68)=B_68 | ~r1_tarski(k1_relat_1(B_68), A_67) | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_30])).
% 3.13/1.58  tff(c_198, plain, (![A_67, A_21]: (k5_relat_1(k6_partfun1(A_67), k6_partfun1(A_21))=k6_partfun1(A_21) | ~r1_tarski(A_21, A_67) | ~v1_relat_1(k6_partfun1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_195])).
% 3.13/1.58  tff(c_200, plain, (![A_67, A_21]: (k5_relat_1(k6_partfun1(A_67), k6_partfun1(A_21))=k6_partfun1(A_21) | ~r1_tarski(A_21, A_67))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_198])).
% 3.13/1.58  tff(c_652, plain, (![B_118, C_119, A_120]: (k10_relat_1(k5_relat_1(B_118, C_119), A_120)=k10_relat_1(B_118, k10_relat_1(C_119, A_120)) | ~v1_relat_1(C_119) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.13/1.58  tff(c_661, plain, (![A_67, A_21, A_120]: (k10_relat_1(k6_partfun1(A_67), k10_relat_1(k6_partfun1(A_21), A_120))=k10_relat_1(k6_partfun1(A_21), A_120) | ~v1_relat_1(k6_partfun1(A_21)) | ~v1_relat_1(k6_partfun1(A_67)) | ~r1_tarski(A_21, A_67))), inference(superposition, [status(thm), theory('equality')], [c_200, c_652])).
% 3.13/1.58  tff(c_754, plain, (![A_130, A_131, A_132]: (k10_relat_1(k6_partfun1(A_130), k10_relat_1(k6_partfun1(A_131), A_132))=k10_relat_1(k6_partfun1(A_131), A_132) | ~r1_tarski(A_131, A_130))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_661])).
% 3.13/1.58  tff(c_799, plain, (![A_130, A_104]: (k10_relat_1(k6_partfun1(A_130), A_104)=k10_relat_1(k6_partfun1(A_104), A_104) | ~r1_tarski(A_104, A_130))), inference(superposition, [status(thm), theory('equality')], [c_559, c_754])).
% 3.13/1.58  tff(c_809, plain, (![A_133, A_134]: (k10_relat_1(k6_partfun1(A_133), A_134)=A_134 | ~r1_tarski(A_134, A_133))), inference(demodulation, [status(thm), theory('equality')], [c_559, c_799])).
% 3.13/1.58  tff(c_52, plain, (![A_34]: (m1_subset_1(k6_relat_1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.13/1.58  tff(c_59, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52])).
% 3.13/1.58  tff(c_568, plain, (![A_105, B_106, C_107, D_108]: (k8_relset_1(A_105, B_106, C_107, D_108)=k10_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.13/1.58  tff(c_571, plain, (![A_34, D_108]: (k8_relset_1(A_34, A_34, k6_partfun1(A_34), D_108)=k10_relat_1(k6_partfun1(A_34), D_108))), inference(resolution, [status(thm)], [c_59, c_568])).
% 3.13/1.58  tff(c_56, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.13/1.58  tff(c_638, plain, (k10_relat_1(k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_571, c_56])).
% 3.13/1.58  tff(c_829, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_809, c_638])).
% 3.13/1.58  tff(c_867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_829])).
% 3.13/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.58  
% 3.13/1.58  Inference rules
% 3.13/1.58  ----------------------
% 3.13/1.58  #Ref     : 0
% 3.13/1.58  #Sup     : 174
% 3.13/1.58  #Fact    : 0
% 3.13/1.58  #Define  : 0
% 3.13/1.58  #Split   : 1
% 3.13/1.58  #Chain   : 0
% 3.13/1.58  #Close   : 0
% 3.13/1.58  
% 3.13/1.58  Ordering : KBO
% 3.13/1.58  
% 3.13/1.58  Simplification rules
% 3.13/1.58  ----------------------
% 3.13/1.58  #Subsume      : 2
% 3.13/1.58  #Demod        : 51
% 3.13/1.58  #Tautology    : 114
% 3.13/1.58  #SimpNegUnit  : 1
% 3.13/1.58  #BackRed      : 5
% 3.13/1.58  
% 3.13/1.58  #Partial instantiations: 0
% 3.13/1.58  #Strategies tried      : 1
% 3.13/1.58  
% 3.13/1.58  Timing (in seconds)
% 3.13/1.58  ----------------------
% 3.13/1.58  Preprocessing        : 0.41
% 3.13/1.58  Parsing              : 0.23
% 3.13/1.58  CNF conversion       : 0.03
% 3.13/1.58  Main loop            : 0.34
% 3.13/1.58  Inferencing          : 0.13
% 3.13/1.58  Reduction            : 0.10
% 3.13/1.58  Demodulation         : 0.07
% 3.13/1.58  BG Simplification    : 0.02
% 3.13/1.58  Subsumption          : 0.05
% 3.13/1.58  Abstraction          : 0.02
% 3.13/1.58  MUC search           : 0.00
% 3.13/1.58  Cooper               : 0.00
% 3.13/1.58  Total                : 0.79
% 3.13/1.58  Index Insertion      : 0.00
% 3.13/1.58  Index Deletion       : 0.00
% 3.13/1.58  Index Matching       : 0.00
% 3.13/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
