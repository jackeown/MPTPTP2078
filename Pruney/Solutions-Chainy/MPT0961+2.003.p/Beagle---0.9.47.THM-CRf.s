%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:41 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 384 expanded)
%              Number of leaves         :   26 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :  154 (1093 expanded)
%              Number of equality atoms :   36 ( 254 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_434,plain,(
    ! [C_126,A_127,B_128] :
      ( m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ r1_tarski(k2_relat_1(C_126),B_128)
      | ~ r1_tarski(k1_relat_1(C_126),A_127)
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_125,plain,(
    ! [C_54,A_55,B_56] :
      ( m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ r1_tarski(k2_relat_1(C_54),B_56)
      | ~ r1_tarski(k1_relat_1(C_54),A_55)
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_5,B_6,C_7] :
      ( k1_relset_1(A_5,B_6,C_7) = k1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_186,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ r1_tarski(k2_relat_1(C_76),B_75)
      | ~ r1_tarski(k1_relat_1(C_76),A_74)
      | ~ v1_relat_1(C_76) ) ),
    inference(resolution,[status(thm)],[c_125,c_16])).

tff(c_191,plain,(
    ! [A_77,C_78] :
      ( k1_relset_1(A_77,k2_relat_1(C_78),C_78) = k1_relat_1(C_78)
      | ~ r1_tarski(k1_relat_1(C_78),A_77)
      | ~ v1_relat_1(C_78) ) ),
    inference(resolution,[status(thm)],[c_8,c_186])).

tff(c_195,plain,(
    ! [C_78] :
      ( k1_relset_1(k1_relat_1(C_78),k2_relat_1(C_78),C_78) = k1_relat_1(C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(resolution,[status(thm)],[c_8,c_191])).

tff(c_18,plain,(
    ! [C_10,A_8,B_9] :
      ( m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ r1_tarski(k2_relat_1(C_10),B_9)
      | ~ r1_tarski(k1_relat_1(C_10),A_8)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_144,plain,(
    ! [B_57,C_58,A_59] :
      ( k1_xboole_0 = B_57
      | v1_funct_2(C_58,A_59,B_57)
      | k1_relset_1(A_59,B_57,C_58) != A_59
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_227,plain,(
    ! [B_85,C_86,A_87] :
      ( k1_xboole_0 = B_85
      | v1_funct_2(C_86,A_87,B_85)
      | k1_relset_1(A_87,B_85,C_86) != A_87
      | ~ r1_tarski(k2_relat_1(C_86),B_85)
      | ~ r1_tarski(k1_relat_1(C_86),A_87)
      | ~ v1_relat_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_18,c_144])).

tff(c_232,plain,(
    ! [C_88,A_89] :
      ( k2_relat_1(C_88) = k1_xboole_0
      | v1_funct_2(C_88,A_89,k2_relat_1(C_88))
      | k1_relset_1(A_89,k2_relat_1(C_88),C_88) != A_89
      | ~ r1_tarski(k1_relat_1(C_88),A_89)
      | ~ v1_relat_1(C_88) ) ),
    inference(resolution,[status(thm)],[c_8,c_227])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_92,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_238,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_232,c_92])).

tff(c_242,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8,c_238])).

tff(c_243,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_246,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_243])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_246])).

tff(c_251,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_12,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_137,plain,(
    ! [C_54,A_3] :
      ( m1_subset_1(C_54,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_54),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_54),A_3)
      | ~ v1_relat_1(C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_125])).

tff(c_271,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_3)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_137])).

tff(c_287,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8,c_271])).

tff(c_306,plain,(
    ! [A_93] : ~ r1_tarski(k1_relat_1('#skF_1'),A_93) ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_311,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_306])).

tff(c_312,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_partfun1(C_28,A_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_99,plain,(
    ! [C_28] :
      ( v1_partfun1(C_28,k1_xboole_0)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_93])).

tff(c_101,plain,(
    ! [C_28] :
      ( v1_partfun1(C_28,k1_xboole_0)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_99])).

tff(c_338,plain,(
    v1_partfun1('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_312,c_101])).

tff(c_114,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_funct_2(C_43,A_44,B_45)
      | ~ v1_partfun1(C_43,A_44)
      | ~ v1_funct_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_120,plain,(
    ! [C_43,B_4] :
      ( v1_funct_2(C_43,k1_xboole_0,B_4)
      | ~ v1_partfun1(C_43,k1_xboole_0)
      | ~ v1_funct_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_114])).

tff(c_316,plain,(
    ! [B_4] :
      ( v1_funct_2('#skF_1',k1_xboole_0,B_4)
      | ~ v1_partfun1('#skF_1',k1_xboole_0)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_312,c_120])).

tff(c_333,plain,(
    ! [B_4] :
      ( v1_funct_2('#skF_1',k1_xboole_0,B_4)
      | ~ v1_partfun1('#skF_1',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_316])).

tff(c_373,plain,(
    ! [B_4] : v1_funct_2('#skF_1',k1_xboole_0,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_333])).

tff(c_104,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_relset_1(A_34,B_35,C_36) = k1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_110,plain,(
    ! [B_4,C_36] :
      ( k1_relset_1(k1_xboole_0,B_4,C_36) = k1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_104])).

tff(c_335,plain,(
    ! [B_4] : k1_relset_1(k1_xboole_0,B_4,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_312,c_110])).

tff(c_374,plain,(
    ! [B_99] : v1_funct_2('#skF_1',k1_xboole_0,B_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_333])).

tff(c_34,plain,(
    ! [B_19,C_20] :
      ( k1_relset_1(k1_xboole_0,B_19,C_20) = k1_xboole_0
      | ~ v1_funct_2(C_20,k1_xboole_0,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    ! [B_19,C_20] :
      ( k1_relset_1(k1_xboole_0,B_19,C_20) = k1_xboole_0
      | ~ v1_funct_2(C_20,k1_xboole_0,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_34])).

tff(c_378,plain,(
    ! [B_99] :
      ( k1_relset_1(k1_xboole_0,B_99,'#skF_1') = k1_xboole_0
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_374,c_46])).

tff(c_387,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_335,c_378])).

tff(c_253,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_92])).

tff(c_394,plain,(
    ~ v1_funct_2('#skF_1',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_253])).

tff(c_399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_394])).

tff(c_400,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_446,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_434,c_400])).

tff(c_459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8,c_8,c_446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n015.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:38:08 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.30  
% 2.29/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.30  %$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.29/1.30  
% 2.29/1.30  %Foreground sorts:
% 2.29/1.30  
% 2.29/1.30  
% 2.29/1.30  %Background operators:
% 2.29/1.30  
% 2.29/1.30  
% 2.29/1.30  %Foreground operators:
% 2.29/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.29/1.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.29/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.29/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.30  
% 2.29/1.32  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.29/1.32  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.29/1.32  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.29/1.32  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.29/1.32  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.29/1.32  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.29/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.29/1.32  tff(f_67, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.29/1.32  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 2.29/1.32  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.29/1.32  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.32  tff(c_434, plain, (![C_126, A_127, B_128]: (m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~r1_tarski(k2_relat_1(C_126), B_128) | ~r1_tarski(k1_relat_1(C_126), A_127) | ~v1_relat_1(C_126))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.29/1.32  tff(c_125, plain, (![C_54, A_55, B_56]: (m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~r1_tarski(k2_relat_1(C_54), B_56) | ~r1_tarski(k1_relat_1(C_54), A_55) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.29/1.32  tff(c_16, plain, (![A_5, B_6, C_7]: (k1_relset_1(A_5, B_6, C_7)=k1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.29/1.32  tff(c_186, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~r1_tarski(k2_relat_1(C_76), B_75) | ~r1_tarski(k1_relat_1(C_76), A_74) | ~v1_relat_1(C_76))), inference(resolution, [status(thm)], [c_125, c_16])).
% 2.29/1.32  tff(c_191, plain, (![A_77, C_78]: (k1_relset_1(A_77, k2_relat_1(C_78), C_78)=k1_relat_1(C_78) | ~r1_tarski(k1_relat_1(C_78), A_77) | ~v1_relat_1(C_78))), inference(resolution, [status(thm)], [c_8, c_186])).
% 2.29/1.32  tff(c_195, plain, (![C_78]: (k1_relset_1(k1_relat_1(C_78), k2_relat_1(C_78), C_78)=k1_relat_1(C_78) | ~v1_relat_1(C_78))), inference(resolution, [status(thm)], [c_8, c_191])).
% 2.29/1.32  tff(c_18, plain, (![C_10, A_8, B_9]: (m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~r1_tarski(k2_relat_1(C_10), B_9) | ~r1_tarski(k1_relat_1(C_10), A_8) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.29/1.32  tff(c_144, plain, (![B_57, C_58, A_59]: (k1_xboole_0=B_57 | v1_funct_2(C_58, A_59, B_57) | k1_relset_1(A_59, B_57, C_58)!=A_59 | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_57))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.29/1.32  tff(c_227, plain, (![B_85, C_86, A_87]: (k1_xboole_0=B_85 | v1_funct_2(C_86, A_87, B_85) | k1_relset_1(A_87, B_85, C_86)!=A_87 | ~r1_tarski(k2_relat_1(C_86), B_85) | ~r1_tarski(k1_relat_1(C_86), A_87) | ~v1_relat_1(C_86))), inference(resolution, [status(thm)], [c_18, c_144])).
% 2.29/1.32  tff(c_232, plain, (![C_88, A_89]: (k2_relat_1(C_88)=k1_xboole_0 | v1_funct_2(C_88, A_89, k2_relat_1(C_88)) | k1_relset_1(A_89, k2_relat_1(C_88), C_88)!=A_89 | ~r1_tarski(k1_relat_1(C_88), A_89) | ~v1_relat_1(C_88))), inference(resolution, [status(thm)], [c_8, c_227])).
% 2.29/1.32  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.29/1.32  tff(c_38, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.29/1.32  tff(c_44, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 2.29/1.32  tff(c_92, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.29/1.32  tff(c_238, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_232, c_92])).
% 2.29/1.32  tff(c_242, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8, c_238])).
% 2.29/1.32  tff(c_243, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_242])).
% 2.29/1.32  tff(c_246, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_195, c_243])).
% 2.29/1.32  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_246])).
% 2.29/1.32  tff(c_251, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_242])).
% 2.29/1.32  tff(c_12, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.29/1.32  tff(c_137, plain, (![C_54, A_3]: (m1_subset_1(C_54, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_54), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_54), A_3) | ~v1_relat_1(C_54))), inference(superposition, [status(thm), theory('equality')], [c_12, c_125])).
% 2.29/1.32  tff(c_271, plain, (![A_3]: (m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_1'), A_3) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_251, c_137])).
% 2.29/1.32  tff(c_287, plain, (![A_3]: (m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_1'), A_3))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8, c_271])).
% 2.29/1.32  tff(c_306, plain, (![A_93]: (~r1_tarski(k1_relat_1('#skF_1'), A_93))), inference(splitLeft, [status(thm)], [c_287])).
% 2.29/1.32  tff(c_311, plain, $false, inference(resolution, [status(thm)], [c_8, c_306])).
% 2.29/1.32  tff(c_312, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_287])).
% 2.29/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.29/1.32  tff(c_14, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.29/1.32  tff(c_93, plain, (![C_28, A_29, B_30]: (v1_partfun1(C_28, A_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.29/1.32  tff(c_99, plain, (![C_28]: (v1_partfun1(C_28, k1_xboole_0) | ~m1_subset_1(C_28, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_93])).
% 2.29/1.32  tff(c_101, plain, (![C_28]: (v1_partfun1(C_28, k1_xboole_0) | ~m1_subset_1(C_28, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_99])).
% 2.29/1.32  tff(c_338, plain, (v1_partfun1('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_312, c_101])).
% 2.29/1.32  tff(c_114, plain, (![C_43, A_44, B_45]: (v1_funct_2(C_43, A_44, B_45) | ~v1_partfun1(C_43, A_44) | ~v1_funct_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.29/1.32  tff(c_120, plain, (![C_43, B_4]: (v1_funct_2(C_43, k1_xboole_0, B_4) | ~v1_partfun1(C_43, k1_xboole_0) | ~v1_funct_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_114])).
% 2.29/1.32  tff(c_316, plain, (![B_4]: (v1_funct_2('#skF_1', k1_xboole_0, B_4) | ~v1_partfun1('#skF_1', k1_xboole_0) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_312, c_120])).
% 2.29/1.32  tff(c_333, plain, (![B_4]: (v1_funct_2('#skF_1', k1_xboole_0, B_4) | ~v1_partfun1('#skF_1', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_316])).
% 2.29/1.32  tff(c_373, plain, (![B_4]: (v1_funct_2('#skF_1', k1_xboole_0, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_333])).
% 2.29/1.32  tff(c_104, plain, (![A_34, B_35, C_36]: (k1_relset_1(A_34, B_35, C_36)=k1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.29/1.32  tff(c_110, plain, (![B_4, C_36]: (k1_relset_1(k1_xboole_0, B_4, C_36)=k1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_104])).
% 2.29/1.32  tff(c_335, plain, (![B_4]: (k1_relset_1(k1_xboole_0, B_4, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_312, c_110])).
% 2.29/1.32  tff(c_374, plain, (![B_99]: (v1_funct_2('#skF_1', k1_xboole_0, B_99))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_333])).
% 2.29/1.32  tff(c_34, plain, (![B_19, C_20]: (k1_relset_1(k1_xboole_0, B_19, C_20)=k1_xboole_0 | ~v1_funct_2(C_20, k1_xboole_0, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.29/1.32  tff(c_46, plain, (![B_19, C_20]: (k1_relset_1(k1_xboole_0, B_19, C_20)=k1_xboole_0 | ~v1_funct_2(C_20, k1_xboole_0, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_34])).
% 2.29/1.32  tff(c_378, plain, (![B_99]: (k1_relset_1(k1_xboole_0, B_99, '#skF_1')=k1_xboole_0 | ~m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_374, c_46])).
% 2.29/1.32  tff(c_387, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_312, c_335, c_378])).
% 2.29/1.32  tff(c_253, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_251, c_92])).
% 2.29/1.32  tff(c_394, plain, (~v1_funct_2('#skF_1', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_387, c_253])).
% 2.29/1.32  tff(c_399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_373, c_394])).
% 2.29/1.32  tff(c_400, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_44])).
% 2.29/1.32  tff(c_446, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_434, c_400])).
% 2.29/1.32  tff(c_459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_8, c_8, c_446])).
% 2.29/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.32  
% 2.29/1.32  Inference rules
% 2.29/1.32  ----------------------
% 2.29/1.32  #Ref     : 0
% 2.29/1.32  #Sup     : 85
% 2.29/1.32  #Fact    : 0
% 2.29/1.32  #Define  : 0
% 2.29/1.32  #Split   : 4
% 2.29/1.32  #Chain   : 0
% 2.29/1.32  #Close   : 0
% 2.29/1.32  
% 2.29/1.32  Ordering : KBO
% 2.29/1.32  
% 2.29/1.32  Simplification rules
% 2.29/1.32  ----------------------
% 2.29/1.32  #Subsume      : 6
% 2.29/1.32  #Demod        : 52
% 2.29/1.32  #Tautology    : 31
% 2.29/1.32  #SimpNegUnit  : 0
% 2.29/1.32  #BackRed      : 6
% 2.29/1.32  
% 2.29/1.32  #Partial instantiations: 0
% 2.29/1.32  #Strategies tried      : 1
% 2.29/1.32  
% 2.29/1.32  Timing (in seconds)
% 2.29/1.32  ----------------------
% 2.29/1.32  Preprocessing        : 0.31
% 2.29/1.32  Parsing              : 0.16
% 2.29/1.32  CNF conversion       : 0.02
% 2.29/1.32  Main loop            : 0.27
% 2.29/1.32  Inferencing          : 0.10
% 2.29/1.32  Reduction            : 0.08
% 2.29/1.32  Demodulation         : 0.05
% 2.29/1.32  BG Simplification    : 0.02
% 2.29/1.32  Subsumption          : 0.06
% 2.29/1.32  Abstraction          : 0.01
% 2.29/1.32  MUC search           : 0.00
% 2.29/1.32  Cooper               : 0.00
% 2.29/1.32  Total                : 0.61
% 2.29/1.32  Index Insertion      : 0.00
% 2.29/1.32  Index Deletion       : 0.00
% 2.29/1.33  Index Matching       : 0.00
% 2.29/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
