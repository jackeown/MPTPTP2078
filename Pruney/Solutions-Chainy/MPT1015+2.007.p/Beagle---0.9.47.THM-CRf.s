%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:38 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 320 expanded)
%              Number of leaves         :   35 ( 132 expanded)
%              Depth                    :   10
%              Number of atoms          :  179 (1136 expanded)
%              Number of equality atoms :   44 ( 134 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(f_126,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,C,B),B)
                & v2_funct_1(B) )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_86,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( ( k1_relat_1(B) = A
              & k1_relat_1(C) = A
              & r1_tarski(k2_relat_1(C),A)
              & v2_funct_1(B)
              & k5_relat_1(C,B) = B )
           => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_90,plain,(
    ! [A_50,B_51,D_52] :
      ( r2_relset_1(A_50,B_51,D_52,D_52)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_96,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_90])).

tff(c_57,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_65,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_57])).

tff(c_66,plain,(
    ! [C_40,B_41,A_42] :
      ( v5_relat_1(C_40,B_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_42,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_74,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_64,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_57])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_106,plain,(
    ! [A_56,B_57] :
      ( k1_relset_1(A_56,A_56,B_57) = A_56
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_zfmisc_1(A_56,A_56)))
      | ~ v1_funct_2(B_57,A_56,A_56)
      | ~ v1_funct_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_109,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_106])).

tff(c_115,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_109])).

tff(c_97,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_104,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_97])).

tff(c_127,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_104])).

tff(c_38,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_112,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_106])).

tff(c_118,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_112])).

tff(c_105,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_97])).

tff(c_132,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_105])).

tff(c_32,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_180,plain,(
    ! [F_74,C_75,E_76,B_72,A_73,D_71] :
      ( k1_partfun1(A_73,B_72,C_75,D_71,E_76,F_74) = k5_relat_1(E_76,F_74)
      | ~ m1_subset_1(F_74,k1_zfmisc_1(k2_zfmisc_1(C_75,D_71)))
      | ~ v1_funct_1(F_74)
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72)))
      | ~ v1_funct_1(E_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_182,plain,(
    ! [A_73,B_72,E_76] :
      ( k1_partfun1(A_73,B_72,'#skF_1','#skF_1',E_76,'#skF_2') = k5_relat_1(E_76,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72)))
      | ~ v1_funct_1(E_76) ) ),
    inference(resolution,[status(thm)],[c_42,c_180])).

tff(c_228,plain,(
    ! [A_85,B_86,E_87] :
      ( k1_partfun1(A_85,B_86,'#skF_1','#skF_1',E_87,'#skF_2') = k5_relat_1(E_87,'#skF_2')
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_1(E_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_182])).

tff(c_234,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_228])).

tff(c_240,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_234])).

tff(c_34,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_137,plain,(
    ! [D_58,C_59,A_60,B_61] :
      ( D_58 = C_59
      | ~ r2_relset_1(A_60,B_61,C_59,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_143,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_34,c_137])).

tff(c_154,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_143])).

tff(c_155,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_247,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_155])).

tff(c_258,plain,(
    ! [E_91,A_92,B_89,F_93,C_88,D_90] :
      ( m1_subset_1(k1_partfun1(A_92,B_89,C_88,D_90,E_91,F_93),k1_zfmisc_1(k2_zfmisc_1(A_92,D_90)))
      | ~ m1_subset_1(F_93,k1_zfmisc_1(k2_zfmisc_1(C_88,D_90)))
      | ~ v1_funct_1(F_93)
      | ~ m1_subset_1(E_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_89)))
      | ~ v1_funct_1(E_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_295,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_258])).

tff(c_318,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_46,c_42,c_295])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_318])).

tff(c_321,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_367,plain,(
    ! [C_110,A_108,B_107,E_111,F_109,D_106] :
      ( k1_partfun1(A_108,B_107,C_110,D_106,E_111,F_109) = k5_relat_1(E_111,F_109)
      | ~ m1_subset_1(F_109,k1_zfmisc_1(k2_zfmisc_1(C_110,D_106)))
      | ~ v1_funct_1(F_109)
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_1(E_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_369,plain,(
    ! [A_108,B_107,E_111] :
      ( k1_partfun1(A_108,B_107,'#skF_1','#skF_1',E_111,'#skF_2') = k5_relat_1(E_111,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_1(E_111) ) ),
    inference(resolution,[status(thm)],[c_42,c_367])).

tff(c_379,plain,(
    ! [A_114,B_115,E_116] :
      ( k1_partfun1(A_114,B_115,'#skF_1','#skF_1',E_116,'#skF_2') = k5_relat_1(E_116,'#skF_2')
      | ~ m1_subset_1(E_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_1(E_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_369])).

tff(c_385,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_379])).

tff(c_391,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_321,c_385])).

tff(c_26,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [C_6,B_4] :
      ( k6_relat_1(k1_relat_1(C_6)) = C_6
      | k5_relat_1(C_6,B_4) != B_4
      | ~ v2_funct_1(B_4)
      | ~ r1_tarski(k2_relat_1(C_6),k1_relat_1(C_6))
      | k1_relat_1(C_6) != k1_relat_1(B_4)
      | ~ v1_funct_1(C_6)
      | ~ v1_relat_1(C_6)
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_47,plain,(
    ! [C_6,B_4] :
      ( k6_partfun1(k1_relat_1(C_6)) = C_6
      | k5_relat_1(C_6,B_4) != B_4
      | ~ v2_funct_1(B_4)
      | ~ r1_tarski(k2_relat_1(C_6),k1_relat_1(C_6))
      | k1_relat_1(C_6) != k1_relat_1(B_4)
      | ~ v1_funct_1(C_6)
      | ~ v1_relat_1(C_6)
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6])).

tff(c_394,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v2_funct_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k1_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_47])).

tff(c_399,plain,
    ( k6_partfun1('#skF_1') = '#skF_3'
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_46,c_65,c_40,c_127,c_132,c_132,c_32,c_132,c_394])).

tff(c_401,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_399])).

tff(c_409,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_401])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_74,c_409])).

tff(c_414,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_416,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_30])).

tff(c_419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:42:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.43  
% 2.72/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.43  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.43  
% 2.72/1.43  %Foreground sorts:
% 2.72/1.43  
% 2.72/1.43  
% 2.72/1.43  %Background operators:
% 2.72/1.43  
% 2.72/1.43  
% 2.72/1.43  %Foreground operators:
% 2.72/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.72/1.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.72/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.72/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.72/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.72/1.43  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.72/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.72/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.72/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.43  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.72/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.72/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.72/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.72/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.72/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.43  
% 2.72/1.45  tff(f_126, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, C, B), B) & v2_funct_1(B)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_funct_2)).
% 2.72/1.45  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.72/1.45  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.72/1.45  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.72/1.45  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.72/1.45  tff(f_106, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 2.72/1.45  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.72/1.45  tff(f_96, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.72/1.45  tff(f_86, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 2.72/1.45  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.72/1.45  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_1)).
% 2.72/1.45  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.72/1.45  tff(c_90, plain, (![A_50, B_51, D_52]: (r2_relset_1(A_50, B_51, D_52, D_52) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.45  tff(c_96, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_90])).
% 2.72/1.45  tff(c_57, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.72/1.45  tff(c_65, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_57])).
% 2.72/1.45  tff(c_66, plain, (![C_40, B_41, A_42]: (v5_relat_1(C_40, B_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_42, B_41))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.72/1.45  tff(c_74, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_66])).
% 2.72/1.45  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.45  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.72/1.45  tff(c_64, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_42, c_57])).
% 2.72/1.45  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.72/1.45  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.72/1.45  tff(c_44, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.72/1.45  tff(c_106, plain, (![A_56, B_57]: (k1_relset_1(A_56, A_56, B_57)=A_56 | ~m1_subset_1(B_57, k1_zfmisc_1(k2_zfmisc_1(A_56, A_56))) | ~v1_funct_2(B_57, A_56, A_56) | ~v1_funct_1(B_57))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.72/1.45  tff(c_109, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_42, c_106])).
% 2.72/1.45  tff(c_115, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_109])).
% 2.72/1.45  tff(c_97, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.72/1.45  tff(c_104, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_42, c_97])).
% 2.72/1.45  tff(c_127, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_104])).
% 2.72/1.45  tff(c_38, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.72/1.45  tff(c_112, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_106])).
% 2.72/1.45  tff(c_118, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_112])).
% 2.72/1.45  tff(c_105, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_97])).
% 2.72/1.45  tff(c_132, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_105])).
% 2.72/1.45  tff(c_32, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.72/1.45  tff(c_180, plain, (![F_74, C_75, E_76, B_72, A_73, D_71]: (k1_partfun1(A_73, B_72, C_75, D_71, E_76, F_74)=k5_relat_1(E_76, F_74) | ~m1_subset_1(F_74, k1_zfmisc_1(k2_zfmisc_1(C_75, D_71))) | ~v1_funct_1(F_74) | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))) | ~v1_funct_1(E_76))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.72/1.45  tff(c_182, plain, (![A_73, B_72, E_76]: (k1_partfun1(A_73, B_72, '#skF_1', '#skF_1', E_76, '#skF_2')=k5_relat_1(E_76, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))) | ~v1_funct_1(E_76))), inference(resolution, [status(thm)], [c_42, c_180])).
% 2.72/1.45  tff(c_228, plain, (![A_85, B_86, E_87]: (k1_partfun1(A_85, B_86, '#skF_1', '#skF_1', E_87, '#skF_2')=k5_relat_1(E_87, '#skF_2') | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_1(E_87))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_182])).
% 2.72/1.45  tff(c_234, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_228])).
% 2.72/1.45  tff(c_240, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_234])).
% 2.72/1.45  tff(c_34, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.72/1.45  tff(c_137, plain, (![D_58, C_59, A_60, B_61]: (D_58=C_59 | ~r2_relset_1(A_60, B_61, C_59, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.45  tff(c_143, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_34, c_137])).
% 2.72/1.45  tff(c_154, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_143])).
% 2.72/1.45  tff(c_155, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_154])).
% 2.72/1.45  tff(c_247, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_155])).
% 2.72/1.45  tff(c_258, plain, (![E_91, A_92, B_89, F_93, C_88, D_90]: (m1_subset_1(k1_partfun1(A_92, B_89, C_88, D_90, E_91, F_93), k1_zfmisc_1(k2_zfmisc_1(A_92, D_90))) | ~m1_subset_1(F_93, k1_zfmisc_1(k2_zfmisc_1(C_88, D_90))) | ~v1_funct_1(F_93) | ~m1_subset_1(E_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_89))) | ~v1_funct_1(E_91))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.72/1.45  tff(c_295, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_240, c_258])).
% 2.72/1.45  tff(c_318, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_46, c_42, c_295])).
% 2.72/1.45  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_318])).
% 2.72/1.45  tff(c_321, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_154])).
% 2.72/1.45  tff(c_367, plain, (![C_110, A_108, B_107, E_111, F_109, D_106]: (k1_partfun1(A_108, B_107, C_110, D_106, E_111, F_109)=k5_relat_1(E_111, F_109) | ~m1_subset_1(F_109, k1_zfmisc_1(k2_zfmisc_1(C_110, D_106))) | ~v1_funct_1(F_109) | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_1(E_111))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.72/1.45  tff(c_369, plain, (![A_108, B_107, E_111]: (k1_partfun1(A_108, B_107, '#skF_1', '#skF_1', E_111, '#skF_2')=k5_relat_1(E_111, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_1(E_111))), inference(resolution, [status(thm)], [c_42, c_367])).
% 2.72/1.45  tff(c_379, plain, (![A_114, B_115, E_116]: (k1_partfun1(A_114, B_115, '#skF_1', '#skF_1', E_116, '#skF_2')=k5_relat_1(E_116, '#skF_2') | ~m1_subset_1(E_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_1(E_116))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_369])).
% 2.72/1.45  tff(c_385, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_379])).
% 2.72/1.45  tff(c_391, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_321, c_385])).
% 2.72/1.45  tff(c_26, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.72/1.45  tff(c_6, plain, (![C_6, B_4]: (k6_relat_1(k1_relat_1(C_6))=C_6 | k5_relat_1(C_6, B_4)!=B_4 | ~v2_funct_1(B_4) | ~r1_tarski(k2_relat_1(C_6), k1_relat_1(C_6)) | k1_relat_1(C_6)!=k1_relat_1(B_4) | ~v1_funct_1(C_6) | ~v1_relat_1(C_6) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.72/1.45  tff(c_47, plain, (![C_6, B_4]: (k6_partfun1(k1_relat_1(C_6))=C_6 | k5_relat_1(C_6, B_4)!=B_4 | ~v2_funct_1(B_4) | ~r1_tarski(k2_relat_1(C_6), k1_relat_1(C_6)) | k1_relat_1(C_6)!=k1_relat_1(B_4) | ~v1_funct_1(C_6) | ~v1_relat_1(C_6) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6])).
% 2.72/1.45  tff(c_394, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v2_funct_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k1_relat_1('#skF_2')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_391, c_47])).
% 2.72/1.45  tff(c_399, plain, (k6_partfun1('#skF_1')='#skF_3' | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_46, c_65, c_40, c_127, c_132, c_132, c_32, c_132, c_394])).
% 2.72/1.45  tff(c_401, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_399])).
% 2.72/1.45  tff(c_409, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_401])).
% 2.72/1.45  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_74, c_409])).
% 2.72/1.45  tff(c_414, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_399])).
% 2.72/1.45  tff(c_30, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.72/1.45  tff(c_416, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_414, c_30])).
% 2.72/1.45  tff(c_419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_416])).
% 2.72/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.45  
% 2.72/1.45  Inference rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Ref     : 0
% 2.72/1.45  #Sup     : 81
% 2.72/1.45  #Fact    : 0
% 2.72/1.45  #Define  : 0
% 2.72/1.45  #Split   : 2
% 2.72/1.45  #Chain   : 0
% 2.72/1.45  #Close   : 0
% 2.72/1.45  
% 2.72/1.45  Ordering : KBO
% 2.72/1.45  
% 2.72/1.45  Simplification rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Subsume      : 1
% 2.72/1.45  #Demod        : 64
% 2.72/1.45  #Tautology    : 30
% 2.72/1.45  #SimpNegUnit  : 1
% 2.72/1.45  #BackRed      : 9
% 2.72/1.45  
% 2.72/1.45  #Partial instantiations: 0
% 2.72/1.45  #Strategies tried      : 1
% 2.72/1.45  
% 2.72/1.45  Timing (in seconds)
% 2.72/1.45  ----------------------
% 2.85/1.45  Preprocessing        : 0.34
% 2.85/1.45  Parsing              : 0.19
% 2.85/1.45  CNF conversion       : 0.02
% 2.85/1.46  Main loop            : 0.28
% 2.85/1.46  Inferencing          : 0.10
% 2.85/1.46  Reduction            : 0.09
% 2.85/1.46  Demodulation         : 0.06
% 2.85/1.46  BG Simplification    : 0.02
% 2.85/1.46  Subsumption          : 0.05
% 2.85/1.46  Abstraction          : 0.02
% 2.85/1.46  MUC search           : 0.00
% 2.85/1.46  Cooper               : 0.00
% 2.85/1.46  Total                : 0.66
% 2.85/1.46  Index Insertion      : 0.00
% 2.85/1.46  Index Deletion       : 0.00
% 2.85/1.46  Index Matching       : 0.00
% 2.85/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
