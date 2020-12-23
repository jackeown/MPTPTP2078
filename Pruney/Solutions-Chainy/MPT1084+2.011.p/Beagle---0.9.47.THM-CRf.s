%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:21 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 882 expanded)
%              Number of leaves         :   35 ( 348 expanded)
%              Depth                    :   14
%              Number of atoms          :  193 (2810 expanded)
%              Number of equality atoms :   56 ( 634 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k9_setfam_1 > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_100,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_109,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_100])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_150,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_166,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_150])).

tff(c_281,plain,(
    ! [A_89,B_90] :
      ( k1_relset_1(A_89,A_89,B_90) = A_89
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_zfmisc_1(A_89,A_89)))
      | ~ v1_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_292,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_281])).

tff(c_299,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_166,c_292])).

tff(c_36,plain,(
    ! [A_27] : k6_relat_1(A_27) = k6_partfun1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_2'(k1_relat_1(B_13),B_13),k1_relat_1(B_13))
      | k6_relat_1(k1_relat_1(B_13)) = B_13
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_57,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_2'(k1_relat_1(B_13),B_13),k1_relat_1(B_13))
      | k6_partfun1(k1_relat_1(B_13)) = B_13
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_24])).

tff(c_313,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),k1_relat_1('#skF_4'))
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_57])).

tff(c_338,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_52,c_299,c_299,c_313])).

tff(c_403,plain,(
    k6_partfun1('#skF_3') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_44,plain,(
    ~ r2_funct_2('#skF_3','#skF_3','#skF_4',k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_404,plain,(
    ~ r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_44])).

tff(c_682,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( r2_funct_2(A_108,B_109,C_110,C_110)
      | ~ m1_subset_1(D_111,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_2(D_111,A_108,B_109)
      | ~ v1_funct_1(D_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_2(C_110,A_108,B_109)
      | ~ v1_funct_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_690,plain,(
    ! [C_110] :
      ( r2_funct_2('#skF_3','#skF_3',C_110,C_110)
      | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_2(C_110,'#skF_3','#skF_3')
      | ~ v1_funct_1(C_110) ) ),
    inference(resolution,[status(thm)],[c_48,c_682])).

tff(c_816,plain,(
    ! [C_116] :
      ( r2_funct_2('#skF_3','#skF_3',C_116,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_2(C_116,'#skF_3','#skF_3')
      | ~ v1_funct_1(C_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_690])).

tff(c_824,plain,
    ( r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_816])).

tff(c_831,plain,(
    r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_824])).

tff(c_833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_831])).

tff(c_835,plain,(
    k6_partfun1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_22,plain,(
    ! [B_13] :
      ( k1_funct_1(B_13,'#skF_2'(k1_relat_1(B_13),B_13)) != '#skF_2'(k1_relat_1(B_13),B_13)
      | k6_relat_1(k1_relat_1(B_13)) = B_13
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_355,plain,(
    ! [B_91] :
      ( k1_funct_1(B_91,'#skF_2'(k1_relat_1(B_91),B_91)) != '#skF_2'(k1_relat_1(B_91),B_91)
      | k6_partfun1(k1_relat_1(B_91)) = B_91
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_22])).

tff(c_358,plain,
    ( k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4')) != '#skF_2'(k1_relat_1('#skF_4'),'#skF_4')
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_355])).

tff(c_360,plain,
    ( k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4')) != '#skF_2'('#skF_3','#skF_4')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_52,c_299,c_299,c_358])).

tff(c_868,plain,(
    k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4')) != '#skF_2'('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_835,c_360])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_167,plain,(
    ! [A_66,B_67] :
      ( k1_funct_1(A_66,B_67) = k1_xboole_0
      | r2_hidden(B_67,k1_relat_1(A_66))
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_174,plain,(
    ! [B_67,A_66] :
      ( m1_subset_1(B_67,k1_relat_1(A_66))
      | v1_xboole_0(k1_relat_1(A_66))
      | k1_funct_1(A_66,B_67) = k1_xboole_0
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_167,c_6])).

tff(c_304,plain,(
    ! [B_67] :
      ( m1_subset_1(B_67,'#skF_3')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | k1_funct_1('#skF_4',B_67) = k1_xboole_0
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_174])).

tff(c_331,plain,(
    ! [B_67] :
      ( m1_subset_1(B_67,'#skF_3')
      | v1_xboole_0('#skF_3')
      | k1_funct_1('#skF_4',B_67) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_52,c_299,c_304])).

tff(c_332,plain,(
    ! [B_67] :
      ( m1_subset_1(B_67,'#skF_3')
      | k1_funct_1('#skF_4',B_67) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_331])).

tff(c_949,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k3_funct_2(A_122,B_123,C_124,D_125) = k1_funct_1(C_124,D_125)
      | ~ m1_subset_1(D_125,A_122)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_funct_2(C_124,A_122,B_123)
      | ~ v1_funct_1(C_124)
      | v1_xboole_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_955,plain,(
    ! [B_123,C_124,B_67] :
      ( k3_funct_2('#skF_3',B_123,C_124,B_67) = k1_funct_1(C_124,B_67)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_123)))
      | ~ v1_funct_2(C_124,'#skF_3',B_123)
      | ~ v1_funct_1(C_124)
      | v1_xboole_0('#skF_3')
      | k1_funct_1('#skF_4',B_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_332,c_949])).

tff(c_1086,plain,(
    ! [B_136,C_137,B_138] :
      ( k3_funct_2('#skF_3',B_136,C_137,B_138) = k1_funct_1(C_137,B_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_136)))
      | ~ v1_funct_2(C_137,'#skF_3',B_136)
      | ~ v1_funct_1(C_137)
      | k1_funct_1('#skF_4',B_138) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_955])).

tff(c_1097,plain,(
    ! [B_138] :
      ( k3_funct_2('#skF_3','#skF_3','#skF_4',B_138) = k1_funct_1('#skF_4',B_138)
      | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | k1_funct_1('#skF_4',B_138) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_1086])).

tff(c_1108,plain,(
    ! [B_139] :
      ( k3_funct_2('#skF_3','#skF_3','#skF_4',B_139) = k1_funct_1('#skF_4',B_139)
      | k1_funct_1('#skF_4',B_139) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1097])).

tff(c_834,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_838,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_834,c_6])).

tff(c_844,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_838])).

tff(c_46,plain,(
    ! [C_39] :
      ( k3_funct_2('#skF_3','#skF_3','#skF_4',C_39) = C_39
      | ~ m1_subset_1(C_39,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_853,plain,(
    k3_funct_2('#skF_3','#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4')) = '#skF_2'('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_844,c_46])).

tff(c_1114,plain,
    ( k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4')) = '#skF_2'('#skF_3','#skF_4')
    | k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1108,c_853])).

tff(c_1134,plain,(
    k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_868,c_1114])).

tff(c_1137,plain,(
    '#skF_2'('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1134,c_868])).

tff(c_953,plain,(
    ! [B_123,C_124] :
      ( k3_funct_2('#skF_3',B_123,C_124,'#skF_2'('#skF_3','#skF_4')) = k1_funct_1(C_124,'#skF_2'('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_123)))
      | ~ v1_funct_2(C_124,'#skF_3',B_123)
      | ~ v1_funct_1(C_124)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_844,c_949])).

tff(c_1205,plain,(
    ! [B_143,C_144] :
      ( k3_funct_2('#skF_3',B_143,C_144,'#skF_2'('#skF_3','#skF_4')) = k1_funct_1(C_144,'#skF_2'('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_143)))
      | ~ v1_funct_2(C_144,'#skF_3',B_143)
      | ~ v1_funct_1(C_144) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_953])).

tff(c_1220,plain,
    ( k3_funct_2('#skF_3','#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1205])).

tff(c_1230,plain,(
    '#skF_2'('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1134,c_853,c_1220])).

tff(c_1232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1137,c_1230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.54  
% 3.43/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.54  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k9_setfam_1 > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.43/1.54  
% 3.43/1.54  %Foreground sorts:
% 3.43/1.54  
% 3.43/1.54  
% 3.43/1.54  %Background operators:
% 3.43/1.54  
% 3.43/1.54  
% 3.43/1.54  %Foreground operators:
% 3.43/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.43/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.43/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.43/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.43/1.54  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.43/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.43/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.43/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.43/1.54  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.43/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.43/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.43/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.54  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.43/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.54  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.43/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.54  
% 3.43/1.56  tff(f_140, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 3.43/1.56  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.43/1.56  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.43/1.56  tff(f_122, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 3.43/1.56  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.43/1.56  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 3.43/1.56  tff(f_114, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 3.43/1.56  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.43/1.56  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.43/1.56  tff(f_96, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.43/1.56  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.43/1.56  tff(c_100, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.43/1.56  tff(c_109, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_100])).
% 3.43/1.56  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.43/1.56  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.43/1.56  tff(c_150, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.43/1.56  tff(c_166, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_150])).
% 3.43/1.56  tff(c_281, plain, (![A_89, B_90]: (k1_relset_1(A_89, A_89, B_90)=A_89 | ~m1_subset_1(B_90, k1_zfmisc_1(k2_zfmisc_1(A_89, A_89))) | ~v1_funct_2(B_90, A_89, A_89) | ~v1_funct_1(B_90))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.43/1.56  tff(c_292, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_281])).
% 3.43/1.56  tff(c_299, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_166, c_292])).
% 3.43/1.56  tff(c_36, plain, (![A_27]: (k6_relat_1(A_27)=k6_partfun1(A_27))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.43/1.56  tff(c_24, plain, (![B_13]: (r2_hidden('#skF_2'(k1_relat_1(B_13), B_13), k1_relat_1(B_13)) | k6_relat_1(k1_relat_1(B_13))=B_13 | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.43/1.56  tff(c_57, plain, (![B_13]: (r2_hidden('#skF_2'(k1_relat_1(B_13), B_13), k1_relat_1(B_13)) | k6_partfun1(k1_relat_1(B_13))=B_13 | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_24])).
% 3.43/1.56  tff(c_313, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), k1_relat_1('#skF_4')) | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_299, c_57])).
% 3.43/1.56  tff(c_338, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_52, c_299, c_299, c_313])).
% 3.43/1.56  tff(c_403, plain, (k6_partfun1('#skF_3')='#skF_4'), inference(splitLeft, [status(thm)], [c_338])).
% 3.43/1.56  tff(c_44, plain, (~r2_funct_2('#skF_3', '#skF_3', '#skF_4', k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.43/1.56  tff(c_404, plain, (~r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_44])).
% 3.43/1.56  tff(c_682, plain, (![A_108, B_109, C_110, D_111]: (r2_funct_2(A_108, B_109, C_110, C_110) | ~m1_subset_1(D_111, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_2(D_111, A_108, B_109) | ~v1_funct_1(D_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_2(C_110, A_108, B_109) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.43/1.56  tff(c_690, plain, (![C_110]: (r2_funct_2('#skF_3', '#skF_3', C_110, C_110) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2(C_110, '#skF_3', '#skF_3') | ~v1_funct_1(C_110))), inference(resolution, [status(thm)], [c_48, c_682])).
% 3.43/1.56  tff(c_816, plain, (![C_116]: (r2_funct_2('#skF_3', '#skF_3', C_116, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2(C_116, '#skF_3', '#skF_3') | ~v1_funct_1(C_116))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_690])).
% 3.43/1.56  tff(c_824, plain, (r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_816])).
% 3.43/1.56  tff(c_831, plain, (r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_824])).
% 3.43/1.56  tff(c_833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_404, c_831])).
% 3.43/1.56  tff(c_835, plain, (k6_partfun1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_338])).
% 3.43/1.56  tff(c_22, plain, (![B_13]: (k1_funct_1(B_13, '#skF_2'(k1_relat_1(B_13), B_13))!='#skF_2'(k1_relat_1(B_13), B_13) | k6_relat_1(k1_relat_1(B_13))=B_13 | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.43/1.56  tff(c_355, plain, (![B_91]: (k1_funct_1(B_91, '#skF_2'(k1_relat_1(B_91), B_91))!='#skF_2'(k1_relat_1(B_91), B_91) | k6_partfun1(k1_relat_1(B_91))=B_91 | ~v1_funct_1(B_91) | ~v1_relat_1(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_22])).
% 3.43/1.56  tff(c_358, plain, (k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4'))!='#skF_2'(k1_relat_1('#skF_4'), '#skF_4') | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_299, c_355])).
% 3.43/1.56  tff(c_360, plain, (k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4'))!='#skF_2'('#skF_3', '#skF_4') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_52, c_299, c_299, c_358])).
% 3.43/1.56  tff(c_868, plain, (k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4'))!='#skF_2'('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_835, c_360])).
% 3.43/1.56  tff(c_54, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.43/1.56  tff(c_167, plain, (![A_66, B_67]: (k1_funct_1(A_66, B_67)=k1_xboole_0 | r2_hidden(B_67, k1_relat_1(A_66)) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.43/1.56  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.43/1.56  tff(c_174, plain, (![B_67, A_66]: (m1_subset_1(B_67, k1_relat_1(A_66)) | v1_xboole_0(k1_relat_1(A_66)) | k1_funct_1(A_66, B_67)=k1_xboole_0 | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_167, c_6])).
% 3.43/1.56  tff(c_304, plain, (![B_67]: (m1_subset_1(B_67, '#skF_3') | v1_xboole_0(k1_relat_1('#skF_4')) | k1_funct_1('#skF_4', B_67)=k1_xboole_0 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_299, c_174])).
% 3.43/1.56  tff(c_331, plain, (![B_67]: (m1_subset_1(B_67, '#skF_3') | v1_xboole_0('#skF_3') | k1_funct_1('#skF_4', B_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_52, c_299, c_304])).
% 3.43/1.56  tff(c_332, plain, (![B_67]: (m1_subset_1(B_67, '#skF_3') | k1_funct_1('#skF_4', B_67)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_331])).
% 3.43/1.56  tff(c_949, plain, (![A_122, B_123, C_124, D_125]: (k3_funct_2(A_122, B_123, C_124, D_125)=k1_funct_1(C_124, D_125) | ~m1_subset_1(D_125, A_122) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_funct_2(C_124, A_122, B_123) | ~v1_funct_1(C_124) | v1_xboole_0(A_122))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.43/1.56  tff(c_955, plain, (![B_123, C_124, B_67]: (k3_funct_2('#skF_3', B_123, C_124, B_67)=k1_funct_1(C_124, B_67) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_123))) | ~v1_funct_2(C_124, '#skF_3', B_123) | ~v1_funct_1(C_124) | v1_xboole_0('#skF_3') | k1_funct_1('#skF_4', B_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_332, c_949])).
% 3.43/1.56  tff(c_1086, plain, (![B_136, C_137, B_138]: (k3_funct_2('#skF_3', B_136, C_137, B_138)=k1_funct_1(C_137, B_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_136))) | ~v1_funct_2(C_137, '#skF_3', B_136) | ~v1_funct_1(C_137) | k1_funct_1('#skF_4', B_138)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_955])).
% 3.43/1.56  tff(c_1097, plain, (![B_138]: (k3_funct_2('#skF_3', '#skF_3', '#skF_4', B_138)=k1_funct_1('#skF_4', B_138) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | k1_funct_1('#skF_4', B_138)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_1086])).
% 3.43/1.56  tff(c_1108, plain, (![B_139]: (k3_funct_2('#skF_3', '#skF_3', '#skF_4', B_139)=k1_funct_1('#skF_4', B_139) | k1_funct_1('#skF_4', B_139)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1097])).
% 3.43/1.56  tff(c_834, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_338])).
% 3.43/1.56  tff(c_838, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_834, c_6])).
% 3.43/1.56  tff(c_844, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_838])).
% 3.43/1.56  tff(c_46, plain, (![C_39]: (k3_funct_2('#skF_3', '#skF_3', '#skF_4', C_39)=C_39 | ~m1_subset_1(C_39, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.43/1.56  tff(c_853, plain, (k3_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4'))='#skF_2'('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_844, c_46])).
% 3.43/1.56  tff(c_1114, plain, (k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4'))='#skF_2'('#skF_3', '#skF_4') | k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1108, c_853])).
% 3.43/1.56  tff(c_1134, plain, (k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_868, c_1114])).
% 3.43/1.56  tff(c_1137, plain, ('#skF_2'('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1134, c_868])).
% 3.43/1.56  tff(c_953, plain, (![B_123, C_124]: (k3_funct_2('#skF_3', B_123, C_124, '#skF_2'('#skF_3', '#skF_4'))=k1_funct_1(C_124, '#skF_2'('#skF_3', '#skF_4')) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_123))) | ~v1_funct_2(C_124, '#skF_3', B_123) | ~v1_funct_1(C_124) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_844, c_949])).
% 3.43/1.56  tff(c_1205, plain, (![B_143, C_144]: (k3_funct_2('#skF_3', B_143, C_144, '#skF_2'('#skF_3', '#skF_4'))=k1_funct_1(C_144, '#skF_2'('#skF_3', '#skF_4')) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_143))) | ~v1_funct_2(C_144, '#skF_3', B_143) | ~v1_funct_1(C_144))), inference(negUnitSimplification, [status(thm)], [c_54, c_953])).
% 3.43/1.56  tff(c_1220, plain, (k3_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1205])).
% 3.43/1.56  tff(c_1230, plain, ('#skF_2'('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1134, c_853, c_1220])).
% 3.43/1.56  tff(c_1232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1137, c_1230])).
% 3.43/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.56  
% 3.43/1.56  Inference rules
% 3.43/1.56  ----------------------
% 3.43/1.56  #Ref     : 0
% 3.43/1.56  #Sup     : 246
% 3.43/1.56  #Fact    : 2
% 3.43/1.56  #Define  : 0
% 3.43/1.56  #Split   : 6
% 3.43/1.56  #Chain   : 0
% 3.43/1.56  #Close   : 0
% 3.43/1.56  
% 3.43/1.56  Ordering : KBO
% 3.43/1.56  
% 3.43/1.56  Simplification rules
% 3.43/1.56  ----------------------
% 3.43/1.56  #Subsume      : 63
% 3.43/1.56  #Demod        : 169
% 3.43/1.56  #Tautology    : 82
% 3.43/1.56  #SimpNegUnit  : 51
% 3.43/1.56  #BackRed      : 3
% 3.43/1.56  
% 3.43/1.56  #Partial instantiations: 0
% 3.43/1.56  #Strategies tried      : 1
% 3.43/1.56  
% 3.43/1.56  Timing (in seconds)
% 3.43/1.56  ----------------------
% 3.43/1.56  Preprocessing        : 0.34
% 3.43/1.56  Parsing              : 0.18
% 3.43/1.56  CNF conversion       : 0.02
% 3.43/1.56  Main loop            : 0.44
% 3.43/1.56  Inferencing          : 0.16
% 3.43/1.57  Reduction            : 0.14
% 3.43/1.57  Demodulation         : 0.09
% 3.43/1.57  BG Simplification    : 0.02
% 3.43/1.57  Subsumption          : 0.08
% 3.43/1.57  Abstraction          : 0.03
% 3.43/1.57  MUC search           : 0.00
% 3.43/1.57  Cooper               : 0.00
% 3.43/1.57  Total                : 0.82
% 3.43/1.57  Index Insertion      : 0.00
% 3.43/1.57  Index Deletion       : 0.00
% 3.43/1.57  Index Matching       : 0.00
% 3.43/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
