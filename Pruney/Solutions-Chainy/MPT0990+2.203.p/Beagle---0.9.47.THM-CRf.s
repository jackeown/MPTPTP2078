%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:26 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 759 expanded)
%              Number of leaves         :   29 ( 321 expanded)
%              Depth                    :   19
%              Number of atoms          :  305 (4550 expanded)
%              Number of equality atoms :   88 (1360 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( B != k1_xboole_0
       => ( k2_relset_1(A,B,C) = B
        <=> ! [D] :
              ( D != k1_xboole_0
             => ! [E] :
                  ( ( v1_funct_1(E)
                    & v1_funct_2(E,B,D)
                    & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) )
                 => ! [F] :
                      ( ( v1_funct_1(F)
                        & v1_funct_2(F,B,D)
                        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(B,D))) )
                     => ( r2_relset_1(A,D,k1_partfun1(A,B,B,D,C,E),k1_partfun1(A,B,B,D,C,F))
                       => r2_relset_1(B,D,E,F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_2)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_38,plain,(
    k2_funct_1('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_58,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    ! [C_41,B_40,A_39] :
      ( m1_subset_1(k2_funct_1(C_41),k1_zfmisc_1(k2_zfmisc_1(B_40,A_39)))
      | k2_relset_1(A_39,B_40,C_41) != B_40
      | ~ v2_funct_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(C_41,A_39,B_40)
      | ~ v1_funct_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_88,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_funct_1(k2_funct_1(C_53))
      | k2_relset_1(A_54,B_55,C_53) != B_55
      | ~ v2_funct_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(C_53,A_54,B_55)
      | ~ v1_funct_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_94,plain,
    ( v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_88])).

tff(c_100,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_44,c_48,c_94])).

tff(c_123,plain,(
    ! [C_59,B_60,A_61] :
      ( v1_funct_2(k2_funct_1(C_59),B_60,A_61)
      | k2_relset_1(A_61,B_60,C_59) != B_60
      | ~ v2_funct_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60)))
      | ~ v1_funct_2(C_59,A_61,B_60)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_129,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_123])).

tff(c_135,plain,(
    v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_44,c_48,c_129])).

tff(c_203,plain,(
    ! [C_77,B_78,A_79] :
      ( m1_subset_1(k2_funct_1(C_77),k1_zfmisc_1(k2_zfmisc_1(B_78,A_79)))
      | k2_relset_1(A_79,B_78,C_77) != B_78
      | ~ v2_funct_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78)))
      | ~ v1_funct_2(C_77,A_79,B_78)
      | ~ v1_funct_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [A_11,B_12,C_13] :
      ( v1_funct_1('#skF_2'(A_11,B_12,C_13))
      | k2_relset_1(A_11,B_12,C_13) = B_12
      | k1_xboole_0 = B_12
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_2(C_13,A_11,B_12)
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_487,plain,(
    ! [B_125,A_126,C_127] :
      ( v1_funct_1('#skF_2'(B_125,A_126,k2_funct_1(C_127)))
      | k2_relset_1(B_125,A_126,k2_funct_1(C_127)) = A_126
      | k1_xboole_0 = A_126
      | ~ v1_funct_2(k2_funct_1(C_127),B_125,A_126)
      | ~ v1_funct_1(k2_funct_1(C_127))
      | k2_relset_1(A_126,B_125,C_127) != B_125
      | ~ v2_funct_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125)))
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ v1_funct_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_203,c_24])).

tff(c_502,plain,
    ( v1_funct_1('#skF_2'('#skF_5','#skF_4',k2_funct_1('#skF_6')))
    | k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_487])).

tff(c_512,plain,
    ( v1_funct_1('#skF_2'('#skF_5','#skF_4',k2_funct_1('#skF_6')))
    | k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_44,c_48,c_100,c_135,c_502])).

tff(c_513,plain,
    ( v1_funct_1('#skF_2'('#skF_5','#skF_4',k2_funct_1('#skF_6')))
    | k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_512])).

tff(c_514,plain,(
    k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_284,plain,(
    ! [B_89,C_90,A_91] :
      ( k6_partfun1(B_89) = k5_relat_1(k2_funct_1(C_90),C_90)
      | k1_xboole_0 = B_89
      | ~ v2_funct_1(C_90)
      | k2_relset_1(A_91,B_89,C_90) != B_89
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_89)))
      | ~ v1_funct_2(C_90,A_91,B_89)
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_290,plain,
    ( k5_relat_1(k2_funct_1('#skF_6'),'#skF_6') = k6_partfun1('#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_284])).

tff(c_298,plain,
    ( k5_relat_1(k2_funct_1('#skF_6'),'#skF_6') = k6_partfun1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_44,c_290])).

tff(c_299,plain,(
    k5_relat_1(k2_funct_1('#skF_6'),'#skF_6') = k6_partfun1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_298])).

tff(c_166,plain,(
    ! [B_70,E_73,A_72,D_68,C_71,F_69] :
      ( k1_partfun1(A_72,B_70,C_71,D_68,E_73,F_69) = k5_relat_1(E_73,F_69)
      | ~ m1_subset_1(F_69,k1_zfmisc_1(k2_zfmisc_1(C_71,D_68)))
      | ~ v1_funct_1(F_69)
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_72,B_70)))
      | ~ v1_funct_1(E_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_170,plain,(
    ! [A_72,B_70,E_73] :
      ( k1_partfun1(A_72,B_70,'#skF_4','#skF_5',E_73,'#skF_6') = k5_relat_1(E_73,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_72,B_70)))
      | ~ v1_funct_1(E_73) ) ),
    inference(resolution,[status(thm)],[c_56,c_166])).

tff(c_234,plain,(
    ! [A_80,B_81,E_82] :
      ( k1_partfun1(A_80,B_81,'#skF_4','#skF_5',E_82,'#skF_6') = k5_relat_1(E_82,'#skF_6')
      | ~ m1_subset_1(E_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_1(E_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_170])).

tff(c_428,plain,(
    ! [B_116,A_117,C_118] :
      ( k1_partfun1(B_116,A_117,'#skF_4','#skF_5',k2_funct_1(C_118),'#skF_6') = k5_relat_1(k2_funct_1(C_118),'#skF_6')
      | ~ v1_funct_1(k2_funct_1(C_118))
      | k2_relset_1(A_117,B_116,C_118) != B_116
      | ~ v2_funct_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116)))
      | ~ v1_funct_2(C_118,A_117,B_116)
      | ~ v1_funct_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_28,c_234])).

tff(c_443,plain,
    ( k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),'#skF_6') = k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_428])).

tff(c_452,plain,(
    k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),'#skF_6') = k6_partfun1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_44,c_48,c_100,c_299,c_443])).

tff(c_573,plain,(
    ! [F_138,D_134,A_137,E_136,B_139,C_135] :
      ( r2_relset_1(B_139,D_134,E_136,F_138)
      | ~ r2_relset_1(A_137,D_134,k1_partfun1(A_137,B_139,B_139,D_134,C_135,E_136),k1_partfun1(A_137,B_139,B_139,D_134,C_135,F_138))
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(B_139,D_134)))
      | ~ v1_funct_2(F_138,B_139,D_134)
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(B_139,D_134)))
      | ~ v1_funct_2(E_136,B_139,D_134)
      | ~ v1_funct_1(E_136)
      | k1_xboole_0 = D_134
      | k2_relset_1(A_137,B_139,C_135) != B_139
      | k1_xboole_0 = B_139
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_137,B_139)))
      | ~ v1_funct_2(C_135,A_137,B_139)
      | ~ v1_funct_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_579,plain,(
    ! [E_136] :
      ( r2_relset_1('#skF_4','#skF_5',E_136,'#skF_6')
      | ~ r2_relset_1('#skF_5','#skF_5',k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),E_136),k6_partfun1('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2(E_136,'#skF_4','#skF_5')
      | ~ v1_funct_1(E_136)
      | k1_xboole_0 = '#skF_5'
      | k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) != '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_573])).

tff(c_599,plain,(
    ! [E_136] :
      ( r2_relset_1('#skF_4','#skF_5',E_136,'#skF_6')
      | ~ r2_relset_1('#skF_5','#skF_5',k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),E_136),k6_partfun1('#skF_5'))
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2(E_136,'#skF_4','#skF_5')
      | ~ v1_funct_1(E_136)
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_135,c_514,c_60,c_58,c_56,c_579])).

tff(c_600,plain,(
    ! [E_136] :
      ( r2_relset_1('#skF_4','#skF_5',E_136,'#skF_6')
      | ~ r2_relset_1('#skF_5','#skF_5',k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),E_136),k6_partfun1('#skF_5'))
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2(E_136,'#skF_4','#skF_5')
      | ~ v1_funct_1(E_136)
      | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_599])).

tff(c_638,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_600])).

tff(c_641,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_638])).

tff(c_645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_44,c_48,c_641])).

tff(c_647,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_600])).

tff(c_54,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_168,plain,(
    ! [A_72,B_70,E_73] :
      ( k1_partfun1(A_72,B_70,'#skF_5','#skF_4',E_73,'#skF_7') = k5_relat_1(E_73,'#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_72,B_70)))
      | ~ v1_funct_1(E_73) ) ),
    inference(resolution,[status(thm)],[c_50,c_166])).

tff(c_177,plain,(
    ! [A_74,B_75,E_76] :
      ( k1_partfun1(A_74,B_75,'#skF_5','#skF_4',E_76,'#skF_7') = k5_relat_1(E_76,'#skF_7')
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_1(E_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_168])).

tff(c_183,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_177])).

tff(c_189,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_183])).

tff(c_46,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k6_partfun1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_195,plain,(
    r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k6_partfun1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_46])).

tff(c_264,plain,(
    ! [A_86,C_87,B_88] :
      ( k6_partfun1(A_86) = k5_relat_1(C_87,k2_funct_1(C_87))
      | k1_xboole_0 = B_88
      | ~ v2_funct_1(C_87)
      | k2_relset_1(A_86,B_88,C_87) != B_88
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_86,B_88)))
      | ~ v1_funct_2(C_87,A_86,B_88)
      | ~ v1_funct_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_270,plain,
    ( k5_relat_1('#skF_6',k2_funct_1('#skF_6')) = k6_partfun1('#skF_4')
    | k1_xboole_0 = '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_264])).

tff(c_278,plain,
    ( k5_relat_1('#skF_6',k2_funct_1('#skF_6')) = k6_partfun1('#skF_4')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_44,c_270])).

tff(c_279,plain,(
    k5_relat_1('#skF_6',k2_funct_1('#skF_6')) = k6_partfun1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_278])).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] :
      ( k1_partfun1(A_5,B_6,C_7,D_8,E_9,F_10) = k5_relat_1(E_9,F_10)
      | ~ m1_subset_1(F_10,k1_zfmisc_1(k2_zfmisc_1(C_7,D_8)))
      | ~ v1_funct_1(F_10)
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_1(E_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_677,plain,(
    ! [A_5,B_6,E_9] :
      ( k1_partfun1(A_5,B_6,'#skF_5','#skF_4',E_9,k2_funct_1('#skF_6')) = k5_relat_1(E_9,k2_funct_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_1(E_9) ) ),
    inference(resolution,[status(thm)],[c_647,c_6])).

tff(c_758,plain,(
    ! [A_144,B_145,E_146] :
      ( k1_partfun1(A_144,B_145,'#skF_5','#skF_4',E_146,k2_funct_1('#skF_6')) = k5_relat_1(E_146,k2_funct_1('#skF_6'))
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_1(E_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_677])).

tff(c_776,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',k2_funct_1('#skF_6')) = k5_relat_1('#skF_6',k2_funct_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_758])).

tff(c_788,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',k2_funct_1('#skF_6')) = k6_partfun1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_279,c_776])).

tff(c_52,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_591,plain,(
    ! [F_138] :
      ( r2_relset_1('#skF_5','#skF_4','#skF_7',F_138)
      | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',F_138))
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2(F_138,'#skF_5','#skF_4')
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | k1_xboole_0 = '#skF_4'
      | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_573])).

tff(c_609,plain,(
    ! [F_138] :
      ( r2_relset_1('#skF_5','#skF_4','#skF_7',F_138)
      | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',F_138))
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2(F_138,'#skF_5','#skF_4')
      | ~ v1_funct_1(F_138)
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_48,c_54,c_52,c_50,c_591])).

tff(c_610,plain,(
    ! [F_138] :
      ( r2_relset_1('#skF_5','#skF_4','#skF_7',F_138)
      | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',F_138))
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2(F_138,'#skF_5','#skF_4')
      | ~ v1_funct_1(F_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_42,c_609])).

tff(c_820,plain,
    ( r2_relset_1('#skF_5','#skF_4','#skF_7',k2_funct_1('#skF_6'))
    | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k6_partfun1('#skF_4'))
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_610])).

tff(c_832,plain,(
    r2_relset_1('#skF_5','#skF_4','#skF_7',k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_135,c_647,c_195,c_820])).

tff(c_4,plain,(
    ! [D_4,C_3,A_1,B_2] :
      ( D_4 = C_3
      | ~ r2_relset_1(A_1,B_2,C_3,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_841,plain,
    ( k2_funct_1('#skF_6') = '#skF_7'
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_832,c_4])).

tff(c_844,plain,(
    k2_funct_1('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_647,c_841])).

tff(c_846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.56  
% 3.54/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.57  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.54/1.57  
% 3.54/1.57  %Foreground sorts:
% 3.54/1.57  
% 3.54/1.57  
% 3.54/1.57  %Background operators:
% 3.54/1.57  
% 3.54/1.57  
% 3.54/1.57  %Foreground operators:
% 3.54/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.54/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.54/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.54/1.57  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.54/1.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.57  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.54/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.54/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.54/1.57  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.54/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.54/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.57  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.54/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.57  
% 3.54/1.59  tff(f_134, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 3.54/1.59  tff(f_92, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.54/1.59  tff(f_76, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => ((k2_relset_1(A, B, C) = B) <=> (![D]: (~(D = k1_xboole_0) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, B, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(B, D)))) => (r2_relset_1(A, D, k1_partfun1(A, B, B, D, C, E), k1_partfun1(A, B, B, D, C, F)) => r2_relset_1(B, D, E, F)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_2)).
% 3.54/1.59  tff(f_108, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 3.54/1.59  tff(f_43, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.54/1.59  tff(f_33, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.54/1.59  tff(c_38, plain, (k2_funct_1('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.54/1.59  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.54/1.59  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.54/1.59  tff(c_58, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.54/1.59  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.54/1.59  tff(c_44, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.54/1.59  tff(c_48, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.54/1.59  tff(c_28, plain, (![C_41, B_40, A_39]: (m1_subset_1(k2_funct_1(C_41), k1_zfmisc_1(k2_zfmisc_1(B_40, A_39))) | k2_relset_1(A_39, B_40, C_41)!=B_40 | ~v2_funct_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(C_41, A_39, B_40) | ~v1_funct_1(C_41))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.54/1.59  tff(c_42, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.54/1.59  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.54/1.59  tff(c_88, plain, (![C_53, A_54, B_55]: (v1_funct_1(k2_funct_1(C_53)) | k2_relset_1(A_54, B_55, C_53)!=B_55 | ~v2_funct_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(C_53, A_54, B_55) | ~v1_funct_1(C_53))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.54/1.59  tff(c_94, plain, (v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_88])).
% 3.54/1.59  tff(c_100, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_44, c_48, c_94])).
% 3.54/1.59  tff(c_123, plain, (![C_59, B_60, A_61]: (v1_funct_2(k2_funct_1(C_59), B_60, A_61) | k2_relset_1(A_61, B_60, C_59)!=B_60 | ~v2_funct_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))) | ~v1_funct_2(C_59, A_61, B_60) | ~v1_funct_1(C_59))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.54/1.59  tff(c_129, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_123])).
% 3.54/1.59  tff(c_135, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_44, c_48, c_129])).
% 3.54/1.59  tff(c_203, plain, (![C_77, B_78, A_79]: (m1_subset_1(k2_funct_1(C_77), k1_zfmisc_1(k2_zfmisc_1(B_78, A_79))) | k2_relset_1(A_79, B_78, C_77)!=B_78 | ~v2_funct_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))) | ~v1_funct_2(C_77, A_79, B_78) | ~v1_funct_1(C_77))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.54/1.59  tff(c_24, plain, (![A_11, B_12, C_13]: (v1_funct_1('#skF_2'(A_11, B_12, C_13)) | k2_relset_1(A_11, B_12, C_13)=B_12 | k1_xboole_0=B_12 | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_2(C_13, A_11, B_12) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.54/1.59  tff(c_487, plain, (![B_125, A_126, C_127]: (v1_funct_1('#skF_2'(B_125, A_126, k2_funct_1(C_127))) | k2_relset_1(B_125, A_126, k2_funct_1(C_127))=A_126 | k1_xboole_0=A_126 | ~v1_funct_2(k2_funct_1(C_127), B_125, A_126) | ~v1_funct_1(k2_funct_1(C_127)) | k2_relset_1(A_126, B_125, C_127)!=B_125 | ~v2_funct_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))) | ~v1_funct_2(C_127, A_126, B_125) | ~v1_funct_1(C_127))), inference(resolution, [status(thm)], [c_203, c_24])).
% 3.54/1.59  tff(c_502, plain, (v1_funct_1('#skF_2'('#skF_5', '#skF_4', k2_funct_1('#skF_6'))) | k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_4' | k1_xboole_0='#skF_4' | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_487])).
% 3.54/1.59  tff(c_512, plain, (v1_funct_1('#skF_2'('#skF_5', '#skF_4', k2_funct_1('#skF_6'))) | k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_44, c_48, c_100, c_135, c_502])).
% 3.54/1.59  tff(c_513, plain, (v1_funct_1('#skF_2'('#skF_5', '#skF_4', k2_funct_1('#skF_6'))) | k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_42, c_512])).
% 3.54/1.59  tff(c_514, plain, (k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_4'), inference(splitLeft, [status(thm)], [c_513])).
% 3.54/1.59  tff(c_284, plain, (![B_89, C_90, A_91]: (k6_partfun1(B_89)=k5_relat_1(k2_funct_1(C_90), C_90) | k1_xboole_0=B_89 | ~v2_funct_1(C_90) | k2_relset_1(A_91, B_89, C_90)!=B_89 | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_89))) | ~v1_funct_2(C_90, A_91, B_89) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.54/1.59  tff(c_290, plain, (k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')=k6_partfun1('#skF_5') | k1_xboole_0='#skF_5' | ~v2_funct_1('#skF_6') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_284])).
% 3.54/1.59  tff(c_298, plain, (k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')=k6_partfun1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_44, c_290])).
% 3.54/1.59  tff(c_299, plain, (k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')=k6_partfun1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_298])).
% 3.54/1.59  tff(c_166, plain, (![B_70, E_73, A_72, D_68, C_71, F_69]: (k1_partfun1(A_72, B_70, C_71, D_68, E_73, F_69)=k5_relat_1(E_73, F_69) | ~m1_subset_1(F_69, k1_zfmisc_1(k2_zfmisc_1(C_71, D_68))) | ~v1_funct_1(F_69) | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_72, B_70))) | ~v1_funct_1(E_73))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.59  tff(c_170, plain, (![A_72, B_70, E_73]: (k1_partfun1(A_72, B_70, '#skF_4', '#skF_5', E_73, '#skF_6')=k5_relat_1(E_73, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_72, B_70))) | ~v1_funct_1(E_73))), inference(resolution, [status(thm)], [c_56, c_166])).
% 3.54/1.59  tff(c_234, plain, (![A_80, B_81, E_82]: (k1_partfun1(A_80, B_81, '#skF_4', '#skF_5', E_82, '#skF_6')=k5_relat_1(E_82, '#skF_6') | ~m1_subset_1(E_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_1(E_82))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_170])).
% 3.54/1.59  tff(c_428, plain, (![B_116, A_117, C_118]: (k1_partfun1(B_116, A_117, '#skF_4', '#skF_5', k2_funct_1(C_118), '#skF_6')=k5_relat_1(k2_funct_1(C_118), '#skF_6') | ~v1_funct_1(k2_funct_1(C_118)) | k2_relset_1(A_117, B_116, C_118)!=B_116 | ~v2_funct_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))) | ~v1_funct_2(C_118, A_117, B_116) | ~v1_funct_1(C_118))), inference(resolution, [status(thm)], [c_28, c_234])).
% 3.54/1.59  tff(c_443, plain, (k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), '#skF_6')=k5_relat_1(k2_funct_1('#skF_6'), '#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_428])).
% 3.54/1.59  tff(c_452, plain, (k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), '#skF_6')=k6_partfun1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_44, c_48, c_100, c_299, c_443])).
% 3.54/1.59  tff(c_573, plain, (![F_138, D_134, A_137, E_136, B_139, C_135]: (r2_relset_1(B_139, D_134, E_136, F_138) | ~r2_relset_1(A_137, D_134, k1_partfun1(A_137, B_139, B_139, D_134, C_135, E_136), k1_partfun1(A_137, B_139, B_139, D_134, C_135, F_138)) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1(B_139, D_134))) | ~v1_funct_2(F_138, B_139, D_134) | ~v1_funct_1(F_138) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(B_139, D_134))) | ~v1_funct_2(E_136, B_139, D_134) | ~v1_funct_1(E_136) | k1_xboole_0=D_134 | k2_relset_1(A_137, B_139, C_135)!=B_139 | k1_xboole_0=B_139 | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_137, B_139))) | ~v1_funct_2(C_135, A_137, B_139) | ~v1_funct_1(C_135))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.54/1.59  tff(c_579, plain, (![E_136]: (r2_relset_1('#skF_4', '#skF_5', E_136, '#skF_6') | ~r2_relset_1('#skF_5', '#skF_5', k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), E_136), k6_partfun1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2(E_136, '#skF_4', '#skF_5') | ~v1_funct_1(E_136) | k1_xboole_0='#skF_5' | k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))!='#skF_4' | k1_xboole_0='#skF_4' | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_452, c_573])).
% 3.54/1.59  tff(c_599, plain, (![E_136]: (r2_relset_1('#skF_4', '#skF_5', E_136, '#skF_6') | ~r2_relset_1('#skF_5', '#skF_5', k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), E_136), k6_partfun1('#skF_5')) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2(E_136, '#skF_4', '#skF_5') | ~v1_funct_1(E_136) | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_135, c_514, c_60, c_58, c_56, c_579])).
% 3.54/1.59  tff(c_600, plain, (![E_136]: (r2_relset_1('#skF_4', '#skF_5', E_136, '#skF_6') | ~r2_relset_1('#skF_5', '#skF_5', k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), E_136), k6_partfun1('#skF_5')) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2(E_136, '#skF_4', '#skF_5') | ~v1_funct_1(E_136) | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_599])).
% 3.54/1.59  tff(c_638, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_600])).
% 3.54/1.59  tff(c_641, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_28, c_638])).
% 3.54/1.59  tff(c_645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_44, c_48, c_641])).
% 3.54/1.59  tff(c_647, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_600])).
% 3.54/1.59  tff(c_54, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.54/1.59  tff(c_168, plain, (![A_72, B_70, E_73]: (k1_partfun1(A_72, B_70, '#skF_5', '#skF_4', E_73, '#skF_7')=k5_relat_1(E_73, '#skF_7') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_72, B_70))) | ~v1_funct_1(E_73))), inference(resolution, [status(thm)], [c_50, c_166])).
% 3.54/1.59  tff(c_177, plain, (![A_74, B_75, E_76]: (k1_partfun1(A_74, B_75, '#skF_5', '#skF_4', E_76, '#skF_7')=k5_relat_1(E_76, '#skF_7') | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_1(E_76))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_168])).
% 3.54/1.59  tff(c_183, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_177])).
% 3.54/1.59  tff(c_189, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_183])).
% 3.54/1.59  tff(c_46, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k6_partfun1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.54/1.59  tff(c_195, plain, (r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k6_partfun1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_46])).
% 3.54/1.59  tff(c_264, plain, (![A_86, C_87, B_88]: (k6_partfun1(A_86)=k5_relat_1(C_87, k2_funct_1(C_87)) | k1_xboole_0=B_88 | ~v2_funct_1(C_87) | k2_relset_1(A_86, B_88, C_87)!=B_88 | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_86, B_88))) | ~v1_funct_2(C_87, A_86, B_88) | ~v1_funct_1(C_87))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.54/1.59  tff(c_270, plain, (k5_relat_1('#skF_6', k2_funct_1('#skF_6'))=k6_partfun1('#skF_4') | k1_xboole_0='#skF_5' | ~v2_funct_1('#skF_6') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_264])).
% 3.54/1.59  tff(c_278, plain, (k5_relat_1('#skF_6', k2_funct_1('#skF_6'))=k6_partfun1('#skF_4') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_44, c_270])).
% 3.54/1.59  tff(c_279, plain, (k5_relat_1('#skF_6', k2_funct_1('#skF_6'))=k6_partfun1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_278])).
% 3.54/1.59  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (k1_partfun1(A_5, B_6, C_7, D_8, E_9, F_10)=k5_relat_1(E_9, F_10) | ~m1_subset_1(F_10, k1_zfmisc_1(k2_zfmisc_1(C_7, D_8))) | ~v1_funct_1(F_10) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_1(E_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.59  tff(c_677, plain, (![A_5, B_6, E_9]: (k1_partfun1(A_5, B_6, '#skF_5', '#skF_4', E_9, k2_funct_1('#skF_6'))=k5_relat_1(E_9, k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_1(E_9))), inference(resolution, [status(thm)], [c_647, c_6])).
% 3.54/1.59  tff(c_758, plain, (![A_144, B_145, E_146]: (k1_partfun1(A_144, B_145, '#skF_5', '#skF_4', E_146, k2_funct_1('#skF_6'))=k5_relat_1(E_146, k2_funct_1('#skF_6')) | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_1(E_146))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_677])).
% 3.54/1.59  tff(c_776, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', k2_funct_1('#skF_6'))=k5_relat_1('#skF_6', k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_758])).
% 3.54/1.59  tff(c_788, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', k2_funct_1('#skF_6'))=k6_partfun1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_279, c_776])).
% 3.54/1.59  tff(c_52, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.54/1.59  tff(c_591, plain, (![F_138]: (r2_relset_1('#skF_5', '#skF_4', '#skF_7', F_138) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', F_138)) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(F_138, '#skF_5', '#skF_4') | ~v1_funct_1(F_138) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | k1_xboole_0='#skF_4' | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_189, c_573])).
% 3.54/1.59  tff(c_609, plain, (![F_138]: (r2_relset_1('#skF_5', '#skF_4', '#skF_7', F_138) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', F_138)) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(F_138, '#skF_5', '#skF_4') | ~v1_funct_1(F_138) | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_48, c_54, c_52, c_50, c_591])).
% 3.54/1.59  tff(c_610, plain, (![F_138]: (r2_relset_1('#skF_5', '#skF_4', '#skF_7', F_138) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', F_138)) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(F_138, '#skF_5', '#skF_4') | ~v1_funct_1(F_138))), inference(negUnitSimplification, [status(thm)], [c_40, c_42, c_609])).
% 3.54/1.59  tff(c_820, plain, (r2_relset_1('#skF_5', '#skF_4', '#skF_7', k2_funct_1('#skF_6')) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k6_partfun1('#skF_4')) | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_788, c_610])).
% 3.54/1.59  tff(c_832, plain, (r2_relset_1('#skF_5', '#skF_4', '#skF_7', k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_135, c_647, c_195, c_820])).
% 3.54/1.59  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_relset_1(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.54/1.59  tff(c_841, plain, (k2_funct_1('#skF_6')='#skF_7' | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(resolution, [status(thm)], [c_832, c_4])).
% 3.54/1.59  tff(c_844, plain, (k2_funct_1('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_647, c_841])).
% 3.54/1.59  tff(c_846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_844])).
% 3.54/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.59  
% 3.54/1.59  Inference rules
% 3.54/1.59  ----------------------
% 3.54/1.59  #Ref     : 0
% 3.54/1.59  #Sup     : 164
% 3.54/1.59  #Fact    : 0
% 3.54/1.59  #Define  : 0
% 3.54/1.59  #Split   : 6
% 3.54/1.59  #Chain   : 0
% 3.54/1.59  #Close   : 0
% 3.54/1.59  
% 3.54/1.59  Ordering : KBO
% 3.54/1.59  
% 3.54/1.59  Simplification rules
% 3.54/1.59  ----------------------
% 3.54/1.59  #Subsume      : 20
% 3.54/1.59  #Demod        : 246
% 3.54/1.59  #Tautology    : 47
% 3.54/1.59  #SimpNegUnit  : 33
% 3.54/1.59  #BackRed      : 2
% 3.54/1.59  
% 3.54/1.59  #Partial instantiations: 0
% 3.54/1.59  #Strategies tried      : 1
% 3.54/1.59  
% 3.54/1.59  Timing (in seconds)
% 3.54/1.59  ----------------------
% 3.54/1.59  Preprocessing        : 0.36
% 3.54/1.59  Parsing              : 0.19
% 3.54/1.59  CNF conversion       : 0.03
% 3.54/1.59  Main loop            : 0.45
% 3.54/1.59  Inferencing          : 0.15
% 3.54/1.59  Reduction            : 0.14
% 3.54/1.59  Demodulation         : 0.11
% 3.54/1.59  BG Simplification    : 0.03
% 3.54/1.59  Subsumption          : 0.10
% 3.54/1.59  Abstraction          : 0.03
% 3.54/1.59  MUC search           : 0.00
% 3.54/1.59  Cooper               : 0.00
% 3.54/1.59  Total                : 0.86
% 3.54/1.59  Index Insertion      : 0.00
% 3.54/1.59  Index Deletion       : 0.00
% 3.54/1.59  Index Matching       : 0.00
% 3.54/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
