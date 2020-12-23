%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:21 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 289 expanded)
%              Number of leaves         :   39 ( 119 expanded)
%              Depth                    :   11
%              Number of atoms          :  241 (1141 expanded)
%              Number of equality atoms :   98 ( 410 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_121,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_137,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_79,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_142,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_155,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_142])).

tff(c_213,plain,(
    ! [B_65,A_66,C_67] :
      ( k1_xboole_0 = B_65
      | k1_relset_1(A_66,B_65,C_67) = A_66
      | ~ v1_funct_2(C_67,A_66,B_65)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_222,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_213])).

tff(c_231,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_155,c_222])).

tff(c_232,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_231])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_110,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_110])).

tff(c_128,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_119])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_116,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_110])).

tff(c_125,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_116])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_154,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_142])).

tff(c_219,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_213])).

tff(c_227,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_154,c_219])).

tff(c_228,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_227])).

tff(c_42,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_relat_1(k1_relat_1(A_8)) != k5_relat_1(A_8,B_10)
      | k2_relat_1(A_8) != k1_relat_1(B_10)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_908,plain,(
    ! [A_174,B_175] :
      ( k2_funct_1(A_174) = B_175
      | k6_partfun1(k1_relat_1(A_174)) != k5_relat_1(A_174,B_175)
      | k2_relat_1(A_174) != k1_relat_1(B_175)
      | ~ v2_funct_1(A_174)
      | ~ v1_funct_1(B_175)
      | ~ v1_relat_1(B_175)
      | ~ v1_funct_1(A_174)
      | ~ v1_relat_1(A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14])).

tff(c_912,plain,(
    ! [B_175] :
      ( k2_funct_1('#skF_3') = B_175
      | k5_relat_1('#skF_3',B_175) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_175)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_175)
      | ~ v1_relat_1(B_175)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_908])).

tff(c_927,plain,(
    ! [B_176] :
      ( k2_funct_1('#skF_3') = B_176
      | k5_relat_1('#skF_3',B_176) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_176)
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_70,c_54,c_912])).

tff(c_933,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_927])).

tff(c_944,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_232,c_933])).

tff(c_945,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_944])).

tff(c_950,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_945])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1063,plain,(
    ! [B_202,C_203,A_204] :
      ( k6_partfun1(B_202) = k5_relat_1(k2_funct_1(C_203),C_203)
      | k1_xboole_0 = B_202
      | ~ v2_funct_1(C_203)
      | k2_relset_1(A_204,B_202,C_203) != B_202
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_204,B_202)))
      | ~ v1_funct_2(C_203,A_204,B_202)
      | ~ v1_funct_1(C_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1067,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1063])).

tff(c_1073,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_1067])).

tff(c_1074,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1073])).

tff(c_10,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_74,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_partfun1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_1082,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1074,c_74])).

tff(c_1089,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_70,c_54,c_1082])).

tff(c_1124,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1089,c_76])).

tff(c_1138,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1124])).

tff(c_1140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_950,c_1138])).

tff(c_1141,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_945])).

tff(c_634,plain,(
    ! [E_132,A_133,F_131,D_136,C_134,B_135] :
      ( k1_partfun1(A_133,B_135,C_134,D_136,E_132,F_131) = k5_relat_1(E_132,F_131)
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_134,D_136)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_135)))
      | ~ v1_funct_1(E_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_640,plain,(
    ! [A_133,B_135,E_132] :
      ( k1_partfun1(A_133,B_135,'#skF_2','#skF_1',E_132,'#skF_4') = k5_relat_1(E_132,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_135)))
      | ~ v1_funct_1(E_132) ) ),
    inference(resolution,[status(thm)],[c_60,c_634])).

tff(c_676,plain,(
    ! [A_141,B_142,E_143] :
      ( k1_partfun1(A_141,B_142,'#skF_2','#skF_1',E_143,'#skF_4') = k5_relat_1(E_143,'#skF_4')
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_1(E_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_640])).

tff(c_682,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_676])).

tff(c_689,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_682])).

tff(c_22,plain,(
    ! [A_18] : m1_subset_1(k6_relat_1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_71,plain,(
    ! [A_18] : m1_subset_1(k6_partfun1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_22])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_273,plain,(
    ! [D_72,C_73,A_74,B_75] :
      ( D_72 = C_73
      | ~ r2_relset_1(A_74,B_75,C_73,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_281,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_273])).

tff(c_296,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_281])).

tff(c_297,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_694,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_297])).

tff(c_813,plain,(
    ! [C_169,D_172,E_170,B_173,F_171,A_168] :
      ( m1_subset_1(k1_partfun1(A_168,B_173,C_169,D_172,E_170,F_171),k1_zfmisc_1(k2_zfmisc_1(A_168,D_172)))
      | ~ m1_subset_1(F_171,k1_zfmisc_1(k2_zfmisc_1(C_169,D_172)))
      | ~ v1_funct_1(F_171)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_173)))
      | ~ v1_funct_1(E_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_867,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_813])).

tff(c_896,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_867])).

tff(c_898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_694,c_896])).

tff(c_899,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_1231,plain,(
    ! [F_221,D_226,E_222,C_224,A_223,B_225] :
      ( k1_partfun1(A_223,B_225,C_224,D_226,E_222,F_221) = k5_relat_1(E_222,F_221)
      | ~ m1_subset_1(F_221,k1_zfmisc_1(k2_zfmisc_1(C_224,D_226)))
      | ~ v1_funct_1(F_221)
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_223,B_225)))
      | ~ v1_funct_1(E_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1237,plain,(
    ! [A_223,B_225,E_222] :
      ( k1_partfun1(A_223,B_225,'#skF_2','#skF_1',E_222,'#skF_4') = k5_relat_1(E_222,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_223,B_225)))
      | ~ v1_funct_1(E_222) ) ),
    inference(resolution,[status(thm)],[c_60,c_1231])).

tff(c_1320,plain,(
    ! [A_234,B_235,E_236] :
      ( k1_partfun1(A_234,B_235,'#skF_2','#skF_1',E_236,'#skF_4') = k5_relat_1(E_236,'#skF_4')
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1(E_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1237])).

tff(c_1326,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1320])).

tff(c_1333,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_899,c_1326])).

tff(c_1335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1141,c_1333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:51:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.80  
% 3.95/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.80  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.95/1.80  
% 3.95/1.80  %Foreground sorts:
% 3.95/1.80  
% 3.95/1.80  
% 3.95/1.80  %Background operators:
% 3.95/1.80  
% 3.95/1.80  
% 3.95/1.80  %Foreground operators:
% 3.95/1.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.95/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.95/1.80  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.95/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.95/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.80  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.95/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.80  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.95/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.95/1.80  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.95/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.95/1.80  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.80  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.80  tff('#skF_1', type, '#skF_1': $i).
% 3.95/1.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.95/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.80  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.95/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.95/1.80  tff('#skF_4', type, '#skF_4': $i).
% 3.95/1.80  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.95/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.95/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.80  
% 4.15/1.82  tff(f_163, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.15/1.82  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.15/1.82  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.15/1.82  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.15/1.82  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.15/1.82  tff(f_121, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.15/1.82  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 4.15/1.82  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.15/1.82  tff(f_137, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 4.15/1.82  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.15/1.82  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.15/1.82  tff(f_79, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.15/1.82  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.15/1.82  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.15/1.82  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.82  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.82  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.82  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.82  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.82  tff(c_142, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.15/1.82  tff(c_155, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_142])).
% 4.15/1.82  tff(c_213, plain, (![B_65, A_66, C_67]: (k1_xboole_0=B_65 | k1_relset_1(A_66, B_65, C_67)=A_66 | ~v1_funct_2(C_67, A_66, B_65) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.15/1.82  tff(c_222, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_213])).
% 4.15/1.82  tff(c_231, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_155, c_222])).
% 4.15/1.82  tff(c_232, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_231])).
% 4.15/1.82  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.15/1.82  tff(c_110, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.82  tff(c_119, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_110])).
% 4.15/1.82  tff(c_128, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_119])).
% 4.15/1.82  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.82  tff(c_116, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_110])).
% 4.15/1.82  tff(c_125, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_116])).
% 4.15/1.82  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.82  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.82  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.82  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.82  tff(c_154, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_142])).
% 4.15/1.82  tff(c_219, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_213])).
% 4.15/1.82  tff(c_227, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_154, c_219])).
% 4.15/1.82  tff(c_228, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_227])).
% 4.15/1.82  tff(c_42, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.15/1.82  tff(c_14, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_relat_1(k1_relat_1(A_8))!=k5_relat_1(A_8, B_10) | k2_relat_1(A_8)!=k1_relat_1(B_10) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.15/1.82  tff(c_908, plain, (![A_174, B_175]: (k2_funct_1(A_174)=B_175 | k6_partfun1(k1_relat_1(A_174))!=k5_relat_1(A_174, B_175) | k2_relat_1(A_174)!=k1_relat_1(B_175) | ~v2_funct_1(A_174) | ~v1_funct_1(B_175) | ~v1_relat_1(B_175) | ~v1_funct_1(A_174) | ~v1_relat_1(A_174))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14])).
% 4.15/1.82  tff(c_912, plain, (![B_175]: (k2_funct_1('#skF_3')=B_175 | k5_relat_1('#skF_3', B_175)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_175) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_175) | ~v1_relat_1(B_175) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_228, c_908])).
% 4.15/1.82  tff(c_927, plain, (![B_176]: (k2_funct_1('#skF_3')=B_176 | k5_relat_1('#skF_3', B_176)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_176) | ~v1_funct_1(B_176) | ~v1_relat_1(B_176))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_70, c_54, c_912])).
% 4.15/1.82  tff(c_933, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_128, c_927])).
% 4.15/1.82  tff(c_944, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_232, c_933])).
% 4.15/1.82  tff(c_945, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_944])).
% 4.15/1.82  tff(c_950, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_945])).
% 4.15/1.82  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.15/1.82  tff(c_76, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6])).
% 4.15/1.82  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.82  tff(c_1063, plain, (![B_202, C_203, A_204]: (k6_partfun1(B_202)=k5_relat_1(k2_funct_1(C_203), C_203) | k1_xboole_0=B_202 | ~v2_funct_1(C_203) | k2_relset_1(A_204, B_202, C_203)!=B_202 | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_204, B_202))) | ~v1_funct_2(C_203, A_204, B_202) | ~v1_funct_1(C_203))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.15/1.82  tff(c_1067, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1063])).
% 4.15/1.82  tff(c_1073, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_1067])).
% 4.15/1.82  tff(c_1074, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_1073])).
% 4.15/1.82  tff(c_10, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.15/1.82  tff(c_74, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_partfun1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 4.15/1.82  tff(c_1082, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1074, c_74])).
% 4.15/1.82  tff(c_1089, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_70, c_54, c_1082])).
% 4.15/1.82  tff(c_1124, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1089, c_76])).
% 4.15/1.82  tff(c_1138, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1124])).
% 4.15/1.82  tff(c_1140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_950, c_1138])).
% 4.15/1.82  tff(c_1141, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_945])).
% 4.15/1.82  tff(c_634, plain, (![E_132, A_133, F_131, D_136, C_134, B_135]: (k1_partfun1(A_133, B_135, C_134, D_136, E_132, F_131)=k5_relat_1(E_132, F_131) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_134, D_136))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_135))) | ~v1_funct_1(E_132))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.15/1.82  tff(c_640, plain, (![A_133, B_135, E_132]: (k1_partfun1(A_133, B_135, '#skF_2', '#skF_1', E_132, '#skF_4')=k5_relat_1(E_132, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_135))) | ~v1_funct_1(E_132))), inference(resolution, [status(thm)], [c_60, c_634])).
% 4.15/1.82  tff(c_676, plain, (![A_141, B_142, E_143]: (k1_partfun1(A_141, B_142, '#skF_2', '#skF_1', E_143, '#skF_4')=k5_relat_1(E_143, '#skF_4') | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_1(E_143))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_640])).
% 4.15/1.82  tff(c_682, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_676])).
% 4.15/1.82  tff(c_689, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_682])).
% 4.15/1.82  tff(c_22, plain, (![A_18]: (m1_subset_1(k6_relat_1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.15/1.82  tff(c_71, plain, (![A_18]: (m1_subset_1(k6_partfun1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_22])).
% 4.15/1.82  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.82  tff(c_273, plain, (![D_72, C_73, A_74, B_75]: (D_72=C_73 | ~r2_relset_1(A_74, B_75, C_73, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.82  tff(c_281, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_273])).
% 4.15/1.82  tff(c_296, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_281])).
% 4.15/1.82  tff(c_297, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_296])).
% 4.15/1.82  tff(c_694, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_297])).
% 4.15/1.82  tff(c_813, plain, (![C_169, D_172, E_170, B_173, F_171, A_168]: (m1_subset_1(k1_partfun1(A_168, B_173, C_169, D_172, E_170, F_171), k1_zfmisc_1(k2_zfmisc_1(A_168, D_172))) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(C_169, D_172))) | ~v1_funct_1(F_171) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_173))) | ~v1_funct_1(E_170))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.15/1.82  tff(c_867, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_689, c_813])).
% 4.15/1.82  tff(c_896, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_867])).
% 4.15/1.82  tff(c_898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_694, c_896])).
% 4.15/1.82  tff(c_899, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_296])).
% 4.15/1.82  tff(c_1231, plain, (![F_221, D_226, E_222, C_224, A_223, B_225]: (k1_partfun1(A_223, B_225, C_224, D_226, E_222, F_221)=k5_relat_1(E_222, F_221) | ~m1_subset_1(F_221, k1_zfmisc_1(k2_zfmisc_1(C_224, D_226))) | ~v1_funct_1(F_221) | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_223, B_225))) | ~v1_funct_1(E_222))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.15/1.82  tff(c_1237, plain, (![A_223, B_225, E_222]: (k1_partfun1(A_223, B_225, '#skF_2', '#skF_1', E_222, '#skF_4')=k5_relat_1(E_222, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_223, B_225))) | ~v1_funct_1(E_222))), inference(resolution, [status(thm)], [c_60, c_1231])).
% 4.15/1.82  tff(c_1320, plain, (![A_234, B_235, E_236]: (k1_partfun1(A_234, B_235, '#skF_2', '#skF_1', E_236, '#skF_4')=k5_relat_1(E_236, '#skF_4') | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1(E_236))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1237])).
% 4.15/1.82  tff(c_1326, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1320])).
% 4.15/1.82  tff(c_1333, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_899, c_1326])).
% 4.15/1.82  tff(c_1335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1141, c_1333])).
% 4.15/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.82  
% 4.15/1.82  Inference rules
% 4.15/1.82  ----------------------
% 4.15/1.82  #Ref     : 0
% 4.15/1.82  #Sup     : 276
% 4.15/1.82  #Fact    : 0
% 4.15/1.82  #Define  : 0
% 4.15/1.82  #Split   : 11
% 4.15/1.82  #Chain   : 0
% 4.15/1.82  #Close   : 0
% 4.15/1.82  
% 4.15/1.82  Ordering : KBO
% 4.15/1.82  
% 4.15/1.82  Simplification rules
% 4.15/1.82  ----------------------
% 4.15/1.82  #Subsume      : 15
% 4.15/1.82  #Demod        : 249
% 4.15/1.82  #Tautology    : 92
% 4.15/1.82  #SimpNegUnit  : 23
% 4.15/1.82  #BackRed      : 17
% 4.15/1.82  
% 4.15/1.82  #Partial instantiations: 0
% 4.15/1.82  #Strategies tried      : 1
% 4.15/1.82  
% 4.15/1.82  Timing (in seconds)
% 4.15/1.82  ----------------------
% 4.15/1.82  Preprocessing        : 0.47
% 4.15/1.82  Parsing              : 0.28
% 4.15/1.82  CNF conversion       : 0.02
% 4.15/1.82  Main loop            : 0.53
% 4.15/1.82  Inferencing          : 0.19
% 4.15/1.82  Reduction            : 0.18
% 4.15/1.82  Demodulation         : 0.12
% 4.15/1.82  BG Simplification    : 0.03
% 4.15/1.82  Subsumption          : 0.10
% 4.15/1.82  Abstraction          : 0.03
% 4.15/1.82  MUC search           : 0.00
% 4.15/1.82  Cooper               : 0.00
% 4.15/1.82  Total                : 1.04
% 4.15/1.82  Index Insertion      : 0.00
% 4.15/1.82  Index Deletion       : 0.00
% 4.15/1.82  Index Matching       : 0.00
% 4.15/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
