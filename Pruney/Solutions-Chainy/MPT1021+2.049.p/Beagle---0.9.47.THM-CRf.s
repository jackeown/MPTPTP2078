%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:07 EST 2020

% Result     : Theorem 5.75s
% Output     : CNFRefutation 6.13s
% Verified   : 
% Statistics : Number of formulae       :  178 (8015 expanded)
%              Number of leaves         :   43 (3243 expanded)
%              Depth                    :   22
%              Number of atoms          :  438 (29359 expanded)
%              Number of equality atoms :   60 (1485 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_116,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_xboole_0(C)
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_159,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_138,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_126,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_36,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    ! [A_21,B_22] : m1_subset_1('#skF_1'(A_21,B_22),k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2005,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( r2_relset_1(A_169,B_170,C_171,C_171)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2015,plain,(
    ! [A_173,B_174,C_175] :
      ( r2_relset_1(A_173,B_174,C_175,C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(resolution,[status(thm)],[c_46,c_2005])).

tff(c_2023,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_36,c_2015])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2072,plain,(
    ! [A_186,B_187] :
      ( k2_funct_2(A_186,B_187) = k2_funct_1(B_187)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(k2_zfmisc_1(A_186,A_186)))
      | ~ v3_funct_2(B_187,A_186,A_186)
      | ~ v1_funct_2(B_187,A_186,A_186)
      | ~ v1_funct_1(B_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2082,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2072])).

tff(c_2087,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2082])).

tff(c_2051,plain,(
    ! [A_183,B_184] :
      ( v1_funct_1(k2_funct_2(A_183,B_184))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_zfmisc_1(A_183,A_183)))
      | ~ v3_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2061,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2051])).

tff(c_2066,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2061])).

tff(c_2088,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2087,c_2066])).

tff(c_85,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_98,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_85])).

tff(c_1972,plain,(
    ! [C_159,A_160,B_161] :
      ( v2_funct_1(C_159)
      | ~ v3_funct_2(C_159,A_160,B_161)
      | ~ v1_funct_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1981,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1972])).

tff(c_1986,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1981])).

tff(c_2190,plain,(
    ! [A_199,B_200] :
      ( m1_subset_1(k2_funct_2(A_199,B_200),k1_zfmisc_1(k2_zfmisc_1(A_199,A_199)))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_zfmisc_1(A_199,A_199)))
      | ~ v3_funct_2(B_200,A_199,A_199)
      | ~ v1_funct_2(B_200,A_199,A_199)
      | ~ v1_funct_1(B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2220,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2087,c_2190])).

tff(c_2232,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_2220])).

tff(c_14,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2283,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2232,c_14])).

tff(c_2111,plain,(
    ! [A_193,B_194] :
      ( v3_funct_2(k2_funct_2(A_193,B_194),A_193,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k2_zfmisc_1(A_193,A_193)))
      | ~ v3_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_1(B_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2118,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2111])).

tff(c_2123,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2087,c_2118])).

tff(c_22,plain,(
    ! [C_17,A_15,B_16] :
      ( v2_funct_1(C_17)
      | ~ v3_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2253,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2232,c_22])).

tff(c_2281,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2088,c_2123,c_2253])).

tff(c_2096,plain,(
    ! [A_189,B_190] :
      ( v1_funct_2(k2_funct_2(A_189,B_190),A_189,A_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(k2_zfmisc_1(A_189,A_189)))
      | ~ v3_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_1(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2103,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2096])).

tff(c_2108,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2087,c_2103])).

tff(c_54,plain,(
    ! [A_33,B_34] :
      ( k1_relset_1(A_33,A_33,B_34) = A_33
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_zfmisc_1(A_33,A_33)))
      | ~ v1_funct_2(B_34,A_33,A_33)
      | ~ v1_funct_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2245,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2232,c_54])).

tff(c_2274,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2088,c_2108,c_2245])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2282,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2232,c_16])).

tff(c_2360,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2274,c_2282])).

tff(c_12,plain,(
    ! [A_4] :
      ( k2_funct_1(k2_funct_1(A_4)) = A_4
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_8,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_relat_1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1948,plain,(
    ! [A_157] :
      ( k5_relat_1(A_157,k2_funct_1(A_157)) = k6_partfun1(k1_relat_1(A_157))
      | ~ v2_funct_1(A_157)
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_2655,plain,(
    ! [A_217] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_217))) = k5_relat_1(k2_funct_1(A_217),A_217)
      | ~ v2_funct_1(k2_funct_1(A_217))
      | ~ v1_funct_1(k2_funct_1(A_217))
      | ~ v1_relat_1(k2_funct_1(A_217))
      | ~ v2_funct_1(A_217)
      | ~ v1_funct_1(A_217)
      | ~ v1_relat_1(A_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1948])).

tff(c_2717,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2360,c_2655])).

tff(c_2731,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_64,c_1986,c_2283,c_2088,c_2281,c_2717])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_funct_2(A_18,B_19),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ v3_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2288,plain,(
    ! [A_205,B_202,F_204,C_201,E_203,D_206] :
      ( k1_partfun1(A_205,B_202,C_201,D_206,E_203,F_204) = k5_relat_1(E_203,F_204)
      | ~ m1_subset_1(F_204,k1_zfmisc_1(k2_zfmisc_1(C_201,D_206)))
      | ~ v1_funct_1(F_204)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_205,B_202)))
      | ~ v1_funct_1(E_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2298,plain,(
    ! [A_205,B_202,E_203] :
      ( k1_partfun1(A_205,B_202,'#skF_2','#skF_2',E_203,'#skF_3') = k5_relat_1(E_203,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_205,B_202)))
      | ~ v1_funct_1(E_203) ) ),
    inference(resolution,[status(thm)],[c_58,c_2288])).

tff(c_2330,plain,(
    ! [A_207,B_208,E_209] :
      ( k1_partfun1(A_207,B_208,'#skF_2','#skF_2',E_209,'#skF_3') = k5_relat_1(E_209,'#skF_3')
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_1(E_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2298])).

tff(c_3074,plain,(
    ! [A_222,B_223] :
      ( k1_partfun1(A_222,A_222,'#skF_2','#skF_2',k2_funct_2(A_222,B_223),'#skF_3') = k5_relat_1(k2_funct_2(A_222,B_223),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_222,B_223))
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k2_zfmisc_1(A_222,A_222)))
      | ~ v3_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_1(B_223) ) ),
    inference(resolution,[status(thm)],[c_26,c_2330])).

tff(c_3089,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_3074])).

tff(c_3102,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2088,c_2087,c_2731,c_2087,c_2087,c_3089])).

tff(c_221,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( r2_relset_1(A_76,B_77,C_78,C_78)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_231,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_relset_1(A_80,B_81,C_82,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(resolution,[status(thm)],[c_46,c_221])).

tff(c_239,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_36,c_231])).

tff(c_187,plain,(
    ! [C_64,A_65,B_66] :
      ( v2_funct_1(C_64)
      | ~ v3_funct_2(C_64,A_65,B_66)
      | ~ v1_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_196,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_187])).

tff(c_201,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_196])).

tff(c_288,plain,(
    ! [A_92,B_93] :
      ( k2_funct_2(A_92,B_93) = k2_funct_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v3_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_298,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_288])).

tff(c_303,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_298])).

tff(c_479,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1(k2_funct_2(A_106,B_107),k1_zfmisc_1(k2_zfmisc_1(A_106,A_106)))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_zfmisc_1(A_106,A_106)))
      | ~ v3_funct_2(B_107,A_106,A_106)
      | ~ v1_funct_2(B_107,A_106,A_106)
      | ~ v1_funct_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_509,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_479])).

tff(c_521,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_509])).

tff(c_572,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_521,c_14])).

tff(c_270,plain,(
    ! [A_88,B_89] :
      ( v1_funct_1(k2_funct_2(A_88,B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_zfmisc_1(A_88,A_88)))
      | ~ v3_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_280,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_270])).

tff(c_285,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_280])).

tff(c_304,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_285])).

tff(c_312,plain,(
    ! [A_96,B_97] :
      ( v3_funct_2(k2_funct_2(A_96,B_97),A_96,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_zfmisc_1(A_96,A_96)))
      | ~ v3_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_319,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_312])).

tff(c_324,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_303,c_319])).

tff(c_542,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_521,c_22])).

tff(c_570,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_324,c_542])).

tff(c_326,plain,(
    ! [A_99,B_100] :
      ( v1_funct_2(k2_funct_2(A_99,B_100),A_99,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v3_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_333,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_326])).

tff(c_338,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_303,c_333])).

tff(c_50,plain,(
    ! [A_30,B_31] :
      ( k2_funct_2(A_30,B_31) = k2_funct_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ v3_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_528,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_521,c_50])).

tff(c_557,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_338,c_324,c_528])).

tff(c_731,plain,(
    ! [A_117,B_118] :
      ( v1_relat_1(k2_funct_2(A_117,B_118))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1(A_117,A_117)))
      | ~ v3_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_479,c_14])).

tff(c_734,plain,
    ( v1_relat_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_521,c_731])).

tff(c_750,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_338,c_324,c_557,c_734])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( v1_funct_1(k2_funct_2(A_18,B_19))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ v3_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_531,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_521,c_32])).

tff(c_560,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_338,c_324,c_531])).

tff(c_599,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_560])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( v3_funct_2(k2_funct_2(A_18,B_19),A_18,A_18)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ v3_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_525,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_521,c_28])).

tff(c_554,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_338,c_324,c_525])).

tff(c_598,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_554])).

tff(c_603,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_26])).

tff(c_607,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_338,c_324,c_521,c_603])).

tff(c_790,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_607,c_22])).

tff(c_830,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_598,c_790])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( v1_funct_2(k2_funct_2(A_18,B_19),A_18,A_18)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ v3_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_523,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_521,c_30])).

tff(c_551,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_338,c_324,c_523])).

tff(c_597,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_551])).

tff(c_782,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_607,c_54])).

tff(c_823,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_597,c_782])).

tff(c_831,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_607,c_16])).

tff(c_1245,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_831])).

tff(c_175,plain,(
    ! [A_63] :
      ( k5_relat_1(A_63,k2_funct_1(A_63)) = k6_partfun1(k1_relat_1(A_63))
      | ~ v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_184,plain,(
    ! [A_4] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_4))) = k5_relat_1(k2_funct_1(A_4),A_4)
      | ~ v2_funct_1(k2_funct_1(A_4))
      | ~ v1_funct_1(k2_funct_1(A_4))
      | ~ v1_relat_1(k2_funct_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_175])).

tff(c_776,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_607,c_50])).

tff(c_817,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_597,c_598,c_776])).

tff(c_898,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_817])).

tff(c_904,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_64,c_201,c_303,c_898])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [A_62] :
      ( k5_relat_1(k2_funct_1(A_62),A_62) = k6_partfun1(k2_relat_1(A_62))
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6])).

tff(c_172,plain,(
    ! [A_4] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_4))) = k5_relat_1(A_4,k2_funct_1(A_4))
      | ~ v2_funct_1(k2_funct_1(A_4))
      | ~ v1_funct_1(k2_funct_1(A_4))
      | ~ v1_relat_1(k2_funct_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_163])).

tff(c_941,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_904,c_172])).

tff(c_978,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_599,c_830,c_572,c_904,c_304,c_904,c_570,c_904,c_904,c_941])).

tff(c_1275,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_978])).

tff(c_1292,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_304,c_570,c_750,c_599,c_830,c_1245,c_1275])).

tff(c_1307,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_172])).

tff(c_1353,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_64,c_201,c_572,c_304,c_570,c_1307])).

tff(c_577,plain,(
    ! [A_112,C_108,E_110,B_109,D_113,F_111] :
      ( k1_partfun1(A_112,B_109,C_108,D_113,E_110,F_111) = k5_relat_1(E_110,F_111)
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_108,D_113)))
      | ~ v1_funct_1(F_111)
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_109)))
      | ~ v1_funct_1(E_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_579,plain,(
    ! [A_112,B_109,E_110] :
      ( k1_partfun1(A_112,B_109,'#skF_2','#skF_2',E_110,k2_funct_1('#skF_3')) = k5_relat_1(E_110,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_109)))
      | ~ v1_funct_1(E_110) ) ),
    inference(resolution,[status(thm)],[c_521,c_577])).

tff(c_1856,plain,(
    ! [A_148,B_149,E_150] :
      ( k1_partfun1(A_148,B_149,'#skF_2','#skF_2',E_150,k2_funct_1('#skF_3')) = k5_relat_1(E_150,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149)))
      | ~ v1_funct_1(E_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_579])).

tff(c_1889,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1856])).

tff(c_1906,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1353,c_1889])).

tff(c_56,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_127,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_305,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_127])).

tff(c_1907,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1906,c_305])).

tff(c_1910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_1907])).

tff(c_1911,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2090,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2087,c_1911])).

tff(c_3150,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3102,c_2090])).

tff(c_3153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2023,c_3150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.75/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.20  
% 5.75/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.21  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.75/2.21  
% 5.75/2.21  %Foreground sorts:
% 5.75/2.21  
% 5.75/2.21  
% 5.75/2.21  %Background operators:
% 5.75/2.21  
% 5.75/2.21  
% 5.75/2.21  %Foreground operators:
% 5.75/2.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.75/2.21  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.75/2.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.75/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.75/2.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.75/2.21  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.75/2.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.21  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.75/2.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.75/2.21  tff('#skF_2', type, '#skF_2': $i).
% 5.75/2.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.75/2.21  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.21  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.75/2.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.75/2.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.75/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.21  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.75/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.75/2.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.75/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.75/2.21  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.75/2.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.75/2.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.75/2.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.75/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.21  
% 6.13/2.25  tff(f_105, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.13/2.25  tff(f_116, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_xboole_0(C)) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_relset_1)).
% 6.13/2.25  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.13/2.25  tff(f_159, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 6.13/2.25  tff(f_136, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.13/2.25  tff(f_101, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.13/2.25  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.13/2.25  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.13/2.25  tff(f_146, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 6.13/2.25  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.13/2.25  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 6.13/2.25  tff(f_138, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.13/2.25  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.13/2.25  tff(f_126, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.13/2.25  tff(c_36, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.13/2.25  tff(c_46, plain, (![A_21, B_22]: (m1_subset_1('#skF_1'(A_21, B_22), k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.13/2.25  tff(c_2005, plain, (![A_169, B_170, C_171, D_172]: (r2_relset_1(A_169, B_170, C_171, C_171) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.13/2.25  tff(c_2015, plain, (![A_173, B_174, C_175]: (r2_relset_1(A_173, B_174, C_175, C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(resolution, [status(thm)], [c_46, c_2005])).
% 6.13/2.25  tff(c_2023, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_36, c_2015])).
% 6.13/2.25  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.13/2.25  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.13/2.25  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.13/2.25  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.13/2.25  tff(c_2072, plain, (![A_186, B_187]: (k2_funct_2(A_186, B_187)=k2_funct_1(B_187) | ~m1_subset_1(B_187, k1_zfmisc_1(k2_zfmisc_1(A_186, A_186))) | ~v3_funct_2(B_187, A_186, A_186) | ~v1_funct_2(B_187, A_186, A_186) | ~v1_funct_1(B_187))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.13/2.25  tff(c_2082, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2072])).
% 6.13/2.25  tff(c_2087, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2082])).
% 6.13/2.25  tff(c_2051, plain, (![A_183, B_184]: (v1_funct_1(k2_funct_2(A_183, B_184)) | ~m1_subset_1(B_184, k1_zfmisc_1(k2_zfmisc_1(A_183, A_183))) | ~v3_funct_2(B_184, A_183, A_183) | ~v1_funct_2(B_184, A_183, A_183) | ~v1_funct_1(B_184))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.13/2.25  tff(c_2061, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2051])).
% 6.13/2.25  tff(c_2066, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2061])).
% 6.13/2.25  tff(c_2088, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2087, c_2066])).
% 6.13/2.25  tff(c_85, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.13/2.25  tff(c_98, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_85])).
% 6.13/2.25  tff(c_1972, plain, (![C_159, A_160, B_161]: (v2_funct_1(C_159) | ~v3_funct_2(C_159, A_160, B_161) | ~v1_funct_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.13/2.25  tff(c_1981, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1972])).
% 6.13/2.25  tff(c_1986, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1981])).
% 6.13/2.25  tff(c_2190, plain, (![A_199, B_200]: (m1_subset_1(k2_funct_2(A_199, B_200), k1_zfmisc_1(k2_zfmisc_1(A_199, A_199))) | ~m1_subset_1(B_200, k1_zfmisc_1(k2_zfmisc_1(A_199, A_199))) | ~v3_funct_2(B_200, A_199, A_199) | ~v1_funct_2(B_200, A_199, A_199) | ~v1_funct_1(B_200))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.13/2.25  tff(c_2220, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2087, c_2190])).
% 6.13/2.25  tff(c_2232, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_2220])).
% 6.13/2.25  tff(c_14, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.13/2.26  tff(c_2283, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2232, c_14])).
% 6.13/2.26  tff(c_2111, plain, (![A_193, B_194]: (v3_funct_2(k2_funct_2(A_193, B_194), A_193, A_193) | ~m1_subset_1(B_194, k1_zfmisc_1(k2_zfmisc_1(A_193, A_193))) | ~v3_funct_2(B_194, A_193, A_193) | ~v1_funct_2(B_194, A_193, A_193) | ~v1_funct_1(B_194))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.13/2.26  tff(c_2118, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2111])).
% 6.13/2.26  tff(c_2123, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2087, c_2118])).
% 6.13/2.26  tff(c_22, plain, (![C_17, A_15, B_16]: (v2_funct_1(C_17) | ~v3_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.13/2.26  tff(c_2253, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2232, c_22])).
% 6.13/2.26  tff(c_2281, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2088, c_2123, c_2253])).
% 6.13/2.26  tff(c_2096, plain, (![A_189, B_190]: (v1_funct_2(k2_funct_2(A_189, B_190), A_189, A_189) | ~m1_subset_1(B_190, k1_zfmisc_1(k2_zfmisc_1(A_189, A_189))) | ~v3_funct_2(B_190, A_189, A_189) | ~v1_funct_2(B_190, A_189, A_189) | ~v1_funct_1(B_190))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.13/2.26  tff(c_2103, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2096])).
% 6.13/2.26  tff(c_2108, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2087, c_2103])).
% 6.13/2.26  tff(c_54, plain, (![A_33, B_34]: (k1_relset_1(A_33, A_33, B_34)=A_33 | ~m1_subset_1(B_34, k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))) | ~v1_funct_2(B_34, A_33, A_33) | ~v1_funct_1(B_34))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.13/2.26  tff(c_2245, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2232, c_54])).
% 6.13/2.26  tff(c_2274, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2088, c_2108, c_2245])).
% 6.13/2.26  tff(c_16, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.13/2.26  tff(c_2282, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2232, c_16])).
% 6.13/2.26  tff(c_2360, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2274, c_2282])).
% 6.13/2.26  tff(c_12, plain, (![A_4]: (k2_funct_1(k2_funct_1(A_4))=A_4 | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.13/2.26  tff(c_52, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.13/2.26  tff(c_8, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_relat_1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.13/2.26  tff(c_1948, plain, (![A_157]: (k5_relat_1(A_157, k2_funct_1(A_157))=k6_partfun1(k1_relat_1(A_157)) | ~v2_funct_1(A_157) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8])).
% 6.13/2.26  tff(c_2655, plain, (![A_217]: (k6_partfun1(k1_relat_1(k2_funct_1(A_217)))=k5_relat_1(k2_funct_1(A_217), A_217) | ~v2_funct_1(k2_funct_1(A_217)) | ~v1_funct_1(k2_funct_1(A_217)) | ~v1_relat_1(k2_funct_1(A_217)) | ~v2_funct_1(A_217) | ~v1_funct_1(A_217) | ~v1_relat_1(A_217))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1948])).
% 6.13/2.26  tff(c_2717, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2360, c_2655])).
% 6.13/2.26  tff(c_2731, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_64, c_1986, c_2283, c_2088, c_2281, c_2717])).
% 6.13/2.26  tff(c_26, plain, (![A_18, B_19]: (m1_subset_1(k2_funct_2(A_18, B_19), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~v3_funct_2(B_19, A_18, A_18) | ~v1_funct_2(B_19, A_18, A_18) | ~v1_funct_1(B_19))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.13/2.26  tff(c_2288, plain, (![A_205, B_202, F_204, C_201, E_203, D_206]: (k1_partfun1(A_205, B_202, C_201, D_206, E_203, F_204)=k5_relat_1(E_203, F_204) | ~m1_subset_1(F_204, k1_zfmisc_1(k2_zfmisc_1(C_201, D_206))) | ~v1_funct_1(F_204) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_205, B_202))) | ~v1_funct_1(E_203))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.26  tff(c_2298, plain, (![A_205, B_202, E_203]: (k1_partfun1(A_205, B_202, '#skF_2', '#skF_2', E_203, '#skF_3')=k5_relat_1(E_203, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_205, B_202))) | ~v1_funct_1(E_203))), inference(resolution, [status(thm)], [c_58, c_2288])).
% 6.13/2.26  tff(c_2330, plain, (![A_207, B_208, E_209]: (k1_partfun1(A_207, B_208, '#skF_2', '#skF_2', E_209, '#skF_3')=k5_relat_1(E_209, '#skF_3') | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_1(E_209))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2298])).
% 6.13/2.26  tff(c_3074, plain, (![A_222, B_223]: (k1_partfun1(A_222, A_222, '#skF_2', '#skF_2', k2_funct_2(A_222, B_223), '#skF_3')=k5_relat_1(k2_funct_2(A_222, B_223), '#skF_3') | ~v1_funct_1(k2_funct_2(A_222, B_223)) | ~m1_subset_1(B_223, k1_zfmisc_1(k2_zfmisc_1(A_222, A_222))) | ~v3_funct_2(B_223, A_222, A_222) | ~v1_funct_2(B_223, A_222, A_222) | ~v1_funct_1(B_223))), inference(resolution, [status(thm)], [c_26, c_2330])).
% 6.13/2.26  tff(c_3089, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_3074])).
% 6.13/2.26  tff(c_3102, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2088, c_2087, c_2731, c_2087, c_2087, c_3089])).
% 6.13/2.26  tff(c_221, plain, (![A_76, B_77, C_78, D_79]: (r2_relset_1(A_76, B_77, C_78, C_78) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.13/2.26  tff(c_231, plain, (![A_80, B_81, C_82]: (r2_relset_1(A_80, B_81, C_82, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(resolution, [status(thm)], [c_46, c_221])).
% 6.13/2.26  tff(c_239, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_36, c_231])).
% 6.13/2.26  tff(c_187, plain, (![C_64, A_65, B_66]: (v2_funct_1(C_64) | ~v3_funct_2(C_64, A_65, B_66) | ~v1_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.13/2.26  tff(c_196, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_187])).
% 6.13/2.26  tff(c_201, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_196])).
% 6.13/2.26  tff(c_288, plain, (![A_92, B_93]: (k2_funct_2(A_92, B_93)=k2_funct_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v3_funct_2(B_93, A_92, A_92) | ~v1_funct_2(B_93, A_92, A_92) | ~v1_funct_1(B_93))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.13/2.26  tff(c_298, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_288])).
% 6.13/2.26  tff(c_303, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_298])).
% 6.13/2.26  tff(c_479, plain, (![A_106, B_107]: (m1_subset_1(k2_funct_2(A_106, B_107), k1_zfmisc_1(k2_zfmisc_1(A_106, A_106))) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_zfmisc_1(A_106, A_106))) | ~v3_funct_2(B_107, A_106, A_106) | ~v1_funct_2(B_107, A_106, A_106) | ~v1_funct_1(B_107))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.13/2.26  tff(c_509, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_303, c_479])).
% 6.13/2.26  tff(c_521, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_509])).
% 6.13/2.26  tff(c_572, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_521, c_14])).
% 6.13/2.26  tff(c_270, plain, (![A_88, B_89]: (v1_funct_1(k2_funct_2(A_88, B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(k2_zfmisc_1(A_88, A_88))) | ~v3_funct_2(B_89, A_88, A_88) | ~v1_funct_2(B_89, A_88, A_88) | ~v1_funct_1(B_89))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.13/2.26  tff(c_280, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_270])).
% 6.13/2.26  tff(c_285, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_280])).
% 6.13/2.26  tff(c_304, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_285])).
% 6.13/2.26  tff(c_312, plain, (![A_96, B_97]: (v3_funct_2(k2_funct_2(A_96, B_97), A_96, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))) | ~v3_funct_2(B_97, A_96, A_96) | ~v1_funct_2(B_97, A_96, A_96) | ~v1_funct_1(B_97))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.13/2.26  tff(c_319, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_312])).
% 6.13/2.26  tff(c_324, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_303, c_319])).
% 6.13/2.26  tff(c_542, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_521, c_22])).
% 6.13/2.26  tff(c_570, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_324, c_542])).
% 6.13/2.26  tff(c_326, plain, (![A_99, B_100]: (v1_funct_2(k2_funct_2(A_99, B_100), A_99, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v3_funct_2(B_100, A_99, A_99) | ~v1_funct_2(B_100, A_99, A_99) | ~v1_funct_1(B_100))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.13/2.26  tff(c_333, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_326])).
% 6.13/2.26  tff(c_338, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_303, c_333])).
% 6.13/2.26  tff(c_50, plain, (![A_30, B_31]: (k2_funct_2(A_30, B_31)=k2_funct_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~v3_funct_2(B_31, A_30, A_30) | ~v1_funct_2(B_31, A_30, A_30) | ~v1_funct_1(B_31))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.13/2.26  tff(c_528, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_521, c_50])).
% 6.13/2.26  tff(c_557, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_338, c_324, c_528])).
% 6.13/2.26  tff(c_731, plain, (![A_117, B_118]: (v1_relat_1(k2_funct_2(A_117, B_118)) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1(A_117, A_117))) | ~v3_funct_2(B_118, A_117, A_117) | ~v1_funct_2(B_118, A_117, A_117) | ~v1_funct_1(B_118))), inference(resolution, [status(thm)], [c_479, c_14])).
% 6.13/2.26  tff(c_734, plain, (v1_relat_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_521, c_731])).
% 6.13/2.26  tff(c_750, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_338, c_324, c_557, c_734])).
% 6.13/2.26  tff(c_32, plain, (![A_18, B_19]: (v1_funct_1(k2_funct_2(A_18, B_19)) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~v3_funct_2(B_19, A_18, A_18) | ~v1_funct_2(B_19, A_18, A_18) | ~v1_funct_1(B_19))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.13/2.26  tff(c_531, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_521, c_32])).
% 6.13/2.26  tff(c_560, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_338, c_324, c_531])).
% 6.13/2.26  tff(c_599, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_557, c_560])).
% 6.13/2.26  tff(c_28, plain, (![A_18, B_19]: (v3_funct_2(k2_funct_2(A_18, B_19), A_18, A_18) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~v3_funct_2(B_19, A_18, A_18) | ~v1_funct_2(B_19, A_18, A_18) | ~v1_funct_1(B_19))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.13/2.26  tff(c_525, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_521, c_28])).
% 6.13/2.26  tff(c_554, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_304, c_338, c_324, c_525])).
% 6.13/2.26  tff(c_598, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_557, c_554])).
% 6.13/2.26  tff(c_603, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_557, c_26])).
% 6.13/2.26  tff(c_607, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_338, c_324, c_521, c_603])).
% 6.13/2.26  tff(c_790, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_607, c_22])).
% 6.13/2.26  tff(c_830, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_599, c_598, c_790])).
% 6.13/2.26  tff(c_30, plain, (![A_18, B_19]: (v1_funct_2(k2_funct_2(A_18, B_19), A_18, A_18) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~v3_funct_2(B_19, A_18, A_18) | ~v1_funct_2(B_19, A_18, A_18) | ~v1_funct_1(B_19))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.13/2.26  tff(c_523, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_521, c_30])).
% 6.13/2.26  tff(c_551, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_304, c_338, c_324, c_523])).
% 6.13/2.26  tff(c_597, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_557, c_551])).
% 6.13/2.26  tff(c_782, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_607, c_54])).
% 6.13/2.26  tff(c_823, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_599, c_597, c_782])).
% 6.13/2.26  tff(c_831, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_607, c_16])).
% 6.13/2.26  tff(c_1245, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_823, c_831])).
% 6.13/2.26  tff(c_175, plain, (![A_63]: (k5_relat_1(A_63, k2_funct_1(A_63))=k6_partfun1(k1_relat_1(A_63)) | ~v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8])).
% 6.13/2.26  tff(c_184, plain, (![A_4]: (k6_partfun1(k1_relat_1(k2_funct_1(A_4)))=k5_relat_1(k2_funct_1(A_4), A_4) | ~v2_funct_1(k2_funct_1(A_4)) | ~v1_funct_1(k2_funct_1(A_4)) | ~v1_relat_1(k2_funct_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(superposition, [status(thm), theory('equality')], [c_12, c_175])).
% 6.13/2.26  tff(c_776, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_607, c_50])).
% 6.13/2.26  tff(c_817, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_599, c_597, c_598, c_776])).
% 6.13/2.26  tff(c_898, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_817])).
% 6.13/2.26  tff(c_904, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_64, c_201, c_303, c_898])).
% 6.13/2.26  tff(c_6, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.13/2.26  tff(c_163, plain, (![A_62]: (k5_relat_1(k2_funct_1(A_62), A_62)=k6_partfun1(k2_relat_1(A_62)) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6])).
% 6.13/2.26  tff(c_172, plain, (![A_4]: (k6_partfun1(k2_relat_1(k2_funct_1(A_4)))=k5_relat_1(A_4, k2_funct_1(A_4)) | ~v2_funct_1(k2_funct_1(A_4)) | ~v1_funct_1(k2_funct_1(A_4)) | ~v1_relat_1(k2_funct_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(superposition, [status(thm), theory('equality')], [c_12, c_163])).
% 6.13/2.26  tff(c_941, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_904, c_172])).
% 6.13/2.26  tff(c_978, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_750, c_599, c_830, c_572, c_904, c_304, c_904, c_570, c_904, c_904, c_941])).
% 6.13/2.26  tff(c_1275, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_978])).
% 6.13/2.26  tff(c_1292, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_572, c_304, c_570, c_750, c_599, c_830, c_1245, c_1275])).
% 6.13/2.26  tff(c_1307, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1292, c_172])).
% 6.13/2.26  tff(c_1353, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_64, c_201, c_572, c_304, c_570, c_1307])).
% 6.13/2.26  tff(c_577, plain, (![A_112, C_108, E_110, B_109, D_113, F_111]: (k1_partfun1(A_112, B_109, C_108, D_113, E_110, F_111)=k5_relat_1(E_110, F_111) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_108, D_113))) | ~v1_funct_1(F_111) | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_109))) | ~v1_funct_1(E_110))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.26  tff(c_579, plain, (![A_112, B_109, E_110]: (k1_partfun1(A_112, B_109, '#skF_2', '#skF_2', E_110, k2_funct_1('#skF_3'))=k5_relat_1(E_110, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_109))) | ~v1_funct_1(E_110))), inference(resolution, [status(thm)], [c_521, c_577])).
% 6.13/2.26  tff(c_1856, plain, (![A_148, B_149, E_150]: (k1_partfun1(A_148, B_149, '#skF_2', '#skF_2', E_150, k2_funct_1('#skF_3'))=k5_relat_1(E_150, k2_funct_1('#skF_3')) | ~m1_subset_1(E_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))) | ~v1_funct_1(E_150))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_579])).
% 6.13/2.26  tff(c_1889, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1856])).
% 6.13/2.26  tff(c_1906, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1353, c_1889])).
% 6.13/2.26  tff(c_56, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.13/2.26  tff(c_127, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 6.13/2.26  tff(c_305, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_127])).
% 6.13/2.26  tff(c_1907, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1906, c_305])).
% 6.13/2.26  tff(c_1910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_239, c_1907])).
% 6.13/2.26  tff(c_1911, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 6.13/2.26  tff(c_2090, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2087, c_1911])).
% 6.13/2.26  tff(c_3150, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3102, c_2090])).
% 6.13/2.26  tff(c_3153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2023, c_3150])).
% 6.13/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.13/2.26  
% 6.13/2.26  Inference rules
% 6.13/2.26  ----------------------
% 6.13/2.26  #Ref     : 0
% 6.13/2.26  #Sup     : 752
% 6.13/2.26  #Fact    : 0
% 6.13/2.26  #Define  : 0
% 6.13/2.26  #Split   : 3
% 6.13/2.26  #Chain   : 0
% 6.13/2.26  #Close   : 0
% 6.13/2.26  
% 6.13/2.26  Ordering : KBO
% 6.13/2.26  
% 6.13/2.26  Simplification rules
% 6.13/2.26  ----------------------
% 6.13/2.26  #Subsume      : 78
% 6.13/2.26  #Demod        : 1278
% 6.13/2.26  #Tautology    : 322
% 6.13/2.26  #SimpNegUnit  : 0
% 6.13/2.26  #BackRed      : 33
% 6.13/2.26  
% 6.13/2.26  #Partial instantiations: 0
% 6.13/2.26  #Strategies tried      : 1
% 6.13/2.26  
% 6.13/2.26  Timing (in seconds)
% 6.13/2.26  ----------------------
% 6.13/2.26  Preprocessing        : 0.36
% 6.13/2.26  Parsing              : 0.20
% 6.13/2.26  CNF conversion       : 0.02
% 6.13/2.26  Main loop            : 1.00
% 6.13/2.26  Inferencing          : 0.33
% 6.13/2.26  Reduction            : 0.39
% 6.13/2.26  Demodulation         : 0.30
% 6.13/2.26  BG Simplification    : 0.04
% 6.13/2.26  Subsumption          : 0.17
% 6.13/2.26  Abstraction          : 0.04
% 6.13/2.26  MUC search           : 0.00
% 6.13/2.26  Cooper               : 0.00
% 6.13/2.26  Total                : 1.44
% 6.13/2.27  Index Insertion      : 0.00
% 6.13/2.27  Index Deletion       : 0.00
% 6.13/2.27  Index Matching       : 0.00
% 6.13/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
