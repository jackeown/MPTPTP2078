%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:22 EST 2020

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 299 expanded)
%              Number of leaves         :   40 ( 125 expanded)
%              Depth                    :   11
%              Number of atoms          :  271 (1252 expanded)
%              Number of equality atoms :  103 ( 435 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_172,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_130,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_74,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_100,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_139,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_150,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_139])).

tff(c_218,plain,(
    ! [B_77,A_78,C_79] :
      ( k1_xboole_0 = B_77
      | k1_relset_1(A_78,B_77,C_79) = A_78
      | ~ v1_funct_2(C_79,A_78,B_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_224,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_218])).

tff(c_232,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_150,c_224])).

tff(c_233,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_232])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_89,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_95,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_89])).

tff(c_104,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_95])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_98,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_89])).

tff(c_107,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_98])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_151,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_139])).

tff(c_227,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_218])).

tff(c_236,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_151,c_227])).

tff(c_237,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_236])).

tff(c_40,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_relat_1(k1_relat_1(A_10)) != k5_relat_1(A_10,B_12)
      | k2_relat_1(A_10) != k1_relat_1(B_12)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1459,plain,(
    ! [A_170,B_171] :
      ( k2_funct_1(A_170) = B_171
      | k6_partfun1(k1_relat_1(A_170)) != k5_relat_1(A_170,B_171)
      | k2_relat_1(A_170) != k1_relat_1(B_171)
      | ~ v2_funct_1(A_170)
      | ~ v1_funct_1(B_171)
      | ~ v1_relat_1(B_171)
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_12])).

tff(c_1461,plain,(
    ! [B_171] :
      ( k2_funct_1('#skF_3') = B_171
      | k5_relat_1('#skF_3',B_171) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_171)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_171)
      | ~ v1_relat_1(B_171)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_1459])).

tff(c_1479,plain,(
    ! [B_173] :
      ( k2_funct_1('#skF_3') = B_173
      | k5_relat_1('#skF_3',B_173) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_173)
      | ~ v1_funct_1(B_173)
      | ~ v1_relat_1(B_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_70,c_54,c_1461])).

tff(c_1488,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_1479])).

tff(c_1498,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_233,c_1488])).

tff(c_1499,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1498])).

tff(c_1501,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1499])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1823,plain,(
    ! [C_186,B_187,A_188] :
      ( v1_funct_2(k2_funct_1(C_186),B_187,A_188)
      | k2_relset_1(A_188,B_187,C_186) != B_187
      | ~ v2_funct_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_188,B_187)))
      | ~ v1_funct_2(C_186,A_188,B_187)
      | ~ v1_funct_1(C_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1847,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1823])).

tff(c_1859,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_1847])).

tff(c_2189,plain,(
    ! [C_203,B_204,A_205] :
      ( m1_subset_1(k2_funct_1(C_203),k1_zfmisc_1(k2_zfmisc_1(B_204,A_205)))
      | k2_relset_1(A_205,B_204,C_203) != B_204
      | ~ v2_funct_1(C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_205,B_204)))
      | ~ v1_funct_2(C_203,A_205,B_204)
      | ~ v1_funct_1(C_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_16,plain,(
    ! [A_19,B_20,C_21] :
      ( k1_relset_1(A_19,B_20,C_21) = k1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3358,plain,(
    ! [B_276,A_277,C_278] :
      ( k1_relset_1(B_276,A_277,k2_funct_1(C_278)) = k1_relat_1(k2_funct_1(C_278))
      | k2_relset_1(A_277,B_276,C_278) != B_276
      | ~ v2_funct_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_277,B_276)))
      | ~ v1_funct_2(C_278,A_277,B_276)
      | ~ v1_funct_1(C_278) ) ),
    inference(resolution,[status(thm)],[c_2189,c_16])).

tff(c_3406,plain,
    ( k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3358])).

tff(c_3426,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_3406])).

tff(c_36,plain,(
    ! [B_34,A_33,C_35] :
      ( k1_xboole_0 = B_34
      | k1_relset_1(A_33,B_34,C_35) = A_33
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4287,plain,(
    ! [A_326,B_327,C_328] :
      ( k1_xboole_0 = A_326
      | k1_relset_1(B_327,A_326,k2_funct_1(C_328)) = B_327
      | ~ v1_funct_2(k2_funct_1(C_328),B_327,A_326)
      | k2_relset_1(A_326,B_327,C_328) != B_327
      | ~ v2_funct_1(C_328)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ v1_funct_2(C_328,A_326,B_327)
      | ~ v1_funct_1(C_328) ) ),
    inference(resolution,[status(thm)],[c_2189,c_36])).

tff(c_4344,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_4287])).

tff(c_4384,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_1859,c_3426,c_4344])).

tff(c_4385,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4384])).

tff(c_10,plain,(
    ! [A_9] :
      ( k1_relat_1(k2_funct_1(A_9)) = k2_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4394,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4385,c_10])).

tff(c_4405,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_70,c_54,c_4394])).

tff(c_4407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1501,c_4405])).

tff(c_4408,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1499])).

tff(c_335,plain,(
    ! [E_94,D_96,A_92,F_95,B_97,C_93] :
      ( k4_relset_1(A_92,B_97,C_93,D_96,E_94,F_95) = k5_relat_1(E_94,F_95)
      | ~ m1_subset_1(F_95,k1_zfmisc_1(k2_zfmisc_1(C_93,D_96)))
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_346,plain,(
    ! [A_98,B_99,E_100] :
      ( k4_relset_1(A_98,B_99,'#skF_2','#skF_1',E_100,'#skF_4') = k5_relat_1(E_100,'#skF_4')
      | ~ m1_subset_1(E_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(resolution,[status(thm)],[c_60,c_335])).

tff(c_358,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_346])).

tff(c_460,plain,(
    ! [D_115,E_117,C_119,A_118,B_116,F_114] :
      ( m1_subset_1(k4_relset_1(A_118,B_116,C_119,D_115,E_117,F_114),k1_zfmisc_1(k2_zfmisc_1(A_118,D_115)))
      | ~ m1_subset_1(F_114,k1_zfmisc_1(k2_zfmisc_1(C_119,D_115)))
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_517,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_460])).

tff(c_547,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_517])).

tff(c_993,plain,(
    ! [B_133,F_130,D_132,A_131,C_134,E_135] :
      ( k1_partfun1(A_131,B_133,C_134,D_132,E_135,F_130) = k5_relat_1(E_135,F_130)
      | ~ m1_subset_1(F_130,k1_zfmisc_1(k2_zfmisc_1(C_134,D_132)))
      | ~ v1_funct_1(F_130)
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_131,B_133)))
      | ~ v1_funct_1(E_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1013,plain,(
    ! [A_131,B_133,E_135] :
      ( k1_partfun1(A_131,B_133,'#skF_2','#skF_1',E_135,'#skF_4') = k5_relat_1(E_135,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_131,B_133)))
      | ~ v1_funct_1(E_135) ) ),
    inference(resolution,[status(thm)],[c_60,c_993])).

tff(c_1303,plain,(
    ! [A_148,B_149,E_150] :
      ( k1_partfun1(A_148,B_149,'#skF_2','#skF_1',E_150,'#skF_4') = k5_relat_1(E_150,'#skF_4')
      | ~ m1_subset_1(E_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149)))
      | ~ v1_funct_1(E_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1013])).

tff(c_1342,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1303])).

tff(c_1359,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1342])).

tff(c_24,plain,(
    ! [A_32] : m1_subset_1(k6_relat_1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_71,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_24])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_269,plain,(
    ! [D_81,C_82,A_83,B_84] :
      ( D_81 = C_82
      | ~ r2_relset_1(A_83,B_84,C_82,D_81)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_277,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_269])).

tff(c_292,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_277])).

tff(c_315,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_1364,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_315])).

tff(c_1368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_1364])).

tff(c_1369,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_5147,plain,(
    ! [A_358,C_361,B_360,F_357,D_359,E_362] :
      ( k1_partfun1(A_358,B_360,C_361,D_359,E_362,F_357) = k5_relat_1(E_362,F_357)
      | ~ m1_subset_1(F_357,k1_zfmisc_1(k2_zfmisc_1(C_361,D_359)))
      | ~ v1_funct_1(F_357)
      | ~ m1_subset_1(E_362,k1_zfmisc_1(k2_zfmisc_1(A_358,B_360)))
      | ~ v1_funct_1(E_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_5171,plain,(
    ! [A_358,B_360,E_362] :
      ( k1_partfun1(A_358,B_360,'#skF_2','#skF_1',E_362,'#skF_4') = k5_relat_1(E_362,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_362,k1_zfmisc_1(k2_zfmisc_1(A_358,B_360)))
      | ~ v1_funct_1(E_362) ) ),
    inference(resolution,[status(thm)],[c_60,c_5147])).

tff(c_5303,plain,(
    ! [A_370,B_371,E_372] :
      ( k1_partfun1(A_370,B_371,'#skF_2','#skF_1',E_372,'#skF_4') = k5_relat_1(E_372,'#skF_4')
      | ~ m1_subset_1(E_372,k1_zfmisc_1(k2_zfmisc_1(A_370,B_371)))
      | ~ v1_funct_1(E_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5171])).

tff(c_5342,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_5303])).

tff(c_5359,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1369,c_5342])).

tff(c_5361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4408,c_5359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.31/2.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.54  
% 7.31/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.54  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.31/2.54  
% 7.31/2.54  %Foreground sorts:
% 7.31/2.54  
% 7.31/2.54  
% 7.31/2.54  %Background operators:
% 7.31/2.54  
% 7.31/2.54  
% 7.31/2.54  %Foreground operators:
% 7.31/2.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.31/2.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.31/2.54  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.31/2.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.31/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.54  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.31/2.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.31/2.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.31/2.54  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.31/2.54  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.31/2.54  tff('#skF_2', type, '#skF_2': $i).
% 7.31/2.54  tff('#skF_3', type, '#skF_3': $i).
% 7.31/2.54  tff('#skF_1', type, '#skF_1': $i).
% 7.31/2.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.31/2.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.31/2.54  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.31/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.31/2.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.31/2.54  tff('#skF_4', type, '#skF_4': $i).
% 7.31/2.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.31/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.31/2.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.31/2.54  
% 7.31/2.56  tff(f_172, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.31/2.56  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.31/2.56  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.31/2.56  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.31/2.56  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.31/2.56  tff(f_130, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.31/2.56  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 7.31/2.56  tff(f_146, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 7.31/2.56  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.31/2.56  tff(f_90, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 7.31/2.56  tff(f_80, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 7.31/2.56  tff(f_128, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.31/2.56  tff(f_100, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.31/2.56  tff(f_98, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.31/2.56  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.56  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.56  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.56  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.56  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.56  tff(c_139, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.31/2.56  tff(c_150, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_139])).
% 7.31/2.56  tff(c_218, plain, (![B_77, A_78, C_79]: (k1_xboole_0=B_77 | k1_relset_1(A_78, B_77, C_79)=A_78 | ~v1_funct_2(C_79, A_78, B_77) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.31/2.56  tff(c_224, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_218])).
% 7.31/2.56  tff(c_232, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_150, c_224])).
% 7.31/2.56  tff(c_233, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_232])).
% 7.31/2.56  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.31/2.56  tff(c_89, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.31/2.56  tff(c_95, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_89])).
% 7.31/2.56  tff(c_104, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_95])).
% 7.31/2.56  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.56  tff(c_98, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_89])).
% 7.31/2.56  tff(c_107, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_98])).
% 7.31/2.56  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.56  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.56  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.56  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.56  tff(c_151, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_139])).
% 7.31/2.56  tff(c_227, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_218])).
% 7.31/2.56  tff(c_236, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_151, c_227])).
% 7.31/2.56  tff(c_237, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_236])).
% 7.31/2.56  tff(c_40, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.31/2.56  tff(c_12, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_relat_1(k1_relat_1(A_10))!=k5_relat_1(A_10, B_12) | k2_relat_1(A_10)!=k1_relat_1(B_12) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.31/2.56  tff(c_1459, plain, (![A_170, B_171]: (k2_funct_1(A_170)=B_171 | k6_partfun1(k1_relat_1(A_170))!=k5_relat_1(A_170, B_171) | k2_relat_1(A_170)!=k1_relat_1(B_171) | ~v2_funct_1(A_170) | ~v1_funct_1(B_171) | ~v1_relat_1(B_171) | ~v1_funct_1(A_170) | ~v1_relat_1(A_170))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_12])).
% 7.31/2.56  tff(c_1461, plain, (![B_171]: (k2_funct_1('#skF_3')=B_171 | k5_relat_1('#skF_3', B_171)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_171) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_171) | ~v1_relat_1(B_171) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_237, c_1459])).
% 7.31/2.56  tff(c_1479, plain, (![B_173]: (k2_funct_1('#skF_3')=B_173 | k5_relat_1('#skF_3', B_173)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_173) | ~v1_funct_1(B_173) | ~v1_relat_1(B_173))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_70, c_54, c_1461])).
% 7.31/2.56  tff(c_1488, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_104, c_1479])).
% 7.31/2.56  tff(c_1498, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_233, c_1488])).
% 7.31/2.56  tff(c_1499, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_1498])).
% 7.31/2.56  tff(c_1501, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_1499])).
% 7.31/2.56  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.56  tff(c_1823, plain, (![C_186, B_187, A_188]: (v1_funct_2(k2_funct_1(C_186), B_187, A_188) | k2_relset_1(A_188, B_187, C_186)!=B_187 | ~v2_funct_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_188, B_187))) | ~v1_funct_2(C_186, A_188, B_187) | ~v1_funct_1(C_186))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.31/2.56  tff(c_1847, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1823])).
% 7.31/2.56  tff(c_1859, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_1847])).
% 7.31/2.56  tff(c_2189, plain, (![C_203, B_204, A_205]: (m1_subset_1(k2_funct_1(C_203), k1_zfmisc_1(k2_zfmisc_1(B_204, A_205))) | k2_relset_1(A_205, B_204, C_203)!=B_204 | ~v2_funct_1(C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_205, B_204))) | ~v1_funct_2(C_203, A_205, B_204) | ~v1_funct_1(C_203))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.31/2.56  tff(c_16, plain, (![A_19, B_20, C_21]: (k1_relset_1(A_19, B_20, C_21)=k1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.31/2.56  tff(c_3358, plain, (![B_276, A_277, C_278]: (k1_relset_1(B_276, A_277, k2_funct_1(C_278))=k1_relat_1(k2_funct_1(C_278)) | k2_relset_1(A_277, B_276, C_278)!=B_276 | ~v2_funct_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_277, B_276))) | ~v1_funct_2(C_278, A_277, B_276) | ~v1_funct_1(C_278))), inference(resolution, [status(thm)], [c_2189, c_16])).
% 7.31/2.56  tff(c_3406, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3358])).
% 7.31/2.56  tff(c_3426, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_3406])).
% 7.31/2.56  tff(c_36, plain, (![B_34, A_33, C_35]: (k1_xboole_0=B_34 | k1_relset_1(A_33, B_34, C_35)=A_33 | ~v1_funct_2(C_35, A_33, B_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.31/2.56  tff(c_4287, plain, (![A_326, B_327, C_328]: (k1_xboole_0=A_326 | k1_relset_1(B_327, A_326, k2_funct_1(C_328))=B_327 | ~v1_funct_2(k2_funct_1(C_328), B_327, A_326) | k2_relset_1(A_326, B_327, C_328)!=B_327 | ~v2_funct_1(C_328) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~v1_funct_2(C_328, A_326, B_327) | ~v1_funct_1(C_328))), inference(resolution, [status(thm)], [c_2189, c_36])).
% 7.31/2.56  tff(c_4344, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_4287])).
% 7.31/2.56  tff(c_4384, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_1859, c_3426, c_4344])).
% 7.31/2.56  tff(c_4385, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_4384])).
% 7.31/2.56  tff(c_10, plain, (![A_9]: (k1_relat_1(k2_funct_1(A_9))=k2_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.31/2.56  tff(c_4394, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4385, c_10])).
% 7.31/2.56  tff(c_4405, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_70, c_54, c_4394])).
% 7.31/2.56  tff(c_4407, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1501, c_4405])).
% 7.31/2.56  tff(c_4408, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1499])).
% 7.31/2.56  tff(c_335, plain, (![E_94, D_96, A_92, F_95, B_97, C_93]: (k4_relset_1(A_92, B_97, C_93, D_96, E_94, F_95)=k5_relat_1(E_94, F_95) | ~m1_subset_1(F_95, k1_zfmisc_1(k2_zfmisc_1(C_93, D_96))) | ~m1_subset_1(E_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_97))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.31/2.56  tff(c_346, plain, (![A_98, B_99, E_100]: (k4_relset_1(A_98, B_99, '#skF_2', '#skF_1', E_100, '#skF_4')=k5_relat_1(E_100, '#skF_4') | ~m1_subset_1(E_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(resolution, [status(thm)], [c_60, c_335])).
% 7.31/2.56  tff(c_358, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_346])).
% 7.31/2.56  tff(c_460, plain, (![D_115, E_117, C_119, A_118, B_116, F_114]: (m1_subset_1(k4_relset_1(A_118, B_116, C_119, D_115, E_117, F_114), k1_zfmisc_1(k2_zfmisc_1(A_118, D_115))) | ~m1_subset_1(F_114, k1_zfmisc_1(k2_zfmisc_1(C_119, D_115))) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_116))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.31/2.56  tff(c_517, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_358, c_460])).
% 7.31/2.56  tff(c_547, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_517])).
% 7.31/2.56  tff(c_993, plain, (![B_133, F_130, D_132, A_131, C_134, E_135]: (k1_partfun1(A_131, B_133, C_134, D_132, E_135, F_130)=k5_relat_1(E_135, F_130) | ~m1_subset_1(F_130, k1_zfmisc_1(k2_zfmisc_1(C_134, D_132))) | ~v1_funct_1(F_130) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_131, B_133))) | ~v1_funct_1(E_135))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.31/2.56  tff(c_1013, plain, (![A_131, B_133, E_135]: (k1_partfun1(A_131, B_133, '#skF_2', '#skF_1', E_135, '#skF_4')=k5_relat_1(E_135, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_131, B_133))) | ~v1_funct_1(E_135))), inference(resolution, [status(thm)], [c_60, c_993])).
% 7.31/2.56  tff(c_1303, plain, (![A_148, B_149, E_150]: (k1_partfun1(A_148, B_149, '#skF_2', '#skF_1', E_150, '#skF_4')=k5_relat_1(E_150, '#skF_4') | ~m1_subset_1(E_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))) | ~v1_funct_1(E_150))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1013])).
% 7.31/2.56  tff(c_1342, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1303])).
% 7.31/2.56  tff(c_1359, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1342])).
% 7.31/2.56  tff(c_24, plain, (![A_32]: (m1_subset_1(k6_relat_1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.31/2.56  tff(c_71, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_24])).
% 7.31/2.56  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.56  tff(c_269, plain, (![D_81, C_82, A_83, B_84]: (D_81=C_82 | ~r2_relset_1(A_83, B_84, C_82, D_81) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.31/2.56  tff(c_277, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_269])).
% 7.31/2.56  tff(c_292, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_277])).
% 7.31/2.56  tff(c_315, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_292])).
% 7.31/2.56  tff(c_1364, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_315])).
% 7.31/2.56  tff(c_1368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_547, c_1364])).
% 7.31/2.56  tff(c_1369, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_292])).
% 7.31/2.56  tff(c_5147, plain, (![A_358, C_361, B_360, F_357, D_359, E_362]: (k1_partfun1(A_358, B_360, C_361, D_359, E_362, F_357)=k5_relat_1(E_362, F_357) | ~m1_subset_1(F_357, k1_zfmisc_1(k2_zfmisc_1(C_361, D_359))) | ~v1_funct_1(F_357) | ~m1_subset_1(E_362, k1_zfmisc_1(k2_zfmisc_1(A_358, B_360))) | ~v1_funct_1(E_362))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.31/2.56  tff(c_5171, plain, (![A_358, B_360, E_362]: (k1_partfun1(A_358, B_360, '#skF_2', '#skF_1', E_362, '#skF_4')=k5_relat_1(E_362, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_362, k1_zfmisc_1(k2_zfmisc_1(A_358, B_360))) | ~v1_funct_1(E_362))), inference(resolution, [status(thm)], [c_60, c_5147])).
% 7.31/2.56  tff(c_5303, plain, (![A_370, B_371, E_372]: (k1_partfun1(A_370, B_371, '#skF_2', '#skF_1', E_372, '#skF_4')=k5_relat_1(E_372, '#skF_4') | ~m1_subset_1(E_372, k1_zfmisc_1(k2_zfmisc_1(A_370, B_371))) | ~v1_funct_1(E_372))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5171])).
% 7.31/2.56  tff(c_5342, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_5303])).
% 7.31/2.56  tff(c_5359, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1369, c_5342])).
% 7.31/2.56  tff(c_5361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4408, c_5359])).
% 7.31/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.56  
% 7.31/2.56  Inference rules
% 7.31/2.56  ----------------------
% 7.31/2.56  #Ref     : 0
% 7.31/2.56  #Sup     : 1238
% 7.31/2.56  #Fact    : 0
% 7.31/2.56  #Define  : 0
% 7.31/2.56  #Split   : 36
% 7.31/2.56  #Chain   : 0
% 7.31/2.56  #Close   : 0
% 7.31/2.56  
% 7.31/2.56  Ordering : KBO
% 7.31/2.56  
% 7.31/2.56  Simplification rules
% 7.31/2.56  ----------------------
% 7.31/2.56  #Subsume      : 41
% 7.31/2.56  #Demod        : 477
% 7.31/2.56  #Tautology    : 243
% 7.31/2.56  #SimpNegUnit  : 88
% 7.31/2.56  #BackRed      : 22
% 7.31/2.56  
% 7.31/2.56  #Partial instantiations: 0
% 7.31/2.56  #Strategies tried      : 1
% 7.31/2.56  
% 7.31/2.56  Timing (in seconds)
% 7.31/2.56  ----------------------
% 7.31/2.56  Preprocessing        : 0.39
% 7.31/2.56  Parsing              : 0.22
% 7.31/2.56  CNF conversion       : 0.02
% 7.31/2.56  Main loop            : 1.33
% 7.31/2.56  Inferencing          : 0.42
% 7.31/2.57  Reduction            : 0.50
% 7.31/2.57  Demodulation         : 0.37
% 7.31/2.57  BG Simplification    : 0.06
% 7.31/2.57  Subsumption          : 0.24
% 7.31/2.57  Abstraction          : 0.07
% 7.31/2.57  MUC search           : 0.00
% 7.31/2.57  Cooper               : 0.00
% 7.31/2.57  Total                : 1.76
% 7.31/2.57  Index Insertion      : 0.00
% 7.31/2.57  Index Deletion       : 0.00
% 7.31/2.57  Index Matching       : 0.00
% 7.31/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
