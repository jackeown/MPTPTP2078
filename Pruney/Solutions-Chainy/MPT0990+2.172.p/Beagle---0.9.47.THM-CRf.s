%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:21 EST 2020

% Result     : Theorem 6.61s
% Output     : CNFRefutation 6.61s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 294 expanded)
%              Number of leaves         :   41 ( 124 expanded)
%              Depth                    :   11
%              Number of atoms          :  271 (1248 expanded)
%              Number of equality atoms :  103 ( 431 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_161,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_119,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
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

tff(f_135,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_77,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_138,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_150,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_138])).

tff(c_191,plain,(
    ! [B_69,A_70,C_71] :
      ( k1_xboole_0 = B_69
      | k1_relset_1(A_70,B_69,C_71) = A_70
      | ~ v1_funct_2(C_71,A_70,B_69)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_200,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_191])).

tff(c_209,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_150,c_200])).

tff(c_210,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_209])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_88,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_88])).

tff(c_106,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_97])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_94,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_88])).

tff(c_103,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_94])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_149,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_138])).

tff(c_197,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_191])).

tff(c_205,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_149,c_197])).

tff(c_206,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_205])).

tff(c_40,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_relat_1(k1_relat_1(A_7)) != k5_relat_1(A_7,B_9)
      | k2_relat_1(A_7) != k1_relat_1(B_9)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1399,plain,(
    ! [A_157,B_158] :
      ( k2_funct_1(A_157) = B_158
      | k6_partfun1(k1_relat_1(A_157)) != k5_relat_1(A_157,B_158)
      | k2_relat_1(A_157) != k1_relat_1(B_158)
      | ~ v2_funct_1(A_157)
      | ~ v1_funct_1(B_158)
      | ~ v1_relat_1(B_158)
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10])).

tff(c_1403,plain,(
    ! [B_158] :
      ( k2_funct_1('#skF_3') = B_158
      | k5_relat_1('#skF_3',B_158) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_158)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_158)
      | ~ v1_relat_1(B_158)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_1399])).

tff(c_1470,plain,(
    ! [B_167] :
      ( k2_funct_1('#skF_3') = B_167
      | k5_relat_1('#skF_3',B_167) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_167)
      | ~ v1_funct_1(B_167)
      | ~ v1_relat_1(B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_70,c_54,c_1403])).

tff(c_1476,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_1470])).

tff(c_1486,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_210,c_1476])).

tff(c_1487,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1486])).

tff(c_1509,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1487])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1492,plain,(
    ! [C_168,B_169,A_170] :
      ( v1_funct_2(k2_funct_1(C_168),B_169,A_170)
      | k2_relset_1(A_170,B_169,C_168) != B_169
      | ~ v2_funct_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169)))
      | ~ v1_funct_2(C_168,A_170,B_169)
      | ~ v1_funct_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1498,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1492])).

tff(c_1505,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_1498])).

tff(c_2071,plain,(
    ! [C_197,B_198,A_199] :
      ( m1_subset_1(k2_funct_1(C_197),k1_zfmisc_1(k2_zfmisc_1(B_198,A_199)))
      | k2_relset_1(A_199,B_198,C_197) != B_198
      | ~ v2_funct_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198)))
      | ~ v1_funct_2(C_197,A_199,B_198)
      | ~ v1_funct_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_14,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_relset_1(A_16,B_17,C_18) = k1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2972,plain,(
    ! [B_259,A_260,C_261] :
      ( k1_relset_1(B_259,A_260,k2_funct_1(C_261)) = k1_relat_1(k2_funct_1(C_261))
      | k2_relset_1(A_260,B_259,C_261) != B_259
      | ~ v2_funct_1(C_261)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_260,B_259)))
      | ~ v1_funct_2(C_261,A_260,B_259)
      | ~ v1_funct_1(C_261) ) ),
    inference(resolution,[status(thm)],[c_2071,c_14])).

tff(c_3011,plain,
    ( k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2972])).

tff(c_3029,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_3011])).

tff(c_32,plain,(
    ! [B_30,A_29,C_31] :
      ( k1_xboole_0 = B_30
      | k1_relset_1(A_29,B_30,C_31) = A_29
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3898,plain,(
    ! [A_287,B_288,C_289] :
      ( k1_xboole_0 = A_287
      | k1_relset_1(B_288,A_287,k2_funct_1(C_289)) = B_288
      | ~ v1_funct_2(k2_funct_1(C_289),B_288,A_287)
      | k2_relset_1(A_287,B_288,C_289) != B_288
      | ~ v2_funct_1(C_289)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ v1_funct_2(C_289,A_287,B_288)
      | ~ v1_funct_1(C_289) ) ),
    inference(resolution,[status(thm)],[c_2071,c_32])).

tff(c_3952,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3898])).

tff(c_3993,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_1505,c_3029,c_3952])).

tff(c_3994,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3993])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4005,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3994,c_8])).

tff(c_4014,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_70,c_54,c_4005])).

tff(c_4016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1509,c_4014])).

tff(c_4017,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1487])).

tff(c_306,plain,(
    ! [C_85,B_87,A_88,F_89,E_86,D_90] :
      ( k4_relset_1(A_88,B_87,C_85,D_90,E_86,F_89) = k5_relat_1(E_86,F_89)
      | ~ m1_subset_1(F_89,k1_zfmisc_1(k2_zfmisc_1(C_85,D_90)))
      | ~ m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_357,plain,(
    ! [A_97,B_98,E_99] :
      ( k4_relset_1(A_97,B_98,'#skF_2','#skF_1',E_99,'#skF_4') = k5_relat_1(E_99,'#skF_4')
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(resolution,[status(thm)],[c_60,c_306])).

tff(c_368,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_357])).

tff(c_466,plain,(
    ! [E_115,A_116,F_118,B_114,C_119,D_117] :
      ( m1_subset_1(k4_relset_1(A_116,B_114,C_119,D_117,E_115,F_118),k1_zfmisc_1(k2_zfmisc_1(A_116,D_117)))
      | ~ m1_subset_1(F_118,k1_zfmisc_1(k2_zfmisc_1(C_119,D_117)))
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_526,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_466])).

tff(c_563,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_526])).

tff(c_771,plain,(
    ! [E_121,B_125,F_123,C_122,A_120,D_124] :
      ( k1_partfun1(A_120,B_125,C_122,D_124,E_121,F_123) = k5_relat_1(E_121,F_123)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_122,D_124)))
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_120,B_125)))
      | ~ v1_funct_1(E_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_787,plain,(
    ! [A_120,B_125,E_121] :
      ( k1_partfun1(A_120,B_125,'#skF_2','#skF_1',E_121,'#skF_4') = k5_relat_1(E_121,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_120,B_125)))
      | ~ v1_funct_1(E_121) ) ),
    inference(resolution,[status(thm)],[c_60,c_771])).

tff(c_1292,plain,(
    ! [A_144,B_145,E_146] :
      ( k1_partfun1(A_144,B_145,'#skF_2','#skF_1',E_146,'#skF_4') = k5_relat_1(E_146,'#skF_4')
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_1(E_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_787])).

tff(c_1331,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1292])).

tff(c_1349,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1331])).

tff(c_36,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_259,plain,(
    ! [D_77,C_78,A_79,B_80] :
      ( D_77 = C_78
      | ~ r2_relset_1(A_79,B_80,C_78,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_267,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_259])).

tff(c_282,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_267])).

tff(c_283,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_1353,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1349,c_283])).

tff(c_1357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_1353])).

tff(c_1358,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_4380,plain,(
    ! [E_305,A_304,D_308,C_306,B_309,F_307] :
      ( k1_partfun1(A_304,B_309,C_306,D_308,E_305,F_307) = k5_relat_1(E_305,F_307)
      | ~ m1_subset_1(F_307,k1_zfmisc_1(k2_zfmisc_1(C_306,D_308)))
      | ~ v1_funct_1(F_307)
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(A_304,B_309)))
      | ~ v1_funct_1(E_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4396,plain,(
    ! [A_304,B_309,E_305] :
      ( k1_partfun1(A_304,B_309,'#skF_2','#skF_1',E_305,'#skF_4') = k5_relat_1(E_305,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(A_304,B_309)))
      | ~ v1_funct_1(E_305) ) ),
    inference(resolution,[status(thm)],[c_60,c_4380])).

tff(c_4755,plain,(
    ! [A_321,B_322,E_323] :
      ( k1_partfun1(A_321,B_322,'#skF_2','#skF_1',E_323,'#skF_4') = k5_relat_1(E_323,'#skF_4')
      | ~ m1_subset_1(E_323,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322)))
      | ~ v1_funct_1(E_323) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4396])).

tff(c_4791,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_4755])).

tff(c_4808,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1358,c_4791])).

tff(c_4810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4017,c_4808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:53:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.61/2.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.61/2.33  
% 6.61/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.61/2.33  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.61/2.33  
% 6.61/2.33  %Foreground sorts:
% 6.61/2.33  
% 6.61/2.33  
% 6.61/2.33  %Background operators:
% 6.61/2.33  
% 6.61/2.33  
% 6.61/2.33  %Foreground operators:
% 6.61/2.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.61/2.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.61/2.33  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.61/2.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.61/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.61/2.33  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.61/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.61/2.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.61/2.33  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.61/2.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.61/2.33  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.61/2.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.61/2.33  tff('#skF_2', type, '#skF_2': $i).
% 6.61/2.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.61/2.33  tff('#skF_3', type, '#skF_3': $i).
% 6.61/2.33  tff('#skF_1', type, '#skF_1': $i).
% 6.61/2.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.61/2.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.61/2.33  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.61/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.61/2.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.61/2.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.61/2.33  tff('#skF_4', type, '#skF_4': $i).
% 6.61/2.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.61/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.61/2.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.61/2.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.61/2.33  
% 6.61/2.35  tff(f_161, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.61/2.35  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.61/2.35  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.61/2.35  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.61/2.35  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.61/2.35  tff(f_119, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.61/2.35  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 6.61/2.35  tff(f_135, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 6.61/2.35  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.61/2.35  tff(f_77, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 6.61/2.35  tff(f_67, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 6.61/2.35  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.61/2.35  tff(f_107, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.61/2.35  tff(f_85, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.61/2.35  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.61/2.35  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.61/2.35  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.61/2.35  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.61/2.35  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.61/2.35  tff(c_138, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.61/2.35  tff(c_150, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_138])).
% 6.61/2.35  tff(c_191, plain, (![B_69, A_70, C_71]: (k1_xboole_0=B_69 | k1_relset_1(A_70, B_69, C_71)=A_70 | ~v1_funct_2(C_71, A_70, B_69) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.61/2.35  tff(c_200, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_191])).
% 6.61/2.35  tff(c_209, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_150, c_200])).
% 6.61/2.35  tff(c_210, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_209])).
% 6.61/2.35  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.61/2.35  tff(c_88, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.61/2.35  tff(c_97, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_88])).
% 6.61/2.35  tff(c_106, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_97])).
% 6.61/2.35  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.61/2.35  tff(c_94, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_88])).
% 6.61/2.35  tff(c_103, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_94])).
% 6.61/2.35  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.61/2.35  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.61/2.35  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.61/2.35  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.61/2.35  tff(c_149, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_138])).
% 6.61/2.35  tff(c_197, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_191])).
% 6.61/2.35  tff(c_205, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_149, c_197])).
% 6.61/2.35  tff(c_206, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_205])).
% 6.61/2.35  tff(c_40, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.61/2.35  tff(c_10, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_relat_1(k1_relat_1(A_7))!=k5_relat_1(A_7, B_9) | k2_relat_1(A_7)!=k1_relat_1(B_9) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.61/2.35  tff(c_1399, plain, (![A_157, B_158]: (k2_funct_1(A_157)=B_158 | k6_partfun1(k1_relat_1(A_157))!=k5_relat_1(A_157, B_158) | k2_relat_1(A_157)!=k1_relat_1(B_158) | ~v2_funct_1(A_157) | ~v1_funct_1(B_158) | ~v1_relat_1(B_158) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10])).
% 6.61/2.35  tff(c_1403, plain, (![B_158]: (k2_funct_1('#skF_3')=B_158 | k5_relat_1('#skF_3', B_158)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_158) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_158) | ~v1_relat_1(B_158) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_206, c_1399])).
% 6.61/2.35  tff(c_1470, plain, (![B_167]: (k2_funct_1('#skF_3')=B_167 | k5_relat_1('#skF_3', B_167)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_167) | ~v1_funct_1(B_167) | ~v1_relat_1(B_167))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_70, c_54, c_1403])).
% 6.61/2.35  tff(c_1476, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_1470])).
% 6.61/2.35  tff(c_1486, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_210, c_1476])).
% 6.61/2.35  tff(c_1487, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_1486])).
% 6.61/2.35  tff(c_1509, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_1487])).
% 6.61/2.35  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.61/2.35  tff(c_1492, plain, (![C_168, B_169, A_170]: (v1_funct_2(k2_funct_1(C_168), B_169, A_170) | k2_relset_1(A_170, B_169, C_168)!=B_169 | ~v2_funct_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))) | ~v1_funct_2(C_168, A_170, B_169) | ~v1_funct_1(C_168))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.61/2.35  tff(c_1498, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1492])).
% 6.61/2.35  tff(c_1505, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_1498])).
% 6.61/2.35  tff(c_2071, plain, (![C_197, B_198, A_199]: (m1_subset_1(k2_funct_1(C_197), k1_zfmisc_1(k2_zfmisc_1(B_198, A_199))) | k2_relset_1(A_199, B_198, C_197)!=B_198 | ~v2_funct_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))) | ~v1_funct_2(C_197, A_199, B_198) | ~v1_funct_1(C_197))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.61/2.35  tff(c_14, plain, (![A_16, B_17, C_18]: (k1_relset_1(A_16, B_17, C_18)=k1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.61/2.35  tff(c_2972, plain, (![B_259, A_260, C_261]: (k1_relset_1(B_259, A_260, k2_funct_1(C_261))=k1_relat_1(k2_funct_1(C_261)) | k2_relset_1(A_260, B_259, C_261)!=B_259 | ~v2_funct_1(C_261) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_260, B_259))) | ~v1_funct_2(C_261, A_260, B_259) | ~v1_funct_1(C_261))), inference(resolution, [status(thm)], [c_2071, c_14])).
% 6.61/2.35  tff(c_3011, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2972])).
% 6.61/2.35  tff(c_3029, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_3011])).
% 6.61/2.35  tff(c_32, plain, (![B_30, A_29, C_31]: (k1_xboole_0=B_30 | k1_relset_1(A_29, B_30, C_31)=A_29 | ~v1_funct_2(C_31, A_29, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.61/2.35  tff(c_3898, plain, (![A_287, B_288, C_289]: (k1_xboole_0=A_287 | k1_relset_1(B_288, A_287, k2_funct_1(C_289))=B_288 | ~v1_funct_2(k2_funct_1(C_289), B_288, A_287) | k2_relset_1(A_287, B_288, C_289)!=B_288 | ~v2_funct_1(C_289) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~v1_funct_2(C_289, A_287, B_288) | ~v1_funct_1(C_289))), inference(resolution, [status(thm)], [c_2071, c_32])).
% 6.61/2.35  tff(c_3952, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3898])).
% 6.61/2.35  tff(c_3993, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_1505, c_3029, c_3952])).
% 6.61/2.35  tff(c_3994, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_3993])).
% 6.61/2.35  tff(c_8, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.61/2.35  tff(c_4005, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3994, c_8])).
% 6.61/2.35  tff(c_4014, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_70, c_54, c_4005])).
% 6.61/2.35  tff(c_4016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1509, c_4014])).
% 6.61/2.35  tff(c_4017, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1487])).
% 6.61/2.35  tff(c_306, plain, (![C_85, B_87, A_88, F_89, E_86, D_90]: (k4_relset_1(A_88, B_87, C_85, D_90, E_86, F_89)=k5_relat_1(E_86, F_89) | ~m1_subset_1(F_89, k1_zfmisc_1(k2_zfmisc_1(C_85, D_90))) | ~m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.61/2.35  tff(c_357, plain, (![A_97, B_98, E_99]: (k4_relset_1(A_97, B_98, '#skF_2', '#skF_1', E_99, '#skF_4')=k5_relat_1(E_99, '#skF_4') | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(resolution, [status(thm)], [c_60, c_306])).
% 6.61/2.35  tff(c_368, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_357])).
% 6.61/2.35  tff(c_466, plain, (![E_115, A_116, F_118, B_114, C_119, D_117]: (m1_subset_1(k4_relset_1(A_116, B_114, C_119, D_117, E_115, F_118), k1_zfmisc_1(k2_zfmisc_1(A_116, D_117))) | ~m1_subset_1(F_118, k1_zfmisc_1(k2_zfmisc_1(C_119, D_117))) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_114))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.61/2.35  tff(c_526, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_368, c_466])).
% 6.61/2.35  tff(c_563, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_526])).
% 6.61/2.35  tff(c_771, plain, (![E_121, B_125, F_123, C_122, A_120, D_124]: (k1_partfun1(A_120, B_125, C_122, D_124, E_121, F_123)=k5_relat_1(E_121, F_123) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_122, D_124))) | ~v1_funct_1(F_123) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_120, B_125))) | ~v1_funct_1(E_121))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.61/2.35  tff(c_787, plain, (![A_120, B_125, E_121]: (k1_partfun1(A_120, B_125, '#skF_2', '#skF_1', E_121, '#skF_4')=k5_relat_1(E_121, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_120, B_125))) | ~v1_funct_1(E_121))), inference(resolution, [status(thm)], [c_60, c_771])).
% 6.61/2.35  tff(c_1292, plain, (![A_144, B_145, E_146]: (k1_partfun1(A_144, B_145, '#skF_2', '#skF_1', E_146, '#skF_4')=k5_relat_1(E_146, '#skF_4') | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_1(E_146))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_787])).
% 6.61/2.35  tff(c_1331, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1292])).
% 6.61/2.35  tff(c_1349, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1331])).
% 6.61/2.35  tff(c_36, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.61/2.35  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.61/2.35  tff(c_259, plain, (![D_77, C_78, A_79, B_80]: (D_77=C_78 | ~r2_relset_1(A_79, B_80, C_78, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.61/2.35  tff(c_267, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_259])).
% 6.61/2.35  tff(c_282, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_267])).
% 6.61/2.35  tff(c_283, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_282])).
% 6.61/2.35  tff(c_1353, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1349, c_283])).
% 6.61/2.35  tff(c_1357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_563, c_1353])).
% 6.61/2.35  tff(c_1358, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_282])).
% 6.61/2.35  tff(c_4380, plain, (![E_305, A_304, D_308, C_306, B_309, F_307]: (k1_partfun1(A_304, B_309, C_306, D_308, E_305, F_307)=k5_relat_1(E_305, F_307) | ~m1_subset_1(F_307, k1_zfmisc_1(k2_zfmisc_1(C_306, D_308))) | ~v1_funct_1(F_307) | ~m1_subset_1(E_305, k1_zfmisc_1(k2_zfmisc_1(A_304, B_309))) | ~v1_funct_1(E_305))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.61/2.35  tff(c_4396, plain, (![A_304, B_309, E_305]: (k1_partfun1(A_304, B_309, '#skF_2', '#skF_1', E_305, '#skF_4')=k5_relat_1(E_305, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_305, k1_zfmisc_1(k2_zfmisc_1(A_304, B_309))) | ~v1_funct_1(E_305))), inference(resolution, [status(thm)], [c_60, c_4380])).
% 6.61/2.35  tff(c_4755, plain, (![A_321, B_322, E_323]: (k1_partfun1(A_321, B_322, '#skF_2', '#skF_1', E_323, '#skF_4')=k5_relat_1(E_323, '#skF_4') | ~m1_subset_1(E_323, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))) | ~v1_funct_1(E_323))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4396])).
% 6.61/2.35  tff(c_4791, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_4755])).
% 6.61/2.35  tff(c_4808, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1358, c_4791])).
% 6.61/2.35  tff(c_4810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4017, c_4808])).
% 6.61/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.61/2.35  
% 6.61/2.35  Inference rules
% 6.61/2.35  ----------------------
% 6.61/2.35  #Ref     : 0
% 6.61/2.35  #Sup     : 1106
% 6.61/2.35  #Fact    : 0
% 6.61/2.35  #Define  : 0
% 6.61/2.35  #Split   : 24
% 6.61/2.35  #Chain   : 0
% 6.61/2.35  #Close   : 0
% 6.61/2.35  
% 6.61/2.35  Ordering : KBO
% 6.61/2.35  
% 6.61/2.35  Simplification rules
% 6.61/2.35  ----------------------
% 6.61/2.35  #Subsume      : 30
% 6.61/2.35  #Demod        : 439
% 6.61/2.35  #Tautology    : 217
% 6.61/2.35  #SimpNegUnit  : 87
% 6.61/2.35  #BackRed      : 25
% 6.61/2.35  
% 6.61/2.35  #Partial instantiations: 0
% 6.61/2.35  #Strategies tried      : 1
% 6.61/2.35  
% 6.61/2.35  Timing (in seconds)
% 6.61/2.35  ----------------------
% 6.61/2.36  Preprocessing        : 0.36
% 6.61/2.36  Parsing              : 0.18
% 6.61/2.36  CNF conversion       : 0.02
% 6.61/2.36  Main loop            : 1.24
% 6.61/2.36  Inferencing          : 0.40
% 6.61/2.36  Reduction            : 0.45
% 6.61/2.36  Demodulation         : 0.33
% 6.61/2.36  BG Simplification    : 0.06
% 6.61/2.36  Subsumption          : 0.23
% 6.61/2.36  Abstraction          : 0.07
% 6.61/2.36  MUC search           : 0.00
% 6.61/2.36  Cooper               : 0.00
% 6.61/2.36  Total                : 1.64
% 6.61/2.36  Index Insertion      : 0.00
% 6.61/2.36  Index Deletion       : 0.00
% 6.61/2.36  Index Matching       : 0.00
% 6.61/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
