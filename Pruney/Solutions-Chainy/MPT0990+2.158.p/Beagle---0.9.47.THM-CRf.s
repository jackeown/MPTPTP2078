%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:19 EST 2020

% Result     : Theorem 5.46s
% Output     : CNFRefutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 303 expanded)
%              Number of leaves         :   39 ( 127 expanded)
%              Depth                    :   11
%              Number of atoms          :  269 (1318 expanded)
%              Number of equality atoms :   99 ( 449 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_174,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_132,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_148,axiom,(
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

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_120,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_140,plain,(
    ! [A_55,B_56,C_57] :
      ( k1_relset_1(A_55,B_56,C_57) = k1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_151,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_140])).

tff(c_215,plain,(
    ! [B_71,A_72,C_73] :
      ( k1_xboole_0 = B_71
      | k1_relset_1(A_72,B_71,C_73) = A_72
      | ~ v1_funct_2(C_73,A_72,B_71)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_221,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_215])).

tff(c_229,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_151,c_221])).

tff(c_230,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_229])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_91,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_91])).

tff(c_106,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_97])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_100,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_91])).

tff(c_109,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_152,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_140])).

tff(c_224,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_215])).

tff(c_233,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_152,c_224])).

tff(c_234,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_233])).

tff(c_42,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

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

tff(c_769,plain,(
    ! [A_153,B_154] :
      ( k2_funct_1(A_153) = B_154
      | k6_partfun1(k1_relat_1(A_153)) != k5_relat_1(A_153,B_154)
      | k2_relat_1(A_153) != k1_relat_1(B_154)
      | ~ v2_funct_1(A_153)
      | ~ v1_funct_1(B_154)
      | ~ v1_relat_1(B_154)
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_771,plain,(
    ! [B_154] :
      ( k2_funct_1('#skF_3') = B_154
      | k5_relat_1('#skF_3',B_154) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_154)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_154)
      | ~ v1_relat_1(B_154)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_769])).

tff(c_780,plain,(
    ! [B_155] :
      ( k2_funct_1('#skF_3') = B_155
      | k5_relat_1('#skF_3',B_155) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_155)
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_72,c_56,c_771])).

tff(c_789,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_780])).

tff(c_799,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_230,c_789])).

tff(c_800,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_799])).

tff(c_802,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_800])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_810,plain,(
    ! [C_159,B_160,A_161] :
      ( v1_funct_2(k2_funct_1(C_159),B_160,A_161)
      | k2_relset_1(A_161,B_160,C_159) != B_160
      | ~ v2_funct_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160)))
      | ~ v1_funct_2(C_159,A_161,B_160)
      | ~ v1_funct_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_819,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_810])).

tff(c_826,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_60,c_819])).

tff(c_928,plain,(
    ! [C_188,B_189,A_190] :
      ( m1_subset_1(k2_funct_1(C_188),k1_zfmisc_1(k2_zfmisc_1(B_189,A_190)))
      | k2_relset_1(A_190,B_189,C_188) != B_189
      | ~ v2_funct_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_190,B_189)))
      | ~ v1_funct_2(C_188,A_190,B_189)
      | ~ v1_funct_1(C_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] :
      ( k1_relset_1(A_13,B_14,C_15) = k1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1894,plain,(
    ! [B_227,A_228,C_229] :
      ( k1_relset_1(B_227,A_228,k2_funct_1(C_229)) = k1_relat_1(k2_funct_1(C_229))
      | k2_relset_1(A_228,B_227,C_229) != B_227
      | ~ v2_funct_1(C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_228,B_227)))
      | ~ v1_funct_2(C_229,A_228,B_227)
      | ~ v1_funct_1(C_229) ) ),
    inference(resolution,[status(thm)],[c_928,c_14])).

tff(c_1927,plain,
    ( k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1894])).

tff(c_1954,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_60,c_1927])).

tff(c_30,plain,(
    ! [B_21,A_20,C_22] :
      ( k1_xboole_0 = B_21
      | k1_relset_1(A_20,B_21,C_22) = A_20
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2357,plain,(
    ! [A_234,B_235,C_236] :
      ( k1_xboole_0 = A_234
      | k1_relset_1(B_235,A_234,k2_funct_1(C_236)) = B_235
      | ~ v1_funct_2(k2_funct_1(C_236),B_235,A_234)
      | k2_relset_1(A_234,B_235,C_236) != B_235
      | ~ v2_funct_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_2(C_236,A_234,B_235)
      | ~ v1_funct_1(C_236) ) ),
    inference(resolution,[status(thm)],[c_928,c_30])).

tff(c_2399,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2357])).

tff(c_2445,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_60,c_826,c_1954,c_2399])).

tff(c_2446,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2445])).

tff(c_10,plain,(
    ! [A_9] :
      ( k1_relat_1(k2_funct_1(A_9)) = k2_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2455,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2446,c_10])).

tff(c_2466,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_72,c_56,c_2455])).

tff(c_2468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_802,c_2466])).

tff(c_2469,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_800])).

tff(c_465,plain,(
    ! [C_121,A_124,B_122,D_126,F_123,E_125] :
      ( k1_partfun1(A_124,B_122,C_121,D_126,E_125,F_123) = k5_relat_1(E_125,F_123)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_121,D_126)))
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_1(E_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_469,plain,(
    ! [A_124,B_122,E_125] :
      ( k1_partfun1(A_124,B_122,'#skF_2','#skF_1',E_125,'#skF_4') = k5_relat_1(E_125,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_1(E_125) ) ),
    inference(resolution,[status(thm)],[c_62,c_465])).

tff(c_479,plain,(
    ! [A_127,B_128,E_129] :
      ( k1_partfun1(A_127,B_128,'#skF_2','#skF_1',E_129,'#skF_4') = k5_relat_1(E_129,'#skF_4')
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_funct_1(E_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_469])).

tff(c_488,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_479])).

tff(c_495,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_488])).

tff(c_38,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_262,plain,(
    ! [D_75,C_76,A_77,B_78] :
      ( D_75 = C_76
      | ~ r2_relset_1(A_77,B_78,C_76,D_75)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_270,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_262])).

tff(c_285,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_270])).

tff(c_317,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_502,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_317])).

tff(c_646,plain,(
    ! [E_143,B_144,F_142,C_141,D_145,A_146] :
      ( m1_subset_1(k1_partfun1(A_146,B_144,C_141,D_145,E_143,F_142),k1_zfmisc_1(k2_zfmisc_1(A_146,D_145)))
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(C_141,D_145)))
      | ~ v1_funct_1(F_142)
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_146,B_144)))
      | ~ v1_funct_1(E_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_708,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_646])).

tff(c_737,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_708])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_502,c_737])).

tff(c_740,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_2659,plain,(
    ! [A_271,D_273,F_270,B_269,C_268,E_272] :
      ( k1_partfun1(A_271,B_269,C_268,D_273,E_272,F_270) = k5_relat_1(E_272,F_270)
      | ~ m1_subset_1(F_270,k1_zfmisc_1(k2_zfmisc_1(C_268,D_273)))
      | ~ v1_funct_1(F_270)
      | ~ m1_subset_1(E_272,k1_zfmisc_1(k2_zfmisc_1(A_271,B_269)))
      | ~ v1_funct_1(E_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2665,plain,(
    ! [A_271,B_269,E_272] :
      ( k1_partfun1(A_271,B_269,'#skF_2','#skF_1',E_272,'#skF_4') = k5_relat_1(E_272,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_272,k1_zfmisc_1(k2_zfmisc_1(A_271,B_269)))
      | ~ v1_funct_1(E_272) ) ),
    inference(resolution,[status(thm)],[c_62,c_2659])).

tff(c_2679,plain,(
    ! [A_278,B_279,E_280] :
      ( k1_partfun1(A_278,B_279,'#skF_2','#skF_1',E_280,'#skF_4') = k5_relat_1(E_280,'#skF_4')
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279)))
      | ~ v1_funct_1(E_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2665])).

tff(c_2691,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2679])).

tff(c_2699,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_740,c_2691])).

tff(c_2701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2469,c_2699])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.46/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.46/2.05  
% 5.46/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.46/2.06  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.46/2.06  
% 5.46/2.06  %Foreground sorts:
% 5.46/2.06  
% 5.46/2.06  
% 5.46/2.06  %Background operators:
% 5.46/2.06  
% 5.46/2.06  
% 5.46/2.06  %Foreground operators:
% 5.46/2.06  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.46/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.46/2.06  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.46/2.06  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.46/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.46/2.06  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.46/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.46/2.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.46/2.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.46/2.06  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.46/2.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.46/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.46/2.06  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.46/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.46/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.46/2.06  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.46/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.46/2.06  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.46/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.46/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.46/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.46/2.06  tff('#skF_4', type, '#skF_4': $i).
% 5.46/2.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.46/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.46/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.46/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.46/2.06  
% 5.85/2.08  tff(f_174, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 5.85/2.08  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.85/2.08  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.85/2.08  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.85/2.08  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.85/2.08  tff(f_132, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.85/2.08  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 5.85/2.08  tff(f_148, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.85/2.08  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.85/2.08  tff(f_130, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.85/2.08  tff(f_120, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.85/2.08  tff(f_86, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.85/2.08  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.85/2.08  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.85/2.08  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.85/2.08  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.85/2.08  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.85/2.08  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.85/2.08  tff(c_140, plain, (![A_55, B_56, C_57]: (k1_relset_1(A_55, B_56, C_57)=k1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.85/2.08  tff(c_151, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_140])).
% 5.85/2.08  tff(c_215, plain, (![B_71, A_72, C_73]: (k1_xboole_0=B_71 | k1_relset_1(A_72, B_71, C_73)=A_72 | ~v1_funct_2(C_73, A_72, B_71) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.85/2.08  tff(c_221, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_215])).
% 5.85/2.08  tff(c_229, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_151, c_221])).
% 5.85/2.08  tff(c_230, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_229])).
% 5.85/2.08  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.85/2.08  tff(c_91, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.85/2.08  tff(c_97, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_91])).
% 5.85/2.08  tff(c_106, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_97])).
% 5.85/2.08  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.85/2.08  tff(c_100, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_91])).
% 5.85/2.08  tff(c_109, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_100])).
% 5.85/2.08  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.85/2.08  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.85/2.08  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.85/2.08  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.85/2.08  tff(c_152, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_140])).
% 5.85/2.08  tff(c_224, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_215])).
% 5.85/2.08  tff(c_233, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_152, c_224])).
% 5.85/2.08  tff(c_234, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_233])).
% 5.85/2.08  tff(c_42, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.85/2.08  tff(c_12, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_relat_1(k1_relat_1(A_10))!=k5_relat_1(A_10, B_12) | k2_relat_1(A_10)!=k1_relat_1(B_12) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.85/2.08  tff(c_769, plain, (![A_153, B_154]: (k2_funct_1(A_153)=B_154 | k6_partfun1(k1_relat_1(A_153))!=k5_relat_1(A_153, B_154) | k2_relat_1(A_153)!=k1_relat_1(B_154) | ~v2_funct_1(A_153) | ~v1_funct_1(B_154) | ~v1_relat_1(B_154) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_12])).
% 5.85/2.08  tff(c_771, plain, (![B_154]: (k2_funct_1('#skF_3')=B_154 | k5_relat_1('#skF_3', B_154)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_154) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_154) | ~v1_relat_1(B_154) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_769])).
% 5.85/2.08  tff(c_780, plain, (![B_155]: (k2_funct_1('#skF_3')=B_155 | k5_relat_1('#skF_3', B_155)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_155) | ~v1_funct_1(B_155) | ~v1_relat_1(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_72, c_56, c_771])).
% 5.85/2.08  tff(c_789, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_780])).
% 5.85/2.08  tff(c_799, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_230, c_789])).
% 5.85/2.08  tff(c_800, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_50, c_799])).
% 5.85/2.08  tff(c_802, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_800])).
% 5.85/2.08  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.85/2.08  tff(c_810, plain, (![C_159, B_160, A_161]: (v1_funct_2(k2_funct_1(C_159), B_160, A_161) | k2_relset_1(A_161, B_160, C_159)!=B_160 | ~v2_funct_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))) | ~v1_funct_2(C_159, A_161, B_160) | ~v1_funct_1(C_159))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.85/2.08  tff(c_819, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_810])).
% 5.85/2.08  tff(c_826, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_60, c_819])).
% 5.85/2.08  tff(c_928, plain, (![C_188, B_189, A_190]: (m1_subset_1(k2_funct_1(C_188), k1_zfmisc_1(k2_zfmisc_1(B_189, A_190))) | k2_relset_1(A_190, B_189, C_188)!=B_189 | ~v2_funct_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_190, B_189))) | ~v1_funct_2(C_188, A_190, B_189) | ~v1_funct_1(C_188))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.85/2.08  tff(c_14, plain, (![A_13, B_14, C_15]: (k1_relset_1(A_13, B_14, C_15)=k1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.85/2.08  tff(c_1894, plain, (![B_227, A_228, C_229]: (k1_relset_1(B_227, A_228, k2_funct_1(C_229))=k1_relat_1(k2_funct_1(C_229)) | k2_relset_1(A_228, B_227, C_229)!=B_227 | ~v2_funct_1(C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_228, B_227))) | ~v1_funct_2(C_229, A_228, B_227) | ~v1_funct_1(C_229))), inference(resolution, [status(thm)], [c_928, c_14])).
% 5.85/2.08  tff(c_1927, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1894])).
% 5.85/2.08  tff(c_1954, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_60, c_1927])).
% 5.85/2.08  tff(c_30, plain, (![B_21, A_20, C_22]: (k1_xboole_0=B_21 | k1_relset_1(A_20, B_21, C_22)=A_20 | ~v1_funct_2(C_22, A_20, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.85/2.08  tff(c_2357, plain, (![A_234, B_235, C_236]: (k1_xboole_0=A_234 | k1_relset_1(B_235, A_234, k2_funct_1(C_236))=B_235 | ~v1_funct_2(k2_funct_1(C_236), B_235, A_234) | k2_relset_1(A_234, B_235, C_236)!=B_235 | ~v2_funct_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_2(C_236, A_234, B_235) | ~v1_funct_1(C_236))), inference(resolution, [status(thm)], [c_928, c_30])).
% 5.85/2.08  tff(c_2399, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2357])).
% 5.85/2.08  tff(c_2445, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_60, c_826, c_1954, c_2399])).
% 5.85/2.08  tff(c_2446, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_2445])).
% 5.85/2.08  tff(c_10, plain, (![A_9]: (k1_relat_1(k2_funct_1(A_9))=k2_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.85/2.08  tff(c_2455, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2446, c_10])).
% 5.85/2.08  tff(c_2466, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_72, c_56, c_2455])).
% 5.85/2.08  tff(c_2468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_802, c_2466])).
% 5.85/2.08  tff(c_2469, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_800])).
% 5.85/2.08  tff(c_465, plain, (![C_121, A_124, B_122, D_126, F_123, E_125]: (k1_partfun1(A_124, B_122, C_121, D_126, E_125, F_123)=k5_relat_1(E_125, F_123) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_121, D_126))) | ~v1_funct_1(F_123) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_1(E_125))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.85/2.08  tff(c_469, plain, (![A_124, B_122, E_125]: (k1_partfun1(A_124, B_122, '#skF_2', '#skF_1', E_125, '#skF_4')=k5_relat_1(E_125, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_1(E_125))), inference(resolution, [status(thm)], [c_62, c_465])).
% 5.85/2.08  tff(c_479, plain, (![A_127, B_128, E_129]: (k1_partfun1(A_127, B_128, '#skF_2', '#skF_1', E_129, '#skF_4')=k5_relat_1(E_129, '#skF_4') | ~m1_subset_1(E_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~v1_funct_1(E_129))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_469])).
% 5.85/2.08  tff(c_488, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_479])).
% 5.85/2.08  tff(c_495, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_488])).
% 5.85/2.08  tff(c_38, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.85/2.08  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.85/2.08  tff(c_262, plain, (![D_75, C_76, A_77, B_78]: (D_75=C_76 | ~r2_relset_1(A_77, B_78, C_76, D_75) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.85/2.08  tff(c_270, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_262])).
% 5.85/2.08  tff(c_285, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_270])).
% 5.85/2.08  tff(c_317, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_285])).
% 5.85/2.08  tff(c_502, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_495, c_317])).
% 5.85/2.08  tff(c_646, plain, (![E_143, B_144, F_142, C_141, D_145, A_146]: (m1_subset_1(k1_partfun1(A_146, B_144, C_141, D_145, E_143, F_142), k1_zfmisc_1(k2_zfmisc_1(A_146, D_145))) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(C_141, D_145))) | ~v1_funct_1(F_142) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_146, B_144))) | ~v1_funct_1(E_143))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.85/2.08  tff(c_708, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_495, c_646])).
% 5.85/2.08  tff(c_737, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_708])).
% 5.85/2.08  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_502, c_737])).
% 5.85/2.08  tff(c_740, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_285])).
% 5.85/2.08  tff(c_2659, plain, (![A_271, D_273, F_270, B_269, C_268, E_272]: (k1_partfun1(A_271, B_269, C_268, D_273, E_272, F_270)=k5_relat_1(E_272, F_270) | ~m1_subset_1(F_270, k1_zfmisc_1(k2_zfmisc_1(C_268, D_273))) | ~v1_funct_1(F_270) | ~m1_subset_1(E_272, k1_zfmisc_1(k2_zfmisc_1(A_271, B_269))) | ~v1_funct_1(E_272))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.85/2.08  tff(c_2665, plain, (![A_271, B_269, E_272]: (k1_partfun1(A_271, B_269, '#skF_2', '#skF_1', E_272, '#skF_4')=k5_relat_1(E_272, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_272, k1_zfmisc_1(k2_zfmisc_1(A_271, B_269))) | ~v1_funct_1(E_272))), inference(resolution, [status(thm)], [c_62, c_2659])).
% 5.85/2.08  tff(c_2679, plain, (![A_278, B_279, E_280]: (k1_partfun1(A_278, B_279, '#skF_2', '#skF_1', E_280, '#skF_4')=k5_relat_1(E_280, '#skF_4') | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))) | ~v1_funct_1(E_280))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2665])).
% 5.85/2.08  tff(c_2691, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2679])).
% 5.85/2.08  tff(c_2699, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_740, c_2691])).
% 5.85/2.08  tff(c_2701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2469, c_2699])).
% 5.85/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.08  
% 5.85/2.08  Inference rules
% 5.85/2.08  ----------------------
% 5.85/2.08  #Ref     : 0
% 5.85/2.08  #Sup     : 527
% 5.85/2.08  #Fact    : 0
% 5.85/2.08  #Define  : 0
% 5.85/2.08  #Split   : 18
% 5.85/2.08  #Chain   : 0
% 5.85/2.08  #Close   : 0
% 5.85/2.08  
% 5.85/2.08  Ordering : KBO
% 5.85/2.08  
% 5.85/2.08  Simplification rules
% 5.85/2.08  ----------------------
% 5.85/2.08  #Subsume      : 34
% 5.85/2.08  #Demod        : 407
% 5.85/2.08  #Tautology    : 87
% 5.85/2.08  #SimpNegUnit  : 45
% 5.85/2.08  #BackRed      : 21
% 5.85/2.08  
% 5.85/2.08  #Partial instantiations: 0
% 5.85/2.08  #Strategies tried      : 1
% 5.85/2.08  
% 5.85/2.08  Timing (in seconds)
% 5.85/2.08  ----------------------
% 5.85/2.08  Preprocessing        : 0.37
% 5.85/2.08  Parsing              : 0.20
% 5.85/2.08  CNF conversion       : 0.02
% 5.85/2.08  Main loop            : 0.93
% 5.85/2.08  Inferencing          : 0.32
% 5.85/2.08  Reduction            : 0.35
% 5.85/2.08  Demodulation         : 0.25
% 5.85/2.08  BG Simplification    : 0.04
% 5.85/2.08  Subsumption          : 0.16
% 5.85/2.08  Abstraction          : 0.04
% 5.85/2.08  MUC search           : 0.00
% 5.85/2.08  Cooper               : 0.00
% 5.85/2.08  Total                : 1.35
% 5.85/2.08  Index Insertion      : 0.00
% 5.85/2.08  Index Deletion       : 0.00
% 5.85/2.08  Index Matching       : 0.00
% 5.85/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
