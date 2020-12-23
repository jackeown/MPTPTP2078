%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:25 EST 2020

% Result     : Theorem 8.46s
% Output     : CNFRefutation 8.46s
% Verified   : 
% Statistics : Number of formulae       :  223 (1212 expanded)
%              Number of leaves         :   42 ( 425 expanded)
%              Depth                    :   13
%              Number of atoms          :  397 (3277 expanded)
%              Number of equality atoms :  129 ( 751 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_151,axiom,(
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

tff(f_161,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_7873,plain,(
    ! [C_360,A_361,B_362] :
      ( v1_relat_1(C_360)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(A_361,B_362))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7885,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_7873])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_74,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_9992,plain,(
    ! [A_454] :
      ( k4_relat_1(A_454) = k2_funct_1(A_454)
      | ~ v2_funct_1(A_454)
      | ~ v1_funct_1(A_454)
      | ~ v1_relat_1(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_9998,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_9992])).

tff(c_10002,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7885,c_80,c_9998])).

tff(c_14,plain,(
    ! [A_6] :
      ( v1_xboole_0(k4_relat_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10012,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10002,c_14])).

tff(c_10021,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10012])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,(
    ! [A_7] :
      ( k1_relat_1(A_7) = k1_xboole_0
      | k2_relat_1(A_7) != k1_xboole_0
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7894,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7885,c_16])).

tff(c_7904,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7894])).

tff(c_72,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_8453,plain,(
    ! [A_396,B_397,C_398] :
      ( k2_relset_1(A_396,B_397,C_398) = k2_relat_1(C_398)
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1(A_396,B_397))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8462,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_8453])).

tff(c_8470,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8462])).

tff(c_36,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1708,plain,(
    ! [C_138,A_139,B_140] :
      ( v1_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1716,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1708])).

tff(c_5077,plain,(
    ! [A_247] :
      ( k4_relat_1(A_247) = k2_funct_1(A_247)
      | ~ v2_funct_1(A_247)
      | ~ v1_funct_1(A_247)
      | ~ v1_relat_1(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5083,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_5077])).

tff(c_5087,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_80,c_5083])).

tff(c_12,plain,(
    ! [A_6] :
      ( v1_relat_1(k4_relat_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5100,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5087,c_12])).

tff(c_5127,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5100])).

tff(c_30,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_242,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_245,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_242])).

tff(c_248,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_245])).

tff(c_266,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_269,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_266])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_269])).

tff(c_278,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_280,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_2102,plain,(
    ! [A_164,B_165,C_166] :
      ( k2_relset_1(A_164,B_165,C_166) = k2_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2105,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2102])).

tff(c_2111,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2105])).

tff(c_1725,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1716,c_16])).

tff(c_1727,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1725])).

tff(c_2114,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2111,c_1727])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2257,plain,(
    ! [A_174,B_175,C_176] :
      ( k1_relset_1(A_174,B_175,C_176) = k1_relat_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2273,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2257])).

tff(c_3488,plain,(
    ! [B_214,A_215,C_216] :
      ( k1_xboole_0 = B_214
      | k1_relset_1(A_215,B_214,C_216) = A_215
      | ~ v1_funct_2(C_216,A_215,B_214)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_215,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_3497,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_3488])).

tff(c_3509,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2273,c_3497])).

tff(c_3510,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2114,c_3509])).

tff(c_34,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_279,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1915,plain,(
    ! [A_156] :
      ( k2_relat_1(k2_funct_1(A_156)) = k1_relat_1(A_156)
      | ~ v2_funct_1(A_156)
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    ! [A_36] :
      ( v1_funct_2(A_36,k1_relat_1(A_36),k2_relat_1(A_36))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3782,plain,(
    ! [A_231] :
      ( v1_funct_2(k2_funct_1(A_231),k1_relat_1(k2_funct_1(A_231)),k1_relat_1(A_231))
      | ~ v1_funct_1(k2_funct_1(A_231))
      | ~ v1_relat_1(k2_funct_1(A_231))
      | ~ v2_funct_1(A_231)
      | ~ v1_funct_1(A_231)
      | ~ v1_relat_1(A_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1915,c_66])).

tff(c_3785,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3510,c_3782])).

tff(c_3805,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_80,c_74,c_279,c_3785])).

tff(c_3812,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3805])).

tff(c_3815,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_3812])).

tff(c_3819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_80,c_3815])).

tff(c_3821,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3805])).

tff(c_2124,plain,(
    ! [A_167] :
      ( m1_subset_1(A_167,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_167),k2_relat_1(A_167))))
      | ~ v1_funct_1(A_167)
      | ~ v1_relat_1(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_4925,plain,(
    ! [A_241] :
      ( m1_subset_1(k2_funct_1(A_241),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_241),k2_relat_1(k2_funct_1(A_241)))))
      | ~ v1_funct_1(k2_funct_1(A_241))
      | ~ v1_relat_1(k2_funct_1(A_241))
      | ~ v2_funct_1(A_241)
      | ~ v1_funct_1(A_241)
      | ~ v1_relat_1(A_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2124])).

tff(c_4961,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2111,c_4925])).

tff(c_4989,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_80,c_74,c_3821,c_279,c_4961])).

tff(c_5025,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4989])).

tff(c_5045,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_80,c_74,c_3510,c_5025])).

tff(c_5047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_5045])).

tff(c_5049,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1725])).

tff(c_5441,plain,(
    ! [A_269,B_270,C_271] :
      ( k2_relset_1(A_269,B_270,C_271) = k2_relat_1(C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5444,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_5441])).

tff(c_5450,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5049,c_72,c_5444])).

tff(c_5476,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5450,c_2])).

tff(c_54,plain,(
    ! [C_35,A_33] :
      ( k1_xboole_0 = C_35
      | ~ v1_funct_2(C_35,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_5721,plain,(
    ! [C_280,A_281] :
      ( C_280 = '#skF_3'
      | ~ v1_funct_2(C_280,A_281,'#skF_3')
      | A_281 = '#skF_3'
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(A_281,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5450,c_5450,c_5450,c_5450,c_54])).

tff(c_5728,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_76,c_5721])).

tff(c_5733,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5728])).

tff(c_5734,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5733])).

tff(c_5129,plain,(
    ! [C_249,A_250,B_251] :
      ( v1_xboole_0(C_249)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251)))
      | ~ v1_xboole_0(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5132,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_5129])).

tff(c_5139,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_5127,c_5132])).

tff(c_5736,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5734,c_5139])).

tff(c_5743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5476,c_5736])).

tff(c_5744,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5733])).

tff(c_5763,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5744,c_5476])).

tff(c_5772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5127,c_5763])).

tff(c_5774,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5100])).

tff(c_117,plain,(
    ! [B_45,A_46] :
      ( ~ v1_xboole_0(B_45)
      | B_45 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_126,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_2,c_117])).

tff(c_5838,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5774,c_126])).

tff(c_6,plain,(
    ! [A_3] : v1_xboole_0('#skF_1'(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_127,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_2,c_117])).

tff(c_138,plain,(
    ! [A_3] : '#skF_1'(A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_127])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1('#skF_1'(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_141,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_8])).

tff(c_5856,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5838,c_141])).

tff(c_137,plain,(
    ! [A_6] :
      ( k4_relat_1(A_6) = k1_xboole_0
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_127])).

tff(c_5837,plain,(
    k4_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5774,c_137])).

tff(c_5944,plain,(
    k4_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5838,c_5837])).

tff(c_5945,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5944,c_5087])).

tff(c_5981,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5945,c_280])).

tff(c_6022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5856,c_5981])).

tff(c_6023,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_8473,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8470,c_7904])).

tff(c_8332,plain,(
    ! [A_387,B_388,C_389] :
      ( k1_relset_1(A_387,B_388,C_389) = k1_relat_1(C_389)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(A_387,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8344,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_8332])).

tff(c_9693,plain,(
    ! [B_432,A_433,C_434] :
      ( k1_xboole_0 = B_432
      | k1_relset_1(A_433,B_432,C_434) = A_433
      | ~ v1_funct_2(C_434,A_433,B_432)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_433,B_432))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_9705,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_9693])).

tff(c_9719,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_8344,c_9705])).

tff(c_9720,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_8473,c_9719])).

tff(c_18,plain,(
    ! [A_7] :
      ( k2_relat_1(A_7) = k1_xboole_0
      | k1_relat_1(A_7) != k1_xboole_0
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7895,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7885,c_18])).

tff(c_7905,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7895])).

tff(c_9729,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9720,c_7905])).

tff(c_6024,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_8343,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6024,c_8332])).

tff(c_9816,plain,(
    ! [B_440,C_441,A_442] :
      ( k1_xboole_0 = B_440
      | v1_funct_2(C_441,A_442,B_440)
      | k1_relset_1(A_442,B_440,C_441) != A_442
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(A_442,B_440))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_9822,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_6024,c_9816])).

tff(c_9832,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8343,c_9822])).

tff(c_9833,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_6023,c_9729,c_9832])).

tff(c_9842,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_9833])).

tff(c_9845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7885,c_80,c_74,c_8470,c_9842])).

tff(c_9846,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7895])).

tff(c_9848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7904,c_9846])).

tff(c_9849,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7894])).

tff(c_9850,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7894])).

tff(c_10383,plain,(
    ! [A_472] :
      ( m1_subset_1(A_472,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_472),k2_relat_1(A_472))))
      | ~ v1_funct_1(A_472)
      | ~ v1_relat_1(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_10413,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0)))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9850,c_10383])).

tff(c_10431,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7885,c_80,c_9849,c_10413])).

tff(c_40,plain,(
    ! [C_19,A_16,B_17] :
      ( v1_xboole_0(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10444,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10431,c_40])).

tff(c_10453,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10444])).

tff(c_10455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10021,c_10453])).

tff(c_10457,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_10012])).

tff(c_10480,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10457,c_126])).

tff(c_6266,plain,(
    ! [C_306,A_307,B_308] :
      ( v1_partfun1(C_306,A_307)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(k2_zfmisc_1(A_307,B_308)))
      | ~ v1_xboole_0(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6279,plain,(
    ! [A_307] :
      ( v1_partfun1(k1_xboole_0,A_307)
      | ~ v1_xboole_0(A_307) ) ),
    inference(resolution,[status(thm)],[c_141,c_6266])).

tff(c_92,plain,(
    ! [A_40] :
      ( v1_funct_1(A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_100,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_92])).

tff(c_7528,plain,(
    ! [C_350,A_351,B_352] :
      ( v1_funct_2(C_350,A_351,B_352)
      | ~ v1_partfun1(C_350,A_351)
      | ~ v1_funct_1(C_350)
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_7544,plain,(
    ! [A_351,B_352] :
      ( v1_funct_2(k1_xboole_0,A_351,B_352)
      | ~ v1_partfun1(k1_xboole_0,A_351)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_141,c_7528])).

tff(c_7558,plain,(
    ! [A_351,B_352] :
      ( v1_funct_2(k1_xboole_0,A_351,B_352)
      | ~ v1_partfun1(k1_xboole_0,A_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_7544])).

tff(c_82,plain,(
    ! [A_38] :
      ( v1_relat_1(A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_229,plain,(
    ! [A_57] :
      ( k2_relat_1(A_57) = k1_xboole_0
      | k1_relat_1(A_57) != k1_xboole_0
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_241,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_229])).

tff(c_6025,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_6923,plain,(
    ! [A_334,B_335,C_336] :
      ( k1_relset_1(A_334,B_335,C_336) = k1_relat_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6944,plain,(
    ! [A_334,B_335] : k1_relset_1(A_334,B_335,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_141,c_6923])).

tff(c_7821,plain,(
    ! [B_356,C_357] :
      ( k1_relset_1(k1_xboole_0,B_356,C_357) = k1_xboole_0
      | ~ v1_funct_2(C_357,k1_xboole_0,B_356)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_356))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_7825,plain,(
    ! [B_356] :
      ( k1_relset_1(k1_xboole_0,B_356,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_356) ) ),
    inference(resolution,[status(thm)],[c_141,c_7821])).

tff(c_7827,plain,(
    ! [B_356] :
      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_356) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6944,c_7825])).

tff(c_7829,plain,(
    ! [B_358] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_358) ),
    inference(negUnitSimplification,[status(thm)],[c_6025,c_7827])).

tff(c_7838,plain,(
    ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7558,c_7829])).

tff(c_7843,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6279,c_7838])).

tff(c_7847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7843])).

tff(c_7849,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_10514,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10480,c_10480,c_7849])).

tff(c_10520,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10480,c_141])).

tff(c_10981,plain,(
    ! [A_499,B_500,C_501] :
      ( k1_relset_1(A_499,B_500,C_501) = k1_relat_1(C_501)
      | ~ m1_subset_1(C_501,k1_zfmisc_1(k2_zfmisc_1(A_499,B_500))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10985,plain,(
    ! [A_499,B_500] : k1_relset_1(A_499,B_500,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10520,c_10981])).

tff(c_10987,plain,(
    ! [A_499,B_500] : k1_relset_1(A_499,B_500,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10514,c_10985])).

tff(c_56,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_11417,plain,(
    ! [C_525,B_526] :
      ( v1_funct_2(C_525,'#skF_4',B_526)
      | k1_relset_1('#skF_4',B_526,C_525) != '#skF_4'
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_526))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10480,c_10480,c_10480,c_10480,c_56])).

tff(c_11421,plain,(
    ! [B_526] :
      ( v1_funct_2('#skF_4','#skF_4',B_526)
      | k1_relset_1('#skF_4',B_526,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_10520,c_11417])).

tff(c_11424,plain,(
    ! [B_526] : v1_funct_2('#skF_4','#skF_4',B_526) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10987,c_11421])).

tff(c_7848,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_10515,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10480,c_10480,c_7848])).

tff(c_11360,plain,(
    ! [A_515,B_516,C_517] :
      ( k2_relset_1(A_515,B_516,C_517) = k2_relat_1(C_517)
      | ~ m1_subset_1(C_517,k1_zfmisc_1(k2_zfmisc_1(A_515,B_516))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_11367,plain,(
    ! [A_515,B_516] : k2_relset_1(A_515,B_516,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10520,c_11360])).

tff(c_11370,plain,(
    ! [A_515,B_516] : k2_relset_1(A_515,B_516,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10515,c_11367])).

tff(c_11371,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11370,c_72])).

tff(c_158,plain,(
    ! [A_51] :
      ( k4_relat_1(A_51) = k1_xboole_0
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_14,c_127])).

tff(c_166,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_158])).

tff(c_10518,plain,(
    k4_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10480,c_10480,c_166])).

tff(c_10560,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10518,c_10002])).

tff(c_10603,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10560,c_6023])).

tff(c_11379,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11371,c_10603])).

tff(c_11428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11424,c_11379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.46/2.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.46/2.78  
% 8.46/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.46/2.78  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 8.46/2.78  
% 8.46/2.78  %Foreground sorts:
% 8.46/2.78  
% 8.46/2.78  
% 8.46/2.78  %Background operators:
% 8.46/2.78  
% 8.46/2.78  
% 8.46/2.78  %Foreground operators:
% 8.46/2.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.46/2.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.46/2.78  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.46/2.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.46/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.46/2.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.46/2.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.46/2.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.46/2.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.46/2.78  tff('#skF_2', type, '#skF_2': $i).
% 8.46/2.78  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.46/2.78  tff('#skF_3', type, '#skF_3': $i).
% 8.46/2.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.46/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.46/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.46/2.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.46/2.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.46/2.78  tff('#skF_4', type, '#skF_4': $i).
% 8.46/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.46/2.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.46/2.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.46/2.78  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.46/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.46/2.78  
% 8.46/2.81  tff(f_178, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 8.46/2.81  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.46/2.81  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 8.46/2.81  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_relat_1)).
% 8.46/2.81  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.46/2.81  tff(f_55, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 8.46/2.81  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.46/2.81  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 8.46/2.81  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.46/2.81  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.46/2.81  tff(f_151, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.46/2.81  tff(f_161, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 8.46/2.81  tff(f_108, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 8.46/2.81  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 8.46/2.81  tff(f_39, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 8.46/2.81  tff(f_133, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 8.46/2.81  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 8.46/2.81  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 8.46/2.81  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 8.46/2.81  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.46/2.81  tff(c_7873, plain, (![C_360, A_361, B_362]: (v1_relat_1(C_360) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(A_361, B_362))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.46/2.81  tff(c_7885, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_7873])).
% 8.46/2.81  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.46/2.81  tff(c_74, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.46/2.81  tff(c_9992, plain, (![A_454]: (k4_relat_1(A_454)=k2_funct_1(A_454) | ~v2_funct_1(A_454) | ~v1_funct_1(A_454) | ~v1_relat_1(A_454))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.46/2.81  tff(c_9998, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_9992])).
% 8.46/2.81  tff(c_10002, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7885, c_80, c_9998])).
% 8.46/2.81  tff(c_14, plain, (![A_6]: (v1_xboole_0(k4_relat_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.46/2.81  tff(c_10012, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10002, c_14])).
% 8.46/2.81  tff(c_10021, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_10012])).
% 8.46/2.81  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.46/2.81  tff(c_16, plain, (![A_7]: (k1_relat_1(A_7)=k1_xboole_0 | k2_relat_1(A_7)!=k1_xboole_0 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.46/2.81  tff(c_7894, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_7885, c_16])).
% 8.46/2.81  tff(c_7904, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7894])).
% 8.46/2.81  tff(c_72, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.46/2.81  tff(c_8453, plain, (![A_396, B_397, C_398]: (k2_relset_1(A_396, B_397, C_398)=k2_relat_1(C_398) | ~m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1(A_396, B_397))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.46/2.81  tff(c_8462, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_8453])).
% 8.46/2.81  tff(c_8470, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_8462])).
% 8.46/2.81  tff(c_36, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.46/2.81  tff(c_1708, plain, (![C_138, A_139, B_140]: (v1_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.46/2.81  tff(c_1716, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1708])).
% 8.46/2.81  tff(c_5077, plain, (![A_247]: (k4_relat_1(A_247)=k2_funct_1(A_247) | ~v2_funct_1(A_247) | ~v1_funct_1(A_247) | ~v1_relat_1(A_247))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.46/2.81  tff(c_5083, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_5077])).
% 8.46/2.81  tff(c_5087, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1716, c_80, c_5083])).
% 8.46/2.81  tff(c_12, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.46/2.81  tff(c_5100, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5087, c_12])).
% 8.46/2.81  tff(c_5127, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_5100])).
% 8.46/2.81  tff(c_30, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.46/2.81  tff(c_70, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.46/2.81  tff(c_242, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_70])).
% 8.46/2.81  tff(c_245, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_242])).
% 8.46/2.81  tff(c_248, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_245])).
% 8.46/2.81  tff(c_266, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.46/2.81  tff(c_269, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_266])).
% 8.46/2.81  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248, c_269])).
% 8.46/2.81  tff(c_278, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_70])).
% 8.46/2.81  tff(c_280, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_278])).
% 8.46/2.81  tff(c_2102, plain, (![A_164, B_165, C_166]: (k2_relset_1(A_164, B_165, C_166)=k2_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.46/2.81  tff(c_2105, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2102])).
% 8.46/2.81  tff(c_2111, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2105])).
% 8.46/2.81  tff(c_1725, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1716, c_16])).
% 8.46/2.81  tff(c_1727, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1725])).
% 8.46/2.81  tff(c_2114, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2111, c_1727])).
% 8.46/2.81  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.46/2.81  tff(c_2257, plain, (![A_174, B_175, C_176]: (k1_relset_1(A_174, B_175, C_176)=k1_relat_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.46/2.81  tff(c_2273, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2257])).
% 8.46/2.81  tff(c_3488, plain, (![B_214, A_215, C_216]: (k1_xboole_0=B_214 | k1_relset_1(A_215, B_214, C_216)=A_215 | ~v1_funct_2(C_216, A_215, B_214) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_215, B_214))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.46/2.81  tff(c_3497, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_3488])).
% 8.46/2.81  tff(c_3509, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2273, c_3497])).
% 8.46/2.81  tff(c_3510, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2114, c_3509])).
% 8.46/2.81  tff(c_34, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.46/2.81  tff(c_32, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.46/2.81  tff(c_279, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_70])).
% 8.46/2.81  tff(c_1915, plain, (![A_156]: (k2_relat_1(k2_funct_1(A_156))=k1_relat_1(A_156) | ~v2_funct_1(A_156) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.46/2.81  tff(c_66, plain, (![A_36]: (v1_funct_2(A_36, k1_relat_1(A_36), k2_relat_1(A_36)) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.46/2.81  tff(c_3782, plain, (![A_231]: (v1_funct_2(k2_funct_1(A_231), k1_relat_1(k2_funct_1(A_231)), k1_relat_1(A_231)) | ~v1_funct_1(k2_funct_1(A_231)) | ~v1_relat_1(k2_funct_1(A_231)) | ~v2_funct_1(A_231) | ~v1_funct_1(A_231) | ~v1_relat_1(A_231))), inference(superposition, [status(thm), theory('equality')], [c_1915, c_66])).
% 8.46/2.81  tff(c_3785, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3510, c_3782])).
% 8.46/2.81  tff(c_3805, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1716, c_80, c_74, c_279, c_3785])).
% 8.46/2.81  tff(c_3812, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3805])).
% 8.46/2.81  tff(c_3815, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_3812])).
% 8.46/2.81  tff(c_3819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1716, c_80, c_3815])).
% 8.46/2.81  tff(c_3821, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3805])).
% 8.46/2.81  tff(c_2124, plain, (![A_167]: (m1_subset_1(A_167, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_167), k2_relat_1(A_167)))) | ~v1_funct_1(A_167) | ~v1_relat_1(A_167))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.46/2.81  tff(c_4925, plain, (![A_241]: (m1_subset_1(k2_funct_1(A_241), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_241), k2_relat_1(k2_funct_1(A_241))))) | ~v1_funct_1(k2_funct_1(A_241)) | ~v1_relat_1(k2_funct_1(A_241)) | ~v2_funct_1(A_241) | ~v1_funct_1(A_241) | ~v1_relat_1(A_241))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2124])).
% 8.46/2.81  tff(c_4961, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2111, c_4925])).
% 8.46/2.81  tff(c_4989, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_1716, c_80, c_74, c_3821, c_279, c_4961])).
% 8.46/2.81  tff(c_5025, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34, c_4989])).
% 8.46/2.81  tff(c_5045, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1716, c_80, c_74, c_3510, c_5025])).
% 8.46/2.81  tff(c_5047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_5045])).
% 8.46/2.81  tff(c_5049, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1725])).
% 8.46/2.81  tff(c_5441, plain, (![A_269, B_270, C_271]: (k2_relset_1(A_269, B_270, C_271)=k2_relat_1(C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.46/2.81  tff(c_5444, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_5441])).
% 8.46/2.81  tff(c_5450, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5049, c_72, c_5444])).
% 8.46/2.81  tff(c_5476, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5450, c_2])).
% 8.46/2.81  tff(c_54, plain, (![C_35, A_33]: (k1_xboole_0=C_35 | ~v1_funct_2(C_35, A_33, k1_xboole_0) | k1_xboole_0=A_33 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.46/2.81  tff(c_5721, plain, (![C_280, A_281]: (C_280='#skF_3' | ~v1_funct_2(C_280, A_281, '#skF_3') | A_281='#skF_3' | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(A_281, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_5450, c_5450, c_5450, c_5450, c_54])).
% 8.46/2.81  tff(c_5728, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_76, c_5721])).
% 8.46/2.81  tff(c_5733, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_5728])).
% 8.46/2.81  tff(c_5734, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_5733])).
% 8.46/2.81  tff(c_5129, plain, (![C_249, A_250, B_251]: (v1_xboole_0(C_249) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))) | ~v1_xboole_0(A_250))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.46/2.81  tff(c_5132, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_5129])).
% 8.46/2.81  tff(c_5139, plain, (~v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_5127, c_5132])).
% 8.46/2.81  tff(c_5736, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5734, c_5139])).
% 8.46/2.81  tff(c_5743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5476, c_5736])).
% 8.46/2.81  tff(c_5744, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_5733])).
% 8.46/2.81  tff(c_5763, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5744, c_5476])).
% 8.46/2.81  tff(c_5772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5127, c_5763])).
% 8.46/2.81  tff(c_5774, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_5100])).
% 8.46/2.81  tff(c_117, plain, (![B_45, A_46]: (~v1_xboole_0(B_45) | B_45=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.46/2.81  tff(c_126, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_2, c_117])).
% 8.46/2.81  tff(c_5838, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_5774, c_126])).
% 8.46/2.81  tff(c_6, plain, (![A_3]: (v1_xboole_0('#skF_1'(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.46/2.81  tff(c_127, plain, (![A_47]: (k1_xboole_0=A_47 | ~v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_2, c_117])).
% 8.46/2.81  tff(c_138, plain, (![A_3]: ('#skF_1'(A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_127])).
% 8.46/2.81  tff(c_8, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.46/2.81  tff(c_141, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_8])).
% 8.46/2.81  tff(c_5856, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_5838, c_141])).
% 8.46/2.81  tff(c_137, plain, (![A_6]: (k4_relat_1(A_6)=k1_xboole_0 | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_14, c_127])).
% 8.46/2.81  tff(c_5837, plain, (k4_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_5774, c_137])).
% 8.46/2.81  tff(c_5944, plain, (k4_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5838, c_5837])).
% 8.46/2.81  tff(c_5945, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5944, c_5087])).
% 8.46/2.81  tff(c_5981, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5945, c_280])).
% 8.46/2.81  tff(c_6022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5856, c_5981])).
% 8.46/2.81  tff(c_6023, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_278])).
% 8.46/2.81  tff(c_8473, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8470, c_7904])).
% 8.46/2.81  tff(c_8332, plain, (![A_387, B_388, C_389]: (k1_relset_1(A_387, B_388, C_389)=k1_relat_1(C_389) | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(A_387, B_388))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.46/2.81  tff(c_8344, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_8332])).
% 8.46/2.81  tff(c_9693, plain, (![B_432, A_433, C_434]: (k1_xboole_0=B_432 | k1_relset_1(A_433, B_432, C_434)=A_433 | ~v1_funct_2(C_434, A_433, B_432) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_433, B_432))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.46/2.81  tff(c_9705, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_9693])).
% 8.46/2.81  tff(c_9719, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_8344, c_9705])).
% 8.46/2.81  tff(c_9720, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_8473, c_9719])).
% 8.46/2.81  tff(c_18, plain, (![A_7]: (k2_relat_1(A_7)=k1_xboole_0 | k1_relat_1(A_7)!=k1_xboole_0 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.46/2.81  tff(c_7895, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_7885, c_18])).
% 8.46/2.81  tff(c_7905, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7895])).
% 8.46/2.81  tff(c_9729, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9720, c_7905])).
% 8.46/2.81  tff(c_6024, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_278])).
% 8.46/2.81  tff(c_8343, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6024, c_8332])).
% 8.46/2.81  tff(c_9816, plain, (![B_440, C_441, A_442]: (k1_xboole_0=B_440 | v1_funct_2(C_441, A_442, B_440) | k1_relset_1(A_442, B_440, C_441)!=A_442 | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(A_442, B_440))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.46/2.81  tff(c_9822, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_6024, c_9816])).
% 8.46/2.81  tff(c_9832, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8343, c_9822])).
% 8.46/2.81  tff(c_9833, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_6023, c_9729, c_9832])).
% 8.46/2.81  tff(c_9842, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_9833])).
% 8.46/2.81  tff(c_9845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7885, c_80, c_74, c_8470, c_9842])).
% 8.46/2.81  tff(c_9846, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7895])).
% 8.46/2.81  tff(c_9848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7904, c_9846])).
% 8.46/2.81  tff(c_9849, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7894])).
% 8.46/2.81  tff(c_9850, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7894])).
% 8.46/2.81  tff(c_10383, plain, (![A_472]: (m1_subset_1(A_472, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_472), k2_relat_1(A_472)))) | ~v1_funct_1(A_472) | ~v1_relat_1(A_472))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.46/2.81  tff(c_10413, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9850, c_10383])).
% 8.46/2.81  tff(c_10431, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_7885, c_80, c_9849, c_10413])).
% 8.46/2.81  tff(c_40, plain, (![C_19, A_16, B_17]: (v1_xboole_0(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.46/2.81  tff(c_10444, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_10431, c_40])).
% 8.46/2.81  tff(c_10453, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10444])).
% 8.46/2.81  tff(c_10455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10021, c_10453])).
% 8.46/2.81  tff(c_10457, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_10012])).
% 8.46/2.81  tff(c_10480, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10457, c_126])).
% 8.46/2.81  tff(c_6266, plain, (![C_306, A_307, B_308]: (v1_partfun1(C_306, A_307) | ~m1_subset_1(C_306, k1_zfmisc_1(k2_zfmisc_1(A_307, B_308))) | ~v1_xboole_0(A_307))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.46/2.81  tff(c_6279, plain, (![A_307]: (v1_partfun1(k1_xboole_0, A_307) | ~v1_xboole_0(A_307))), inference(resolution, [status(thm)], [c_141, c_6266])).
% 8.46/2.81  tff(c_92, plain, (![A_40]: (v1_funct_1(A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.46/2.81  tff(c_100, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_92])).
% 8.46/2.81  tff(c_7528, plain, (![C_350, A_351, B_352]: (v1_funct_2(C_350, A_351, B_352) | ~v1_partfun1(C_350, A_351) | ~v1_funct_1(C_350) | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.46/2.81  tff(c_7544, plain, (![A_351, B_352]: (v1_funct_2(k1_xboole_0, A_351, B_352) | ~v1_partfun1(k1_xboole_0, A_351) | ~v1_funct_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_141, c_7528])).
% 8.46/2.81  tff(c_7558, plain, (![A_351, B_352]: (v1_funct_2(k1_xboole_0, A_351, B_352) | ~v1_partfun1(k1_xboole_0, A_351))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_7544])).
% 8.46/2.81  tff(c_82, plain, (![A_38]: (v1_relat_1(A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.46/2.81  tff(c_90, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_82])).
% 8.46/2.81  tff(c_229, plain, (![A_57]: (k2_relat_1(A_57)=k1_xboole_0 | k1_relat_1(A_57)!=k1_xboole_0 | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.46/2.81  tff(c_241, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_90, c_229])).
% 8.46/2.81  tff(c_6025, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_241])).
% 8.46/2.81  tff(c_6923, plain, (![A_334, B_335, C_336]: (k1_relset_1(A_334, B_335, C_336)=k1_relat_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.46/2.81  tff(c_6944, plain, (![A_334, B_335]: (k1_relset_1(A_334, B_335, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_141, c_6923])).
% 8.46/2.81  tff(c_7821, plain, (![B_356, C_357]: (k1_relset_1(k1_xboole_0, B_356, C_357)=k1_xboole_0 | ~v1_funct_2(C_357, k1_xboole_0, B_356) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_356))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.46/2.81  tff(c_7825, plain, (![B_356]: (k1_relset_1(k1_xboole_0, B_356, k1_xboole_0)=k1_xboole_0 | ~v1_funct_2(k1_xboole_0, k1_xboole_0, B_356))), inference(resolution, [status(thm)], [c_141, c_7821])).
% 8.46/2.81  tff(c_7827, plain, (![B_356]: (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_funct_2(k1_xboole_0, k1_xboole_0, B_356))), inference(demodulation, [status(thm), theory('equality')], [c_6944, c_7825])).
% 8.46/2.81  tff(c_7829, plain, (![B_358]: (~v1_funct_2(k1_xboole_0, k1_xboole_0, B_358))), inference(negUnitSimplification, [status(thm)], [c_6025, c_7827])).
% 8.46/2.81  tff(c_7838, plain, (~v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_7558, c_7829])).
% 8.46/2.81  tff(c_7843, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6279, c_7838])).
% 8.46/2.81  tff(c_7847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_7843])).
% 8.46/2.81  tff(c_7849, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_241])).
% 8.46/2.81  tff(c_10514, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10480, c_10480, c_7849])).
% 8.46/2.81  tff(c_10520, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_10480, c_141])).
% 8.46/2.81  tff(c_10981, plain, (![A_499, B_500, C_501]: (k1_relset_1(A_499, B_500, C_501)=k1_relat_1(C_501) | ~m1_subset_1(C_501, k1_zfmisc_1(k2_zfmisc_1(A_499, B_500))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.46/2.81  tff(c_10985, plain, (![A_499, B_500]: (k1_relset_1(A_499, B_500, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_10520, c_10981])).
% 8.46/2.81  tff(c_10987, plain, (![A_499, B_500]: (k1_relset_1(A_499, B_500, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10514, c_10985])).
% 8.46/2.81  tff(c_56, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.46/2.81  tff(c_11417, plain, (![C_525, B_526]: (v1_funct_2(C_525, '#skF_4', B_526) | k1_relset_1('#skF_4', B_526, C_525)!='#skF_4' | ~m1_subset_1(C_525, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_526))))), inference(demodulation, [status(thm), theory('equality')], [c_10480, c_10480, c_10480, c_10480, c_56])).
% 8.46/2.81  tff(c_11421, plain, (![B_526]: (v1_funct_2('#skF_4', '#skF_4', B_526) | k1_relset_1('#skF_4', B_526, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_10520, c_11417])).
% 8.46/2.81  tff(c_11424, plain, (![B_526]: (v1_funct_2('#skF_4', '#skF_4', B_526))), inference(demodulation, [status(thm), theory('equality')], [c_10987, c_11421])).
% 8.46/2.81  tff(c_7848, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_241])).
% 8.46/2.81  tff(c_10515, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10480, c_10480, c_7848])).
% 8.46/2.81  tff(c_11360, plain, (![A_515, B_516, C_517]: (k2_relset_1(A_515, B_516, C_517)=k2_relat_1(C_517) | ~m1_subset_1(C_517, k1_zfmisc_1(k2_zfmisc_1(A_515, B_516))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.46/2.81  tff(c_11367, plain, (![A_515, B_516]: (k2_relset_1(A_515, B_516, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_10520, c_11360])).
% 8.46/2.81  tff(c_11370, plain, (![A_515, B_516]: (k2_relset_1(A_515, B_516, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10515, c_11367])).
% 8.46/2.81  tff(c_11371, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11370, c_72])).
% 8.46/2.81  tff(c_158, plain, (![A_51]: (k4_relat_1(A_51)=k1_xboole_0 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_14, c_127])).
% 8.46/2.81  tff(c_166, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_158])).
% 8.46/2.81  tff(c_10518, plain, (k4_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10480, c_10480, c_166])).
% 8.46/2.81  tff(c_10560, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10518, c_10002])).
% 8.46/2.81  tff(c_10603, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10560, c_6023])).
% 8.46/2.81  tff(c_11379, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11371, c_10603])).
% 8.46/2.81  tff(c_11428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11424, c_11379])).
% 8.46/2.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.46/2.81  
% 8.46/2.81  Inference rules
% 8.46/2.81  ----------------------
% 8.46/2.81  #Ref     : 0
% 8.46/2.81  #Sup     : 2935
% 8.46/2.81  #Fact    : 0
% 8.46/2.81  #Define  : 0
% 8.46/2.81  #Split   : 61
% 8.46/2.81  #Chain   : 0
% 8.46/2.81  #Close   : 0
% 8.46/2.81  
% 8.46/2.81  Ordering : KBO
% 8.46/2.81  
% 8.46/2.81  Simplification rules
% 8.46/2.81  ----------------------
% 8.46/2.81  #Subsume      : 936
% 8.46/2.81  #Demod        : 2159
% 8.46/2.81  #Tautology    : 974
% 8.46/2.81  #SimpNegUnit  : 49
% 8.46/2.81  #BackRed      : 130
% 8.46/2.81  
% 8.46/2.81  #Partial instantiations: 0
% 8.46/2.81  #Strategies tried      : 1
% 8.46/2.81  
% 8.46/2.81  Timing (in seconds)
% 8.46/2.81  ----------------------
% 8.85/2.81  Preprocessing        : 0.35
% 8.85/2.81  Parsing              : 0.19
% 8.85/2.81  CNF conversion       : 0.02
% 8.85/2.81  Main loop            : 1.67
% 8.85/2.81  Inferencing          : 0.52
% 8.85/2.81  Reduction            : 0.54
% 8.85/2.81  Demodulation         : 0.38
% 8.85/2.81  BG Simplification    : 0.06
% 8.85/2.81  Subsumption          : 0.42
% 8.85/2.81  Abstraction          : 0.07
% 8.85/2.81  MUC search           : 0.00
% 8.85/2.81  Cooper               : 0.00
% 8.85/2.81  Total                : 2.08
% 8.85/2.81  Index Insertion      : 0.00
% 8.85/2.82  Index Deletion       : 0.00
% 8.85/2.82  Index Matching       : 0.00
% 8.85/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
