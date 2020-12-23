%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:53 EST 2020

% Result     : Theorem 8.02s
% Output     : CNFRefutation 8.33s
% Verified   : 
% Statistics : Number of formulae       :  194 (1066 expanded)
%              Number of leaves         :   47 ( 363 expanded)
%              Depth                    :   16
%              Number of atoms          :  341 (3008 expanded)
%              Number of equality atoms :   94 ( 617 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_190,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_124,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_168,axiom,(
    ! [A,B,C] :
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

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_49,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_129,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_145,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_129])).

tff(c_163,plain,(
    ! [C_65,B_66,A_67] :
      ( v5_relat_1(C_65,B_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_179,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_163])).

tff(c_4980,plain,(
    ! [B_300,A_301] :
      ( k2_relat_1(B_300) = A_301
      | ~ v2_funct_2(B_300,A_301)
      | ~ v5_relat_1(B_300,A_301)
      | ~ v1_relat_1(B_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4989,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_179,c_4980])).

tff(c_4998,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_4989])).

tff(c_5005,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4998])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_62,plain,(
    v3_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_5090,plain,(
    ! [C_315,B_316,A_317] :
      ( v2_funct_2(C_315,B_316)
      | ~ v3_funct_2(C_315,A_317,B_316)
      | ~ v1_funct_1(C_315)
      | ~ m1_subset_1(C_315,k1_zfmisc_1(k2_zfmisc_1(A_317,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_5100,plain,
    ( v2_funct_2('#skF_4','#skF_2')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_5090])).

tff(c_5107,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_5100])).

tff(c_5109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5005,c_5107])).

tff(c_5110,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4998])).

tff(c_931,plain,(
    ! [A_147,B_148,D_149] :
      ( r2_relset_1(A_147,B_148,D_149,D_149)
      | ~ m1_subset_1(D_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_943,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_931])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_146,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_129])).

tff(c_180,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_163])).

tff(c_272,plain,(
    ! [B_83,A_84] :
      ( k2_relat_1(B_83) = A_84
      | ~ v2_funct_2(B_83,A_84)
      | ~ v5_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_281,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_272])).

tff(c_293,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_281])).

tff(c_333,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_70,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_680,plain,(
    ! [C_124,B_125,A_126] :
      ( v2_funct_2(C_124,B_125)
      | ~ v3_funct_2(C_124,A_126,B_125)
      | ~ v1_funct_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_693,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_680])).

tff(c_701,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_693])).

tff(c_703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_333,c_701])).

tff(c_704,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_10,plain,(
    ! [A_5] :
      ( k2_relat_1(A_5) != k1_xboole_0
      | k1_xboole_0 = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_161,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_146,c_10])).

tff(c_224,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_706,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_224])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_946,plain,(
    ! [A_152,B_153,C_154] :
      ( k2_relset_1(A_152,B_153,C_154) = k2_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_959,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_946])).

tff(c_965,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_959])).

tff(c_48,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_75,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_30])).

tff(c_941,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_75,c_931])).

tff(c_1003,plain,(
    ! [C_160,A_161,B_162] :
      ( v2_funct_1(C_160)
      | ~ v3_funct_2(C_160,A_161,B_162)
      | ~ v1_funct_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1016,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1003])).

tff(c_1024,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_1016])).

tff(c_2038,plain,(
    ! [A_209,C_206,F_208,D_211,E_210,B_207] :
      ( m1_subset_1(k1_partfun1(A_209,B_207,C_206,D_211,E_210,F_208),k1_zfmisc_1(k2_zfmisc_1(A_209,D_211)))
      | ~ m1_subset_1(F_208,k1_zfmisc_1(k2_zfmisc_1(C_206,D_211)))
      | ~ v1_funct_1(F_208)
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(A_209,B_207)))
      | ~ v1_funct_1(E_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_58,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_1089,plain,(
    ! [D_171,C_172,A_173,B_174] :
      ( D_171 = C_172
      | ~ r2_relset_1(A_173,B_174,C_172,D_171)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1099,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_58,c_1089])).

tff(c_1118,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1099])).

tff(c_1157,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1118])).

tff(c_2046,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2038,c_1157])).

tff(c_2079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_66,c_60,c_2046])).

tff(c_2080,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1118])).

tff(c_4722,plain,(
    ! [C_278,D_279,B_280,A_281] :
      ( k2_funct_1(C_278) = D_279
      | k1_xboole_0 = B_280
      | k1_xboole_0 = A_281
      | ~ v2_funct_1(C_278)
      | ~ r2_relset_1(A_281,A_281,k1_partfun1(A_281,B_280,B_280,A_281,C_278,D_279),k6_partfun1(A_281))
      | k2_relset_1(A_281,B_280,C_278) != B_280
      | ~ m1_subset_1(D_279,k1_zfmisc_1(k2_zfmisc_1(B_280,A_281)))
      | ~ v1_funct_2(D_279,B_280,A_281)
      | ~ v1_funct_1(D_279)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_281,B_280)))
      | ~ v1_funct_2(C_278,A_281,B_280)
      | ~ v1_funct_1(C_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_4743,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2080,c_4722])).

tff(c_4751,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_64,c_60,c_965,c_941,c_1024,c_4743])).

tff(c_4752,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_706,c_4751])).

tff(c_2404,plain,(
    ! [A_220,B_221] :
      ( k2_funct_2(A_220,B_221) = k2_funct_1(B_221)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(k2_zfmisc_1(A_220,A_220)))
      | ~ v3_funct_2(B_221,A_220,A_220)
      | ~ v1_funct_2(B_221,A_220,A_220)
      | ~ v1_funct_1(B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2417,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2404])).

tff(c_2427,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_2417])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_2432,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2427,c_56])).

tff(c_4754,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4752,c_2432])).

tff(c_4758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_4754])).

tff(c_4759,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_153,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_145,c_10])).

tff(c_222,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_4761,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4759,c_222])).

tff(c_5112,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5110,c_4761])).

tff(c_6,plain,(
    ! [A_3] : v1_xboole_0('#skF_1'(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_97,plain,(
    ! [B_54,A_55] :
      ( ~ v1_xboole_0(B_54)
      | B_54 = A_55
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_104,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_2,c_97])).

tff(c_111,plain,(
    ! [A_3] : '#skF_1'(A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1('#skF_1'(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_115,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_8])).

tff(c_4767,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4759,c_115])).

tff(c_5214,plain,(
    ! [C_329,B_330,A_331] :
      ( v2_funct_2(C_329,B_330)
      | ~ v3_funct_2(C_329,A_331,B_330)
      | ~ v1_funct_1(C_329)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_331,B_330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_5218,plain,(
    ! [B_330,A_331] :
      ( v2_funct_2('#skF_3',B_330)
      | ~ v3_funct_2('#skF_3',A_331,B_330)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4767,c_5214])).

tff(c_5248,plain,(
    ! [B_335,A_336] :
      ( v2_funct_2('#skF_3',B_335)
      | ~ v3_funct_2('#skF_3',A_336,B_335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5218])).

tff(c_5252,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_5248])).

tff(c_4760,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_4782,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4759,c_4760])).

tff(c_178,plain,(
    ! [B_66] : v5_relat_1(k1_xboole_0,B_66) ),
    inference(resolution,[status(thm)],[c_115,c_163])).

tff(c_4764,plain,(
    ! [B_66] : v5_relat_1('#skF_3',B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4759,c_178])).

tff(c_4983,plain,(
    ! [B_66] :
      ( k2_relat_1('#skF_3') = B_66
      | ~ v2_funct_2('#skF_3',B_66)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4764,c_4980])).

tff(c_4992,plain,(
    ! [B_66] :
      ( B_66 = '#skF_3'
      | ~ v2_funct_2('#skF_3',B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_4782,c_4983])).

tff(c_5255,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5252,c_4992])).

tff(c_5259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5112,c_5255])).

tff(c_5260,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_6291,plain,(
    ! [A_439] : m1_subset_1('#skF_4',k1_zfmisc_1(A_439)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5260,c_115])).

tff(c_26,plain,(
    ! [A_20,B_21,D_23] :
      ( r2_relset_1(A_20,B_21,D_23,D_23)
      | ~ m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6311,plain,(
    ! [A_20,B_21] : r2_relset_1(A_20,B_21,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_6291,c_26])).

tff(c_5261,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_5280,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5260,c_5261])).

tff(c_5271,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5260,c_2])).

tff(c_5267,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5260,c_115])).

tff(c_6134,plain,(
    ! [C_428,B_429,A_430] :
      ( v2_funct_2(C_428,B_429)
      | ~ v3_funct_2(C_428,A_430,B_429)
      | ~ v1_funct_1(C_428)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_430,B_429))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6138,plain,(
    ! [B_429,A_430] :
      ( v2_funct_2('#skF_4',B_429)
      | ~ v3_funct_2('#skF_4',A_430,B_429)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5267,c_6134])).

tff(c_6146,plain,(
    ! [B_431,A_432] :
      ( v2_funct_2('#skF_4',B_431)
      | ~ v3_funct_2('#skF_4',A_432,B_431) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6138])).

tff(c_6150,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_6146])).

tff(c_5264,plain,(
    ! [B_66] : v5_relat_1('#skF_4',B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5260,c_178])).

tff(c_5996,plain,(
    ! [B_409,A_410] :
      ( k2_relat_1(B_409) = A_410
      | ~ v2_funct_2(B_409,A_410)
      | ~ v5_relat_1(B_409,A_410)
      | ~ v1_relat_1(B_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5999,plain,(
    ! [B_66] :
      ( k2_relat_1('#skF_4') = B_66
      | ~ v2_funct_2('#skF_4',B_66)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5264,c_5996])).

tff(c_6005,plain,(
    ! [B_66] :
      ( B_66 = '#skF_4'
      | ~ v2_funct_2('#skF_4',B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_5280,c_5999])).

tff(c_6154,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6150,c_6005])).

tff(c_5292,plain,(
    ! [C_338,B_339,A_340] :
      ( v1_xboole_0(C_338)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(B_339,A_340)))
      | ~ v1_xboole_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5305,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_5292])).

tff(c_5311,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5305])).

tff(c_6158,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6154,c_5311])).

tff(c_6165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5271,c_6158])).

tff(c_6167,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_5305])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6188,plain,(
    ! [A_434] :
      ( A_434 = '#skF_2'
      | ~ v1_xboole_0(A_434) ) ),
    inference(resolution,[status(thm)],[c_6167,c_4])).

tff(c_6201,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5271,c_6188])).

tff(c_6166,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5305])).

tff(c_6200,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6166,c_6188])).

tff(c_6221,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6201,c_6200])).

tff(c_6202,plain,
    ( k2_relat_1('#skF_3') != '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5260,c_5260,c_161])).

tff(c_6203,plain,(
    k2_relat_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6202])).

tff(c_6238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5280,c_6221,c_6203])).

tff(c_6239,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6202])).

tff(c_6271,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_6200])).

tff(c_6275,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6271,c_6271,c_64])).

tff(c_6276,plain,(
    v3_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6271,c_6271,c_62])).

tff(c_6335,plain,(
    ! [A_442] :
      ( v1_xboole_0(k6_partfun1(A_442))
      | ~ v1_xboole_0(A_442) ) ),
    inference(resolution,[status(thm)],[c_75,c_5292])).

tff(c_6170,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_6166,c_4])).

tff(c_6284,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_6170])).

tff(c_6346,plain,(
    ! [A_445] :
      ( k6_partfun1(A_445) = '#skF_4'
      | ~ v1_xboole_0(A_445) ) ),
    inference(resolution,[status(thm)],[c_6335,c_6284])).

tff(c_6354,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5271,c_6346])).

tff(c_14,plain,(
    ! [A_6] : k2_funct_1(k6_relat_1(A_6)) = k6_relat_1(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    ! [A_6] : k2_funct_1(k6_partfun1(A_6)) = k6_partfun1(A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_14])).

tff(c_6372,plain,(
    k6_partfun1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6354,c_76])).

tff(c_6381,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6354,c_6372])).

tff(c_9438,plain,(
    ! [A_535,B_536] :
      ( k2_funct_2(A_535,B_536) = k2_funct_1(B_536)
      | ~ m1_subset_1(B_536,k1_zfmisc_1(k2_zfmisc_1(A_535,A_535)))
      | ~ v3_funct_2(B_536,A_535,A_535)
      | ~ v1_funct_2(B_536,A_535,A_535)
      | ~ v1_funct_1(B_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_9442,plain,(
    ! [A_535] :
      ( k2_funct_2(A_535,'#skF_4') = k2_funct_1('#skF_4')
      | ~ v3_funct_2('#skF_4',A_535,A_535)
      | ~ v1_funct_2('#skF_4',A_535,A_535)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5267,c_9438])).

tff(c_11229,plain,(
    ! [A_573] :
      ( k2_funct_2(A_573,'#skF_4') = '#skF_4'
      | ~ v3_funct_2('#skF_4',A_573,A_573)
      | ~ v1_funct_2('#skF_4',A_573,A_573) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6381,c_9442])).

tff(c_11232,plain,
    ( k2_funct_2('#skF_4','#skF_4') = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_6276,c_11229])).

tff(c_11235,plain,(
    k2_funct_2('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6275,c_11232])).

tff(c_6247,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_56])).

tff(c_6411,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6271,c_6271,c_6271,c_6247])).

tff(c_11236,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11235,c_6411])).

tff(c_11239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6311,c_11236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:37:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.02/2.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/2.65  
% 8.02/2.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/2.65  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 8.02/2.65  
% 8.02/2.65  %Foreground sorts:
% 8.02/2.65  
% 8.02/2.65  
% 8.02/2.65  %Background operators:
% 8.02/2.65  
% 8.02/2.65  
% 8.02/2.65  %Foreground operators:
% 8.02/2.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.02/2.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.02/2.65  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.02/2.65  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.02/2.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.02/2.65  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.02/2.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.02/2.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.02/2.65  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 8.02/2.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.02/2.65  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.02/2.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.02/2.65  tff('#skF_2', type, '#skF_2': $i).
% 8.02/2.65  tff('#skF_3', type, '#skF_3': $i).
% 8.02/2.65  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.02/2.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.02/2.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.02/2.65  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.02/2.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.02/2.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.02/2.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.02/2.65  tff('#skF_4', type, '#skF_4': $i).
% 8.02/2.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.02/2.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.02/2.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.02/2.65  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 8.02/2.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.02/2.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.02/2.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.02/2.65  
% 8.33/2.68  tff(f_190, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 8.33/2.68  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.33/2.68  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.33/2.68  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.33/2.68  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 8.33/2.68  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.33/2.68  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 8.33/2.68  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.33/2.68  tff(f_124, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.33/2.68  tff(f_80, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 8.33/2.68  tff(f_112, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.33/2.68  tff(f_168, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 8.33/2.68  tff(f_122, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 8.33/2.68  tff(f_39, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 8.33/2.68  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.33/2.68  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 8.33/2.68  tff(f_66, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 8.33/2.68  tff(f_49, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 8.33/2.68  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.33/2.68  tff(c_129, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.33/2.68  tff(c_145, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_129])).
% 8.33/2.68  tff(c_163, plain, (![C_65, B_66, A_67]: (v5_relat_1(C_65, B_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.33/2.68  tff(c_179, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_163])).
% 8.33/2.68  tff(c_4980, plain, (![B_300, A_301]: (k2_relat_1(B_300)=A_301 | ~v2_funct_2(B_300, A_301) | ~v5_relat_1(B_300, A_301) | ~v1_relat_1(B_300))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.33/2.68  tff(c_4989, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_179, c_4980])).
% 8.33/2.68  tff(c_4998, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_4989])).
% 8.33/2.68  tff(c_5005, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_4998])).
% 8.33/2.68  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.33/2.68  tff(c_62, plain, (v3_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.33/2.68  tff(c_5090, plain, (![C_315, B_316, A_317]: (v2_funct_2(C_315, B_316) | ~v3_funct_2(C_315, A_317, B_316) | ~v1_funct_1(C_315) | ~m1_subset_1(C_315, k1_zfmisc_1(k2_zfmisc_1(A_317, B_316))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.33/2.68  tff(c_5100, plain, (v2_funct_2('#skF_4', '#skF_2') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_5090])).
% 8.33/2.68  tff(c_5107, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_5100])).
% 8.33/2.68  tff(c_5109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5005, c_5107])).
% 8.33/2.68  tff(c_5110, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_4998])).
% 8.33/2.68  tff(c_931, plain, (![A_147, B_148, D_149]: (r2_relset_1(A_147, B_148, D_149, D_149) | ~m1_subset_1(D_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.33/2.68  tff(c_943, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_931])).
% 8.33/2.68  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.33/2.68  tff(c_146, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_129])).
% 8.33/2.68  tff(c_180, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_163])).
% 8.33/2.68  tff(c_272, plain, (![B_83, A_84]: (k2_relat_1(B_83)=A_84 | ~v2_funct_2(B_83, A_84) | ~v5_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.33/2.68  tff(c_281, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_180, c_272])).
% 8.33/2.68  tff(c_293, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_281])).
% 8.33/2.68  tff(c_333, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_293])).
% 8.33/2.68  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.33/2.68  tff(c_70, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.33/2.68  tff(c_680, plain, (![C_124, B_125, A_126]: (v2_funct_2(C_124, B_125) | ~v3_funct_2(C_124, A_126, B_125) | ~v1_funct_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.33/2.68  tff(c_693, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_680])).
% 8.33/2.68  tff(c_701, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_693])).
% 8.33/2.68  tff(c_703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_333, c_701])).
% 8.33/2.68  tff(c_704, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_293])).
% 8.33/2.68  tff(c_10, plain, (![A_5]: (k2_relat_1(A_5)!=k1_xboole_0 | k1_xboole_0=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.33/2.68  tff(c_161, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_146, c_10])).
% 8.33/2.68  tff(c_224, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_161])).
% 8.33/2.68  tff(c_706, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_704, c_224])).
% 8.33/2.68  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.33/2.68  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.33/2.68  tff(c_946, plain, (![A_152, B_153, C_154]: (k2_relset_1(A_152, B_153, C_154)=k2_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.33/2.68  tff(c_959, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_946])).
% 8.33/2.68  tff(c_965, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_704, c_959])).
% 8.33/2.68  tff(c_48, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.33/2.68  tff(c_30, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.33/2.68  tff(c_75, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_30])).
% 8.33/2.68  tff(c_941, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_75, c_931])).
% 8.33/2.68  tff(c_1003, plain, (![C_160, A_161, B_162]: (v2_funct_1(C_160) | ~v3_funct_2(C_160, A_161, B_162) | ~v1_funct_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.33/2.68  tff(c_1016, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1003])).
% 8.33/2.68  tff(c_1024, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_1016])).
% 8.33/2.68  tff(c_2038, plain, (![A_209, C_206, F_208, D_211, E_210, B_207]: (m1_subset_1(k1_partfun1(A_209, B_207, C_206, D_211, E_210, F_208), k1_zfmisc_1(k2_zfmisc_1(A_209, D_211))) | ~m1_subset_1(F_208, k1_zfmisc_1(k2_zfmisc_1(C_206, D_211))) | ~v1_funct_1(F_208) | ~m1_subset_1(E_210, k1_zfmisc_1(k2_zfmisc_1(A_209, B_207))) | ~v1_funct_1(E_210))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.33/2.68  tff(c_58, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.33/2.68  tff(c_1089, plain, (![D_171, C_172, A_173, B_174]: (D_171=C_172 | ~r2_relset_1(A_173, B_174, C_172, D_171) | ~m1_subset_1(D_171, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.33/2.68  tff(c_1099, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_58, c_1089])).
% 8.33/2.68  tff(c_1118, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1099])).
% 8.33/2.68  tff(c_1157, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1118])).
% 8.33/2.68  tff(c_2046, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2038, c_1157])).
% 8.33/2.68  tff(c_2079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_66, c_60, c_2046])).
% 8.33/2.68  tff(c_2080, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1118])).
% 8.33/2.68  tff(c_4722, plain, (![C_278, D_279, B_280, A_281]: (k2_funct_1(C_278)=D_279 | k1_xboole_0=B_280 | k1_xboole_0=A_281 | ~v2_funct_1(C_278) | ~r2_relset_1(A_281, A_281, k1_partfun1(A_281, B_280, B_280, A_281, C_278, D_279), k6_partfun1(A_281)) | k2_relset_1(A_281, B_280, C_278)!=B_280 | ~m1_subset_1(D_279, k1_zfmisc_1(k2_zfmisc_1(B_280, A_281))) | ~v1_funct_2(D_279, B_280, A_281) | ~v1_funct_1(D_279) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_281, B_280))) | ~v1_funct_2(C_278, A_281, B_280) | ~v1_funct_1(C_278))), inference(cnfTransformation, [status(thm)], [f_168])).
% 8.33/2.68  tff(c_4743, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2080, c_4722])).
% 8.33/2.68  tff(c_4751, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_64, c_60, c_965, c_941, c_1024, c_4743])).
% 8.33/2.68  tff(c_4752, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_706, c_4751])).
% 8.33/2.68  tff(c_2404, plain, (![A_220, B_221]: (k2_funct_2(A_220, B_221)=k2_funct_1(B_221) | ~m1_subset_1(B_221, k1_zfmisc_1(k2_zfmisc_1(A_220, A_220))) | ~v3_funct_2(B_221, A_220, A_220) | ~v1_funct_2(B_221, A_220, A_220) | ~v1_funct_1(B_221))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.33/2.68  tff(c_2417, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2404])).
% 8.33/2.68  tff(c_2427, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_2417])).
% 8.33/2.68  tff(c_56, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.33/2.68  tff(c_2432, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2427, c_56])).
% 8.33/2.68  tff(c_4754, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4752, c_2432])).
% 8.33/2.68  tff(c_4758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_943, c_4754])).
% 8.33/2.68  tff(c_4759, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_161])).
% 8.33/2.68  tff(c_153, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_145, c_10])).
% 8.33/2.68  tff(c_222, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_153])).
% 8.33/2.68  tff(c_4761, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4759, c_222])).
% 8.33/2.68  tff(c_5112, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5110, c_4761])).
% 8.33/2.68  tff(c_6, plain, (![A_3]: (v1_xboole_0('#skF_1'(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.33/2.68  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.33/2.68  tff(c_97, plain, (![B_54, A_55]: (~v1_xboole_0(B_54) | B_54=A_55 | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.33/2.68  tff(c_104, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_2, c_97])).
% 8.33/2.68  tff(c_111, plain, (![A_3]: ('#skF_1'(A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_104])).
% 8.33/2.68  tff(c_8, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.33/2.68  tff(c_115, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_8])).
% 8.33/2.68  tff(c_4767, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_4759, c_115])).
% 8.33/2.68  tff(c_5214, plain, (![C_329, B_330, A_331]: (v2_funct_2(C_329, B_330) | ~v3_funct_2(C_329, A_331, B_330) | ~v1_funct_1(C_329) | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_331, B_330))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.33/2.68  tff(c_5218, plain, (![B_330, A_331]: (v2_funct_2('#skF_3', B_330) | ~v3_funct_2('#skF_3', A_331, B_330) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_4767, c_5214])).
% 8.33/2.68  tff(c_5248, plain, (![B_335, A_336]: (v2_funct_2('#skF_3', B_335) | ~v3_funct_2('#skF_3', A_336, B_335))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5218])).
% 8.33/2.68  tff(c_5252, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_5248])).
% 8.33/2.68  tff(c_4760, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_161])).
% 8.33/2.68  tff(c_4782, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4759, c_4760])).
% 8.33/2.68  tff(c_178, plain, (![B_66]: (v5_relat_1(k1_xboole_0, B_66))), inference(resolution, [status(thm)], [c_115, c_163])).
% 8.33/2.68  tff(c_4764, plain, (![B_66]: (v5_relat_1('#skF_3', B_66))), inference(demodulation, [status(thm), theory('equality')], [c_4759, c_178])).
% 8.33/2.68  tff(c_4983, plain, (![B_66]: (k2_relat_1('#skF_3')=B_66 | ~v2_funct_2('#skF_3', B_66) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4764, c_4980])).
% 8.33/2.68  tff(c_4992, plain, (![B_66]: (B_66='#skF_3' | ~v2_funct_2('#skF_3', B_66))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_4782, c_4983])).
% 8.33/2.68  tff(c_5255, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_5252, c_4992])).
% 8.33/2.68  tff(c_5259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5112, c_5255])).
% 8.33/2.68  tff(c_5260, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_153])).
% 8.33/2.68  tff(c_6291, plain, (![A_439]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_439)))), inference(demodulation, [status(thm), theory('equality')], [c_5260, c_115])).
% 8.33/2.68  tff(c_26, plain, (![A_20, B_21, D_23]: (r2_relset_1(A_20, B_21, D_23, D_23) | ~m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.33/2.68  tff(c_6311, plain, (![A_20, B_21]: (r2_relset_1(A_20, B_21, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_6291, c_26])).
% 8.33/2.68  tff(c_5261, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_153])).
% 8.33/2.68  tff(c_5280, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5260, c_5261])).
% 8.33/2.68  tff(c_5271, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5260, c_2])).
% 8.33/2.68  tff(c_5267, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_5260, c_115])).
% 8.33/2.68  tff(c_6134, plain, (![C_428, B_429, A_430]: (v2_funct_2(C_428, B_429) | ~v3_funct_2(C_428, A_430, B_429) | ~v1_funct_1(C_428) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_430, B_429))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.33/2.68  tff(c_6138, plain, (![B_429, A_430]: (v2_funct_2('#skF_4', B_429) | ~v3_funct_2('#skF_4', A_430, B_429) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5267, c_6134])).
% 8.33/2.68  tff(c_6146, plain, (![B_431, A_432]: (v2_funct_2('#skF_4', B_431) | ~v3_funct_2('#skF_4', A_432, B_431))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6138])).
% 8.33/2.68  tff(c_6150, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_6146])).
% 8.33/2.68  tff(c_5264, plain, (![B_66]: (v5_relat_1('#skF_4', B_66))), inference(demodulation, [status(thm), theory('equality')], [c_5260, c_178])).
% 8.33/2.68  tff(c_5996, plain, (![B_409, A_410]: (k2_relat_1(B_409)=A_410 | ~v2_funct_2(B_409, A_410) | ~v5_relat_1(B_409, A_410) | ~v1_relat_1(B_409))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.33/2.68  tff(c_5999, plain, (![B_66]: (k2_relat_1('#skF_4')=B_66 | ~v2_funct_2('#skF_4', B_66) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_5264, c_5996])).
% 8.33/2.68  tff(c_6005, plain, (![B_66]: (B_66='#skF_4' | ~v2_funct_2('#skF_4', B_66))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_5280, c_5999])).
% 8.33/2.68  tff(c_6154, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_6150, c_6005])).
% 8.33/2.68  tff(c_5292, plain, (![C_338, B_339, A_340]: (v1_xboole_0(C_338) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(B_339, A_340))) | ~v1_xboole_0(A_340))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.33/2.68  tff(c_5305, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_5292])).
% 8.33/2.68  tff(c_5311, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_5305])).
% 8.33/2.68  tff(c_6158, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6154, c_5311])).
% 8.33/2.68  tff(c_6165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5271, c_6158])).
% 8.33/2.68  tff(c_6167, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_5305])).
% 8.33/2.68  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.33/2.68  tff(c_6188, plain, (![A_434]: (A_434='#skF_2' | ~v1_xboole_0(A_434))), inference(resolution, [status(thm)], [c_6167, c_4])).
% 8.33/2.68  tff(c_6201, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_5271, c_6188])).
% 8.33/2.68  tff(c_6166, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_5305])).
% 8.33/2.68  tff(c_6200, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_6166, c_6188])).
% 8.33/2.68  tff(c_6221, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6201, c_6200])).
% 8.33/2.68  tff(c_6202, plain, (k2_relat_1('#skF_3')!='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5260, c_5260, c_161])).
% 8.33/2.68  tff(c_6203, plain, (k2_relat_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_6202])).
% 8.33/2.68  tff(c_6238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5280, c_6221, c_6203])).
% 8.33/2.68  tff(c_6239, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_6202])).
% 8.33/2.68  tff(c_6271, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_6200])).
% 8.33/2.68  tff(c_6275, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6271, c_6271, c_64])).
% 8.33/2.68  tff(c_6276, plain, (v3_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6271, c_6271, c_62])).
% 8.33/2.68  tff(c_6335, plain, (![A_442]: (v1_xboole_0(k6_partfun1(A_442)) | ~v1_xboole_0(A_442))), inference(resolution, [status(thm)], [c_75, c_5292])).
% 8.33/2.68  tff(c_6170, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_6166, c_4])).
% 8.33/2.68  tff(c_6284, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_6170])).
% 8.33/2.68  tff(c_6346, plain, (![A_445]: (k6_partfun1(A_445)='#skF_4' | ~v1_xboole_0(A_445))), inference(resolution, [status(thm)], [c_6335, c_6284])).
% 8.33/2.68  tff(c_6354, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_5271, c_6346])).
% 8.33/2.68  tff(c_14, plain, (![A_6]: (k2_funct_1(k6_relat_1(A_6))=k6_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.33/2.68  tff(c_76, plain, (![A_6]: (k2_funct_1(k6_partfun1(A_6))=k6_partfun1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_14])).
% 8.33/2.68  tff(c_6372, plain, (k6_partfun1('#skF_4')=k2_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6354, c_76])).
% 8.33/2.68  tff(c_6381, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6354, c_6372])).
% 8.33/2.68  tff(c_9438, plain, (![A_535, B_536]: (k2_funct_2(A_535, B_536)=k2_funct_1(B_536) | ~m1_subset_1(B_536, k1_zfmisc_1(k2_zfmisc_1(A_535, A_535))) | ~v3_funct_2(B_536, A_535, A_535) | ~v1_funct_2(B_536, A_535, A_535) | ~v1_funct_1(B_536))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.33/2.68  tff(c_9442, plain, (![A_535]: (k2_funct_2(A_535, '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', A_535, A_535) | ~v1_funct_2('#skF_4', A_535, A_535) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5267, c_9438])).
% 8.33/2.68  tff(c_11229, plain, (![A_573]: (k2_funct_2(A_573, '#skF_4')='#skF_4' | ~v3_funct_2('#skF_4', A_573, A_573) | ~v1_funct_2('#skF_4', A_573, A_573))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6381, c_9442])).
% 8.33/2.68  tff(c_11232, plain, (k2_funct_2('#skF_4', '#skF_4')='#skF_4' | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_6276, c_11229])).
% 8.33/2.68  tff(c_11235, plain, (k2_funct_2('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6275, c_11232])).
% 8.33/2.68  tff(c_6247, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_56])).
% 8.33/2.68  tff(c_6411, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6271, c_6271, c_6271, c_6247])).
% 8.33/2.68  tff(c_11236, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11235, c_6411])).
% 8.33/2.68  tff(c_11239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6311, c_11236])).
% 8.33/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.33/2.68  
% 8.33/2.68  Inference rules
% 8.33/2.68  ----------------------
% 8.33/2.68  #Ref     : 0
% 8.33/2.68  #Sup     : 2956
% 8.33/2.68  #Fact    : 0
% 8.33/2.68  #Define  : 0
% 8.33/2.68  #Split   : 31
% 8.33/2.68  #Chain   : 0
% 8.33/2.68  #Close   : 0
% 8.33/2.68  
% 8.33/2.68  Ordering : KBO
% 8.33/2.68  
% 8.33/2.68  Simplification rules
% 8.33/2.68  ----------------------
% 8.33/2.68  #Subsume      : 820
% 8.33/2.68  #Demod        : 2021
% 8.33/2.68  #Tautology    : 1028
% 8.33/2.68  #SimpNegUnit  : 14
% 8.33/2.68  #BackRed      : 90
% 8.33/2.68  
% 8.33/2.68  #Partial instantiations: 0
% 8.33/2.68  #Strategies tried      : 1
% 8.33/2.68  
% 8.33/2.68  Timing (in seconds)
% 8.33/2.68  ----------------------
% 8.33/2.68  Preprocessing        : 0.36
% 8.33/2.68  Parsing              : 0.19
% 8.33/2.68  CNF conversion       : 0.03
% 8.33/2.68  Main loop            : 1.53
% 8.33/2.68  Inferencing          : 0.45
% 8.33/2.68  Reduction            : 0.54
% 8.33/2.68  Demodulation         : 0.39
% 8.33/2.68  BG Simplification    : 0.06
% 8.33/2.68  Subsumption          : 0.37
% 8.33/2.68  Abstraction          : 0.07
% 8.33/2.68  MUC search           : 0.00
% 8.33/2.68  Cooper               : 0.00
% 8.33/2.68  Total                : 1.95
% 8.33/2.68  Index Insertion      : 0.00
% 8.33/2.68  Index Deletion       : 0.00
% 8.33/2.68  Index Matching       : 0.00
% 8.33/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
