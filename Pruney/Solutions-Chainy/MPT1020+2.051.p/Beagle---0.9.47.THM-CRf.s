%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:58 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 838 expanded)
%              Number of leaves         :   50 ( 331 expanded)
%              Depth                    :   12
%              Number of atoms          :  232 (2991 expanded)
%              Number of equality atoms :   62 ( 366 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_funct_2 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(f_185,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_163,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_111,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_155,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_57,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_168,plain,(
    ! [A_67,B_68,D_69] :
      ( r2_relset_1(A_67,B_68,D_69,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_173,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_168])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_72,plain,(
    v3_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_174,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_168])).

tff(c_10,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_136,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_130])).

tff(c_142,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_356,plain,(
    ! [A_102,B_103,C_104] :
      ( k1_relset_1(A_102,B_103,C_104) = k1_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_364,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_356])).

tff(c_409,plain,(
    ! [A_115,B_116] :
      ( k1_relset_1(A_115,A_115,B_116) = A_115
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_zfmisc_1(A_115,A_115)))
      | ~ v1_funct_2(B_116,A_115,A_115)
      | ~ v1_funct_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_415,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_409])).

tff(c_421,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_364,c_415])).

tff(c_48,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_2'(k1_relat_1(B_11),B_11),k1_relat_1(B_11))
      | k6_relat_1(k1_relat_1(B_11)) = B_11
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_403,plain,(
    ! [B_113] :
      ( r2_hidden('#skF_2'(k1_relat_1(B_113),B_113),k1_relat_1(B_113))
      | k6_partfun1(k1_relat_1(B_113)) = B_113
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_407,plain,(
    ! [B_113] :
      ( ~ v1_xboole_0(k1_relat_1(B_113))
      | k6_partfun1(k1_relat_1(B_113)) = B_113
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_403,c_2])).

tff(c_455,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k6_partfun1(k1_relat_1('#skF_5')) = '#skF_5'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_407])).

tff(c_467,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k6_partfun1('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_68,c_421,c_455])).

tff(c_481,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_467])).

tff(c_133,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_70,c_130])).

tff(c_139,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_133])).

tff(c_143,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_150,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_143])).

tff(c_175,plain,(
    ! [B_70,A_71] :
      ( k2_relat_1(B_70) = A_71
      | ~ v2_funct_2(B_70,A_71)
      | ~ v5_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_181,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v2_funct_2('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_150,c_175])).

tff(c_187,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v2_funct_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_181])).

tff(c_188,plain,(
    ~ v2_funct_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_247,plain,(
    ! [C_85,B_86,A_87] :
      ( v2_funct_2(C_85,B_86)
      | ~ v3_funct_2(C_85,A_87,B_86)
      | ~ v1_funct_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_250,plain,
    ( v2_funct_2('#skF_4','#skF_3')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_247])).

tff(c_256,plain,(
    v2_funct_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_250])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_256])).

tff(c_259,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_270,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_273,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_270])).

tff(c_278,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_273])).

tff(c_377,plain,(
    ! [C_107,A_108,B_109] :
      ( v2_funct_1(C_107)
      | ~ v3_funct_2(C_107,A_108,B_109)
      | ~ v1_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_380,plain,
    ( v2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_377])).

tff(c_386,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_380])).

tff(c_60,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_913,plain,(
    ! [C_208,D_209,B_210,A_211] :
      ( k2_funct_1(C_208) = D_209
      | k1_xboole_0 = B_210
      | k1_xboole_0 = A_211
      | ~ v2_funct_1(C_208)
      | ~ r2_relset_1(A_211,A_211,k1_partfun1(A_211,B_210,B_210,A_211,C_208,D_209),k6_partfun1(A_211))
      | k2_relset_1(A_211,B_210,C_208) != B_210
      | ~ m1_subset_1(D_209,k1_zfmisc_1(k2_zfmisc_1(B_210,A_211)))
      | ~ v1_funct_2(D_209,B_210,A_211)
      | ~ v1_funct_1(D_209)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210)))
      | ~ v1_funct_2(C_208,A_211,B_210)
      | ~ v1_funct_1(C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_916,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_3','#skF_3','#skF_4') != '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_913])).

tff(c_922,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_66,c_62,c_278,c_386,c_916])).

tff(c_924,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_922])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_932,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_924,c_6])).

tff(c_934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_932])).

tff(c_935,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_922])).

tff(c_869,plain,(
    ! [A_192,B_193] :
      ( k2_funct_2(A_192,B_193) = k2_funct_1(B_193)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k2_zfmisc_1(A_192,A_192)))
      | ~ v3_funct_2(B_193,A_192,A_192)
      | ~ v1_funct_2(B_193,A_192,A_192)
      | ~ v1_funct_1(B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_872,plain,
    ( k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_869])).

tff(c_878,plain,(
    k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_872])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5',k2_funct_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_882,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_58])).

tff(c_937,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_882])).

tff(c_941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_937])).

tff(c_942,plain,(
    k6_partfun1('#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_943,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_363,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_356])).

tff(c_412,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_409])).

tff(c_418,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_363,c_412])).

tff(c_430,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_407])).

tff(c_442,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_76,c_418,c_430])).

tff(c_983,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_943,c_442])).

tff(c_22,plain,(
    ! [A_15] : k2_funct_1(k6_relat_1(A_15)) = k6_relat_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_77,plain,(
    ! [A_15] : k2_funct_1(k6_partfun1(A_15)) = k6_partfun1(A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_22])).

tff(c_969,plain,(
    k6_partfun1('#skF_3') = k2_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_77])).

tff(c_976,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_969])).

tff(c_984,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_983,c_976])).

tff(c_1049,plain,(
    ! [A_217,B_218] :
      ( k2_funct_2(A_217,B_218) = k2_funct_1(B_218)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(k2_zfmisc_1(A_217,A_217)))
      | ~ v3_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_1(B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1052,plain,
    ( k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_1049])).

tff(c_1055,plain,(
    k2_funct_2('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_984,c_1052])).

tff(c_996,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4',k2_funct_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_58])).

tff(c_1056,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_996])).

tff(c_1059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_1056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n002.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 14:48:51 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.59  
% 3.77/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.59  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_funct_2 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.77/1.59  
% 3.77/1.59  %Foreground sorts:
% 3.77/1.59  
% 3.77/1.59  
% 3.77/1.59  %Background operators:
% 3.77/1.59  
% 3.77/1.59  
% 3.77/1.59  %Foreground operators:
% 3.77/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.77/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.77/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.77/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.77/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.77/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.77/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.59  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.77/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.77/1.59  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.77/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.77/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.77/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.59  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.77/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.77/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.77/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.77/1.59  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.77/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.77/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.77/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.77/1.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.77/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.77/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.77/1.59  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.77/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.77/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.77/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.59  
% 3.77/1.61  tff(f_185, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 3.77/1.61  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.77/1.61  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.77/1.61  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.77/1.61  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.77/1.61  tff(f_163, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 3.77/1.61  tff(f_111, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.77/1.61  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 3.77/1.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.77/1.61  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.77/1.61  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 3.77/1.61  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 3.77/1.61  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.77/1.61  tff(f_155, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 3.77/1.61  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.77/1.61  tff(f_109, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 3.77/1.61  tff(f_57, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 3.77/1.61  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.77/1.61  tff(c_168, plain, (![A_67, B_68, D_69]: (r2_relset_1(A_67, B_68, D_69, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.77/1.61  tff(c_173, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_168])).
% 3.77/1.61  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.77/1.61  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.77/1.61  tff(c_72, plain, (v3_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.77/1.61  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.77/1.61  tff(c_174, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_168])).
% 3.77/1.61  tff(c_10, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.77/1.61  tff(c_130, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.77/1.61  tff(c_136, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_130])).
% 3.77/1.61  tff(c_142, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 3.77/1.61  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.77/1.61  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.77/1.61  tff(c_356, plain, (![A_102, B_103, C_104]: (k1_relset_1(A_102, B_103, C_104)=k1_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.77/1.61  tff(c_364, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_356])).
% 3.77/1.61  tff(c_409, plain, (![A_115, B_116]: (k1_relset_1(A_115, A_115, B_116)=A_115 | ~m1_subset_1(B_116, k1_zfmisc_1(k2_zfmisc_1(A_115, A_115))) | ~v1_funct_2(B_116, A_115, A_115) | ~v1_funct_1(B_116))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.77/1.61  tff(c_415, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_409])).
% 3.77/1.61  tff(c_421, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_364, c_415])).
% 3.77/1.61  tff(c_48, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.77/1.61  tff(c_16, plain, (![B_11]: (r2_hidden('#skF_2'(k1_relat_1(B_11), B_11), k1_relat_1(B_11)) | k6_relat_1(k1_relat_1(B_11))=B_11 | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.77/1.61  tff(c_403, plain, (![B_113]: (r2_hidden('#skF_2'(k1_relat_1(B_113), B_113), k1_relat_1(B_113)) | k6_partfun1(k1_relat_1(B_113))=B_113 | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 3.77/1.61  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.61  tff(c_407, plain, (![B_113]: (~v1_xboole_0(k1_relat_1(B_113)) | k6_partfun1(k1_relat_1(B_113))=B_113 | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_403, c_2])).
% 3.77/1.61  tff(c_455, plain, (~v1_xboole_0('#skF_3') | k6_partfun1(k1_relat_1('#skF_5'))='#skF_5' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_421, c_407])).
% 3.77/1.61  tff(c_467, plain, (~v1_xboole_0('#skF_3') | k6_partfun1('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_68, c_421, c_455])).
% 3.77/1.61  tff(c_481, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_467])).
% 3.77/1.61  tff(c_133, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_70, c_130])).
% 3.77/1.61  tff(c_139, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_133])).
% 3.77/1.61  tff(c_143, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.77/1.61  tff(c_150, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_143])).
% 3.77/1.61  tff(c_175, plain, (![B_70, A_71]: (k2_relat_1(B_70)=A_71 | ~v2_funct_2(B_70, A_71) | ~v5_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.77/1.61  tff(c_181, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v2_funct_2('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_150, c_175])).
% 3.77/1.61  tff(c_187, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v2_funct_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_181])).
% 3.77/1.61  tff(c_188, plain, (~v2_funct_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_187])).
% 3.77/1.61  tff(c_247, plain, (![C_85, B_86, A_87]: (v2_funct_2(C_85, B_86) | ~v3_funct_2(C_85, A_87, B_86) | ~v1_funct_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.77/1.61  tff(c_250, plain, (v2_funct_2('#skF_4', '#skF_3') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_247])).
% 3.77/1.61  tff(c_256, plain, (v2_funct_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_250])).
% 3.77/1.61  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_256])).
% 3.77/1.61  tff(c_259, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_187])).
% 3.77/1.61  tff(c_270, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.77/1.61  tff(c_273, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_270])).
% 3.77/1.61  tff(c_278, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_259, c_273])).
% 3.77/1.61  tff(c_377, plain, (![C_107, A_108, B_109]: (v2_funct_1(C_107) | ~v3_funct_2(C_107, A_108, B_109) | ~v1_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.77/1.61  tff(c_380, plain, (v2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_377])).
% 3.77/1.61  tff(c_386, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_380])).
% 3.77/1.61  tff(c_60, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.77/1.61  tff(c_913, plain, (![C_208, D_209, B_210, A_211]: (k2_funct_1(C_208)=D_209 | k1_xboole_0=B_210 | k1_xboole_0=A_211 | ~v2_funct_1(C_208) | ~r2_relset_1(A_211, A_211, k1_partfun1(A_211, B_210, B_210, A_211, C_208, D_209), k6_partfun1(A_211)) | k2_relset_1(A_211, B_210, C_208)!=B_210 | ~m1_subset_1(D_209, k1_zfmisc_1(k2_zfmisc_1(B_210, A_211))) | ~v1_funct_2(D_209, B_210, A_211) | ~v1_funct_1(D_209) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))) | ~v1_funct_2(C_208, A_211, B_210) | ~v1_funct_1(C_208))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.77/1.61  tff(c_916, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_3', '#skF_3', '#skF_4')!='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_913])).
% 3.77/1.61  tff(c_922, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_66, c_62, c_278, c_386, c_916])).
% 3.77/1.61  tff(c_924, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_922])).
% 3.77/1.61  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.77/1.61  tff(c_932, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_924, c_6])).
% 3.77/1.61  tff(c_934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_481, c_932])).
% 3.77/1.61  tff(c_935, plain, (k2_funct_1('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_922])).
% 3.77/1.61  tff(c_869, plain, (![A_192, B_193]: (k2_funct_2(A_192, B_193)=k2_funct_1(B_193) | ~m1_subset_1(B_193, k1_zfmisc_1(k2_zfmisc_1(A_192, A_192))) | ~v3_funct_2(B_193, A_192, A_192) | ~v1_funct_2(B_193, A_192, A_192) | ~v1_funct_1(B_193))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.77/1.61  tff(c_872, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_869])).
% 3.77/1.61  tff(c_878, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_872])).
% 3.77/1.61  tff(c_58, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', k2_funct_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.77/1.61  tff(c_882, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_878, c_58])).
% 3.77/1.61  tff(c_937, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_935, c_882])).
% 3.77/1.61  tff(c_941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_937])).
% 3.77/1.61  tff(c_942, plain, (k6_partfun1('#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_467])).
% 3.77/1.61  tff(c_943, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_467])).
% 3.77/1.61  tff(c_363, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_356])).
% 3.77/1.61  tff(c_412, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_409])).
% 3.77/1.61  tff(c_418, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_363, c_412])).
% 3.77/1.61  tff(c_430, plain, (~v1_xboole_0('#skF_3') | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_418, c_407])).
% 3.77/1.61  tff(c_442, plain, (~v1_xboole_0('#skF_3') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_76, c_418, c_430])).
% 3.77/1.61  tff(c_983, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_942, c_943, c_442])).
% 3.77/1.61  tff(c_22, plain, (![A_15]: (k2_funct_1(k6_relat_1(A_15))=k6_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.77/1.61  tff(c_77, plain, (![A_15]: (k2_funct_1(k6_partfun1(A_15))=k6_partfun1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_22])).
% 3.77/1.61  tff(c_969, plain, (k6_partfun1('#skF_3')=k2_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_942, c_77])).
% 3.77/1.61  tff(c_976, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_942, c_969])).
% 3.77/1.61  tff(c_984, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_983, c_983, c_976])).
% 3.77/1.61  tff(c_1049, plain, (![A_217, B_218]: (k2_funct_2(A_217, B_218)=k2_funct_1(B_218) | ~m1_subset_1(B_218, k1_zfmisc_1(k2_zfmisc_1(A_217, A_217))) | ~v3_funct_2(B_218, A_217, A_217) | ~v1_funct_2(B_218, A_217, A_217) | ~v1_funct_1(B_218))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.77/1.61  tff(c_1052, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_1049])).
% 3.77/1.61  tff(c_1055, plain, (k2_funct_2('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_984, c_1052])).
% 3.77/1.61  tff(c_996, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', k2_funct_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_983, c_58])).
% 3.77/1.61  tff(c_1056, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_996])).
% 3.77/1.61  tff(c_1059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_1056])).
% 3.77/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.61  
% 3.77/1.61  Inference rules
% 3.77/1.61  ----------------------
% 3.77/1.61  #Ref     : 0
% 3.77/1.61  #Sup     : 202
% 3.77/1.61  #Fact    : 0
% 3.77/1.61  #Define  : 0
% 3.77/1.61  #Split   : 14
% 3.77/1.61  #Chain   : 0
% 3.77/1.61  #Close   : 0
% 3.77/1.61  
% 3.77/1.61  Ordering : KBO
% 3.77/1.61  
% 3.77/1.61  Simplification rules
% 3.77/1.61  ----------------------
% 3.77/1.61  #Subsume      : 8
% 3.77/1.61  #Demod        : 430
% 3.77/1.61  #Tautology    : 151
% 3.77/1.61  #SimpNegUnit  : 16
% 3.77/1.61  #BackRed      : 73
% 3.77/1.61  
% 3.77/1.61  #Partial instantiations: 0
% 3.77/1.61  #Strategies tried      : 1
% 3.77/1.61  
% 3.77/1.61  Timing (in seconds)
% 3.77/1.61  ----------------------
% 3.77/1.62  Preprocessing        : 0.36
% 3.77/1.62  Parsing              : 0.19
% 3.77/1.62  CNF conversion       : 0.03
% 3.77/1.62  Main loop            : 0.48
% 3.77/1.62  Inferencing          : 0.16
% 3.77/1.62  Reduction            : 0.17
% 3.77/1.62  Demodulation         : 0.12
% 3.77/1.62  BG Simplification    : 0.03
% 3.77/1.62  Subsumption          : 0.08
% 4.10/1.62  Abstraction          : 0.02
% 4.10/1.62  MUC search           : 0.00
% 4.10/1.62  Cooper               : 0.00
% 4.10/1.62  Total                : 0.88
% 4.10/1.62  Index Insertion      : 0.00
% 4.10/1.62  Index Deletion       : 0.00
% 4.10/1.62  Index Matching       : 0.00
% 4.10/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
