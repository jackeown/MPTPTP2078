%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:55 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  200 (2248 expanded)
%              Number of leaves         :   46 ( 747 expanded)
%              Depth                    :   17
%              Number of atoms          :  378 (5631 expanded)
%              Number of equality atoms :  137 (1998 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

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

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_119,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_163,axiom,(
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

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_44,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

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

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_824,plain,(
    ! [A_116,B_117,D_118] :
      ( r2_relset_1(A_116,B_117,D_118,D_118)
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_836,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_824])).

tff(c_46,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10,plain,(
    ! [A_3] : k2_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [A_3] : k2_relat_1(k6_partfun1(A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_1] : v1_relat_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_145,plain,(
    ! [A_47] :
      ( k2_relat_1(A_47) != k1_xboole_0
      | k1_xboole_0 = A_47
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_151,plain,(
    ! [A_1] :
      ( k2_relat_1(k6_partfun1(A_1)) != k1_xboole_0
      | k6_partfun1(A_1) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_77,c_145])).

tff(c_157,plain,(
    ! [A_1] :
      ( k1_xboole_0 != A_1
      | k6_partfun1(A_1) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_151])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_230,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_56])).

tff(c_299,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_72,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_70,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_246,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_263,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_246])).

tff(c_282,plain,(
    ! [C_56,B_57,A_58] :
      ( v5_relat_1(C_56,B_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_297,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_282])).

tff(c_354,plain,(
    ! [B_67,A_68] :
      ( k2_relat_1(B_67) = A_68
      | ~ v2_funct_2(B_67,A_68)
      | ~ v5_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_366,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_297,c_354])).

tff(c_378,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_366])).

tff(c_678,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_68,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_764,plain,(
    ! [C_112,B_113,A_114] :
      ( v2_funct_2(C_112,B_113)
      | ~ v3_funct_2(C_112,A_114,B_113)
      | ~ v1_funct_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_773,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_764])).

tff(c_783,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_773])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_678,c_783])).

tff(c_786,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_837,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_846,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_837])).

tff(c_855,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_846])).

tff(c_889,plain,(
    ! [C_124,A_125,B_126] :
      ( v2_funct_1(C_124)
      | ~ v3_funct_2(C_124,A_125,B_126)
      | ~ v1_funct_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_898,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_889])).

tff(c_906,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_898])).

tff(c_1202,plain,(
    ! [C_160,D_161,B_162,A_163] :
      ( k2_funct_1(C_160) = D_161
      | k1_xboole_0 = B_162
      | k1_xboole_0 = A_163
      | ~ v2_funct_1(C_160)
      | ~ r2_relset_1(A_163,A_163,k1_partfun1(A_163,B_162,B_162,A_163,C_160,D_161),k6_partfun1(A_163))
      | k2_relset_1(A_163,B_162,C_160) != B_162
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(B_162,A_163)))
      | ~ v1_funct_2(D_161,B_162,A_163)
      | ~ v1_funct_1(D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162)))
      | ~ v1_funct_2(C_160,A_163,B_162)
      | ~ v1_funct_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1205,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1202])).

tff(c_1211,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_58,c_855,c_906,c_1205])).

tff(c_1212,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_299,c_1211])).

tff(c_1099,plain,(
    ! [A_144,B_145] :
      ( k2_funct_2(A_144,B_145) = k2_funct_1(B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k2_zfmisc_1(A_144,A_144)))
      | ~ v3_funct_2(B_145,A_144,A_144)
      | ~ v1_funct_2(B_145,A_144,A_144)
      | ~ v1_funct_1(B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1108,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1099])).

tff(c_1116,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1108])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_1120,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_54])).

tff(c_1213,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1212,c_1120])).

tff(c_1217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_1213])).

tff(c_1219,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_102,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_14])).

tff(c_8,plain,(
    ! [A_3] : k1_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    ! [A_3] : k1_relat_1(k6_partfun1(A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_123,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_76])).

tff(c_1228,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1219,c_123])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(A_2) != k1_xboole_0
      | k1_xboole_0 = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_272,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_263,c_4])).

tff(c_1271,plain,
    ( k2_relat_1('#skF_2') != '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1219,c_272])).

tff(c_1272,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1271])).

tff(c_1331,plain,(
    ! [B_170,A_171] :
      ( k2_relat_1(B_170) = A_171
      | ~ v2_funct_2(B_170,A_171)
      | ~ v5_relat_1(B_170,A_171)
      | ~ v1_relat_1(B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1343,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_297,c_1331])).

tff(c_1355,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_1343])).

tff(c_1356,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1272,c_1355])).

tff(c_1620,plain,(
    ! [C_193,B_194,A_195] :
      ( v2_funct_2(C_193,B_194)
      | ~ v3_funct_2(C_193,A_195,B_194)
      | ~ v1_funct_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_195,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1629,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1620])).

tff(c_1638,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1629])).

tff(c_1640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1356,c_1638])).

tff(c_1641,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1271])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(A_2) != k1_xboole_0
      | k1_xboole_0 = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_271,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_263,c_6])).

tff(c_281,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_1220,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_281])).

tff(c_1670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_1641,c_1220])).

tff(c_1671,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_1693,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2')
    | '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_1671,c_230])).

tff(c_1694,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1693])).

tff(c_120,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_75])).

tff(c_1679,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_1671,c_120])).

tff(c_1744,plain,(
    ! [C_197,B_198,A_199] :
      ( v5_relat_1(C_197,B_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1755,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_1744])).

tff(c_1856,plain,(
    ! [B_208,A_209] :
      ( k2_relat_1(B_208) = A_209
      | ~ v2_funct_2(B_208,A_209)
      | ~ v5_relat_1(B_208,A_209)
      | ~ v1_relat_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1868,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1755,c_1856])).

tff(c_1880,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_1679,c_1868])).

tff(c_1881,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1694,c_1880])).

tff(c_2097,plain,(
    ! [C_229,B_230,A_231] :
      ( v2_funct_2(C_229,B_230)
      | ~ v3_funct_2(C_229,A_231,B_230)
      | ~ v1_funct_1(C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_231,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2106,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_2097])).

tff(c_2117,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2106])).

tff(c_2119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1881,c_2117])).

tff(c_2121,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1693])).

tff(c_2123,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_1671])).

tff(c_160,plain,(
    ! [A_48] :
      ( k1_xboole_0 != A_48
      | k6_partfun1(A_48) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_151])).

tff(c_42,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_166,plain,(
    ! [A_48] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_48,A_48)))
      | k1_xboole_0 != A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_42])).

tff(c_2698,plain,(
    ! [A_286] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_286,A_286)))
      | A_286 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2123,c_2123,c_166])).

tff(c_26,plain,(
    ! [A_17,B_18,D_20] :
      ( r2_relset_1(A_17,B_18,D_20,D_20)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2715,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2698,c_26])).

tff(c_2130,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_72])).

tff(c_1672,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_1688,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_1672])).

tff(c_2122,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_2121,c_1688])).

tff(c_2124,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_263])).

tff(c_1682,plain,(
    k6_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_1671,c_14])).

tff(c_2139,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_46,c_2121,c_1682])).

tff(c_2180,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_2121,c_1679])).

tff(c_12,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k6_relat_1(k2_relat_1(A_4))) = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k6_partfun1(k2_relat_1(A_4))) = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_2184,plain,
    ( k5_relat_1('#skF_1',k6_partfun1('#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2180,c_74])).

tff(c_2188,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2124,c_2139,c_2184])).

tff(c_2695,plain,(
    ! [A_48] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_48,A_48)))
      | A_48 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2123,c_2123,c_166])).

tff(c_2806,plain,(
    ! [C_298,A_299,B_300] :
      ( v2_funct_1(C_298)
      | ~ v3_funct_2(C_298,A_299,B_300)
      | ~ v1_funct_1(C_298)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2809,plain,(
    ! [A_48] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_48,A_48)
      | ~ v1_funct_1('#skF_1')
      | A_48 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_2695,c_2806])).

tff(c_2815,plain,(
    ! [A_48] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_48,A_48)
      | A_48 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2130,c_2809])).

tff(c_2818,plain,(
    ~ v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2815])).

tff(c_2129,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_68])).

tff(c_2820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2818,c_2129])).

tff(c_2821,plain,(
    v2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2815])).

tff(c_1676,plain,(
    ! [A_1] :
      ( A_1 != '#skF_2'
      | k6_partfun1(A_1) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_1671,c_157])).

tff(c_2234,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_2121,c_1676])).

tff(c_16,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_relat_1(k1_relat_1(A_5)) != k5_relat_1(A_5,B_7)
      | k2_relat_1(A_5) != k1_relat_1(B_7)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2935,plain,(
    ! [A_322,B_323] :
      ( k2_funct_1(A_322) = B_323
      | k6_partfun1(k1_relat_1(A_322)) != k5_relat_1(A_322,B_323)
      | k2_relat_1(A_322) != k1_relat_1(B_323)
      | ~ v2_funct_1(A_322)
      | ~ v1_funct_1(B_323)
      | ~ v1_relat_1(B_323)
      | ~ v1_funct_1(A_322)
      | ~ v1_relat_1(A_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_2942,plain,(
    ! [B_323] :
      ( k2_funct_1('#skF_1') = B_323
      | k5_relat_1('#skF_1',B_323) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_1') != k1_relat_1(B_323)
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1(B_323)
      | ~ v1_relat_1(B_323)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2122,c_2935])).

tff(c_2985,plain,(
    ! [B_327] :
      ( k2_funct_1('#skF_1') = B_327
      | k5_relat_1('#skF_1',B_327) != '#skF_1'
      | k1_relat_1(B_327) != '#skF_1'
      | ~ v1_funct_1(B_327)
      | ~ v1_relat_1(B_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2124,c_2130,c_2821,c_2180,c_2234,c_2942])).

tff(c_2988,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | k5_relat_1('#skF_1','#skF_1') != '#skF_1'
    | k1_relat_1('#skF_1') != '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2124,c_2985])).

tff(c_2994,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2130,c_2122,c_2188,c_2988])).

tff(c_2128,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_70])).

tff(c_2872,plain,(
    ! [A_310,B_311] :
      ( k2_funct_2(A_310,B_311) = k2_funct_1(B_311)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(k2_zfmisc_1(A_310,A_310)))
      | ~ v3_funct_2(B_311,A_310,A_310)
      | ~ v1_funct_2(B_311,A_310,A_310)
      | ~ v1_funct_1(B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2875,plain,(
    ! [A_48] :
      ( k2_funct_2(A_48,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_48,A_48)
      | ~ v1_funct_2('#skF_1',A_48,A_48)
      | ~ v1_funct_1('#skF_1')
      | A_48 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_2695,c_2872])).

tff(c_2884,plain,(
    ! [A_312] :
      ( k2_funct_2(A_312,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_312,A_312)
      | ~ v1_funct_2('#skF_1',A_312,A_312)
      | A_312 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2130,c_2875])).

tff(c_2887,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2129,c_2884])).

tff(c_2890,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2887])).

tff(c_264,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_246])).

tff(c_280,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_264,c_4])).

tff(c_2295,plain,
    ( k2_relat_1('#skF_3') != '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2123,c_2123,c_280])).

tff(c_2296,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2295])).

tff(c_2167,plain,(
    ! [C_232,B_233,A_234] :
      ( v5_relat_1(C_232,B_233)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_234,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2175,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2167])).

tff(c_2332,plain,(
    ! [B_250,A_251] :
      ( k2_relat_1(B_250) = A_251
      | ~ v2_funct_2(B_250,A_251)
      | ~ v5_relat_1(B_250,A_251)
      | ~ v1_relat_1(B_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2341,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2175,c_2332])).

tff(c_2350,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_2341])).

tff(c_2351,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2296,c_2350])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_2547,plain,(
    ! [C_270,B_271,A_272] :
      ( v2_funct_2(C_270,B_271)
      | ~ v3_funct_2(C_270,A_272,B_271)
      | ~ v1_funct_1(C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_272,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2556,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2547])).

tff(c_2564,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2556])).

tff(c_2566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2351,c_2564])).

tff(c_2567,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2295])).

tff(c_2126,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_54])).

tff(c_2607,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2567,c_2126])).

tff(c_2891,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2890,c_2607])).

tff(c_2998,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_2891])).

tff(c_3003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2715,c_2998])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.90  
% 4.84/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.90  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.84/1.90  
% 4.84/1.90  %Foreground sorts:
% 4.84/1.90  
% 4.84/1.90  
% 4.84/1.90  %Background operators:
% 4.84/1.90  
% 4.84/1.90  
% 4.84/1.90  %Foreground operators:
% 4.84/1.90  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.84/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.84/1.90  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.84/1.90  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.84/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/1.90  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.84/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.84/1.90  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.84/1.90  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.84/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.84/1.90  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.84/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.84/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.84/1.90  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.84/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.84/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.84/1.90  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.84/1.90  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.84/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.84/1.90  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.84/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.84/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.84/1.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.84/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/1.90  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.84/1.90  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.84/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.84/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.84/1.90  
% 4.84/1.92  tff(f_185, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 4.84/1.92  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.84/1.92  tff(f_119, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.84/1.92  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.84/1.92  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 4.84/1.92  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.84/1.92  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.84/1.92  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.84/1.92  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.84/1.92  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.84/1.92  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.84/1.92  tff(f_163, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.84/1.92  tff(f_117, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.84/1.92  tff(f_44, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 4.84/1.92  tff(f_107, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.84/1.92  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 4.84/1.92  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 4.84/1.92  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.84/1.92  tff(c_824, plain, (![A_116, B_117, D_118]: (r2_relset_1(A_116, B_117, D_118, D_118) | ~m1_subset_1(D_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.84/1.92  tff(c_836, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_824])).
% 4.84/1.92  tff(c_46, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.84/1.92  tff(c_10, plain, (![A_3]: (k2_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.84/1.92  tff(c_75, plain, (![A_3]: (k2_relat_1(k6_partfun1(A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 4.84/1.92  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.84/1.92  tff(c_77, plain, (![A_1]: (v1_relat_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2])).
% 4.84/1.92  tff(c_145, plain, (![A_47]: (k2_relat_1(A_47)!=k1_xboole_0 | k1_xboole_0=A_47 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.84/1.92  tff(c_151, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))!=k1_xboole_0 | k6_partfun1(A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_77, c_145])).
% 4.84/1.92  tff(c_157, plain, (![A_1]: (k1_xboole_0!=A_1 | k6_partfun1(A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_151])).
% 4.84/1.92  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.84/1.92  tff(c_230, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_157, c_56])).
% 4.84/1.92  tff(c_299, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_230])).
% 4.84/1.92  tff(c_72, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.84/1.92  tff(c_70, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.84/1.92  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.84/1.92  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.84/1.92  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.84/1.92  tff(c_246, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.84/1.92  tff(c_263, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_246])).
% 4.84/1.92  tff(c_282, plain, (![C_56, B_57, A_58]: (v5_relat_1(C_56, B_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.84/1.92  tff(c_297, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_282])).
% 4.84/1.92  tff(c_354, plain, (![B_67, A_68]: (k2_relat_1(B_67)=A_68 | ~v2_funct_2(B_67, A_68) | ~v5_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.84/1.92  tff(c_366, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_297, c_354])).
% 4.84/1.92  tff(c_378, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_366])).
% 4.84/1.92  tff(c_678, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_378])).
% 4.84/1.92  tff(c_68, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.84/1.92  tff(c_764, plain, (![C_112, B_113, A_114]: (v2_funct_2(C_112, B_113) | ~v3_funct_2(C_112, A_114, B_113) | ~v1_funct_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.84/1.92  tff(c_773, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_764])).
% 4.84/1.92  tff(c_783, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_773])).
% 4.84/1.92  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_678, c_783])).
% 4.84/1.92  tff(c_786, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_378])).
% 4.84/1.92  tff(c_837, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.84/1.92  tff(c_846, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_837])).
% 4.84/1.92  tff(c_855, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_786, c_846])).
% 4.84/1.92  tff(c_889, plain, (![C_124, A_125, B_126]: (v2_funct_1(C_124) | ~v3_funct_2(C_124, A_125, B_126) | ~v1_funct_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.84/1.92  tff(c_898, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_889])).
% 4.84/1.92  tff(c_906, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_898])).
% 4.84/1.92  tff(c_1202, plain, (![C_160, D_161, B_162, A_163]: (k2_funct_1(C_160)=D_161 | k1_xboole_0=B_162 | k1_xboole_0=A_163 | ~v2_funct_1(C_160) | ~r2_relset_1(A_163, A_163, k1_partfun1(A_163, B_162, B_162, A_163, C_160, D_161), k6_partfun1(A_163)) | k2_relset_1(A_163, B_162, C_160)!=B_162 | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(B_162, A_163))) | ~v1_funct_2(D_161, B_162, A_163) | ~v1_funct_1(D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))) | ~v1_funct_2(C_160, A_163, B_162) | ~v1_funct_1(C_160))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.84/1.92  tff(c_1205, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1202])).
% 4.84/1.92  tff(c_1211, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_58, c_855, c_906, c_1205])).
% 4.84/1.92  tff(c_1212, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_299, c_1211])).
% 4.84/1.92  tff(c_1099, plain, (![A_144, B_145]: (k2_funct_2(A_144, B_145)=k2_funct_1(B_145) | ~m1_subset_1(B_145, k1_zfmisc_1(k2_zfmisc_1(A_144, A_144))) | ~v3_funct_2(B_145, A_144, A_144) | ~v1_funct_2(B_145, A_144, A_144) | ~v1_funct_1(B_145))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.84/1.92  tff(c_1108, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1099])).
% 4.84/1.92  tff(c_1116, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1108])).
% 4.84/1.92  tff(c_54, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.84/1.92  tff(c_1120, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_54])).
% 4.84/1.92  tff(c_1213, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1212, c_1120])).
% 4.84/1.92  tff(c_1217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_836, c_1213])).
% 4.84/1.92  tff(c_1219, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_230])).
% 4.84/1.92  tff(c_102, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.84/1.92  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.84/1.92  tff(c_108, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_102, c_14])).
% 4.84/1.92  tff(c_8, plain, (![A_3]: (k1_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.84/1.92  tff(c_76, plain, (![A_3]: (k1_relat_1(k6_partfun1(A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 4.84/1.92  tff(c_123, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_108, c_76])).
% 4.84/1.92  tff(c_1228, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1219, c_123])).
% 4.84/1.92  tff(c_4, plain, (![A_2]: (k2_relat_1(A_2)!=k1_xboole_0 | k1_xboole_0=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.84/1.92  tff(c_272, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_263, c_4])).
% 4.84/1.92  tff(c_1271, plain, (k2_relat_1('#skF_2')!='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1219, c_272])).
% 4.84/1.92  tff(c_1272, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1271])).
% 4.84/1.92  tff(c_1331, plain, (![B_170, A_171]: (k2_relat_1(B_170)=A_171 | ~v2_funct_2(B_170, A_171) | ~v5_relat_1(B_170, A_171) | ~v1_relat_1(B_170))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.84/1.92  tff(c_1343, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_297, c_1331])).
% 4.84/1.92  tff(c_1355, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_1343])).
% 4.84/1.92  tff(c_1356, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1272, c_1355])).
% 4.84/1.92  tff(c_1620, plain, (![C_193, B_194, A_195]: (v2_funct_2(C_193, B_194) | ~v3_funct_2(C_193, A_195, B_194) | ~v1_funct_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_195, B_194))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.84/1.92  tff(c_1629, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1620])).
% 4.84/1.92  tff(c_1638, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1629])).
% 4.84/1.92  tff(c_1640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1356, c_1638])).
% 4.84/1.92  tff(c_1641, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1271])).
% 4.84/1.92  tff(c_6, plain, (![A_2]: (k1_relat_1(A_2)!=k1_xboole_0 | k1_xboole_0=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.84/1.92  tff(c_271, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_263, c_6])).
% 4.84/1.92  tff(c_281, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_271])).
% 4.84/1.92  tff(c_1220, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_281])).
% 4.84/1.92  tff(c_1670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1228, c_1641, c_1220])).
% 4.84/1.92  tff(c_1671, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_271])).
% 4.84/1.92  tff(c_1693, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2') | '#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_1671, c_230])).
% 4.84/1.92  tff(c_1694, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_1693])).
% 4.84/1.92  tff(c_120, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_108, c_75])).
% 4.84/1.93  tff(c_1679, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_1671, c_120])).
% 4.84/1.93  tff(c_1744, plain, (![C_197, B_198, A_199]: (v5_relat_1(C_197, B_198) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.84/1.93  tff(c_1755, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_1744])).
% 4.84/1.93  tff(c_1856, plain, (![B_208, A_209]: (k2_relat_1(B_208)=A_209 | ~v2_funct_2(B_208, A_209) | ~v5_relat_1(B_208, A_209) | ~v1_relat_1(B_208))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.84/1.93  tff(c_1868, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1755, c_1856])).
% 4.84/1.93  tff(c_1880, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_1679, c_1868])).
% 4.84/1.93  tff(c_1881, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1694, c_1880])).
% 4.84/1.93  tff(c_2097, plain, (![C_229, B_230, A_231]: (v2_funct_2(C_229, B_230) | ~v3_funct_2(C_229, A_231, B_230) | ~v1_funct_1(C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_231, B_230))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.84/1.93  tff(c_2106, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_2097])).
% 4.84/1.93  tff(c_2117, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2106])).
% 4.84/1.93  tff(c_2119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1881, c_2117])).
% 4.84/1.93  tff(c_2121, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1693])).
% 4.84/1.93  tff(c_2123, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_1671])).
% 4.84/1.93  tff(c_160, plain, (![A_48]: (k1_xboole_0!=A_48 | k6_partfun1(A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_151])).
% 4.84/1.93  tff(c_42, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.84/1.93  tff(c_166, plain, (![A_48]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_48, A_48))) | k1_xboole_0!=A_48)), inference(superposition, [status(thm), theory('equality')], [c_160, c_42])).
% 4.84/1.93  tff(c_2698, plain, (![A_286]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_286, A_286))) | A_286!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2123, c_2123, c_166])).
% 4.84/1.93  tff(c_26, plain, (![A_17, B_18, D_20]: (r2_relset_1(A_17, B_18, D_20, D_20) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.84/1.93  tff(c_2715, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2698, c_26])).
% 4.84/1.93  tff(c_2130, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_72])).
% 4.84/1.93  tff(c_1672, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_271])).
% 4.84/1.93  tff(c_1688, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_1672])).
% 4.84/1.93  tff(c_2122, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_2121, c_1688])).
% 4.84/1.93  tff(c_2124, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_263])).
% 4.84/1.93  tff(c_1682, plain, (k6_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_1671, c_14])).
% 4.84/1.93  tff(c_2139, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_46, c_2121, c_1682])).
% 4.84/1.93  tff(c_2180, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_2121, c_1679])).
% 4.84/1.93  tff(c_12, plain, (![A_4]: (k5_relat_1(A_4, k6_relat_1(k2_relat_1(A_4)))=A_4 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.84/1.93  tff(c_74, plain, (![A_4]: (k5_relat_1(A_4, k6_partfun1(k2_relat_1(A_4)))=A_4 | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 4.84/1.93  tff(c_2184, plain, (k5_relat_1('#skF_1', k6_partfun1('#skF_1'))='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2180, c_74])).
% 4.84/1.93  tff(c_2188, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2124, c_2139, c_2184])).
% 4.84/1.93  tff(c_2695, plain, (![A_48]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_48, A_48))) | A_48!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2123, c_2123, c_166])).
% 4.84/1.93  tff(c_2806, plain, (![C_298, A_299, B_300]: (v2_funct_1(C_298) | ~v3_funct_2(C_298, A_299, B_300) | ~v1_funct_1(C_298) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.84/1.93  tff(c_2809, plain, (![A_48]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_48, A_48) | ~v1_funct_1('#skF_1') | A_48!='#skF_1')), inference(resolution, [status(thm)], [c_2695, c_2806])).
% 4.84/1.93  tff(c_2815, plain, (![A_48]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_48, A_48) | A_48!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2130, c_2809])).
% 4.84/1.93  tff(c_2818, plain, (~v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_2815])).
% 4.84/1.93  tff(c_2129, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_68])).
% 4.84/1.93  tff(c_2820, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2818, c_2129])).
% 4.84/1.93  tff(c_2821, plain, (v2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_2815])).
% 4.84/1.93  tff(c_1676, plain, (![A_1]: (A_1!='#skF_2' | k6_partfun1(A_1)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_1671, c_157])).
% 4.84/1.93  tff(c_2234, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_2121, c_1676])).
% 4.84/1.93  tff(c_16, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_relat_1(k1_relat_1(A_5))!=k5_relat_1(A_5, B_7) | k2_relat_1(A_5)!=k1_relat_1(B_7) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.84/1.93  tff(c_2935, plain, (![A_322, B_323]: (k2_funct_1(A_322)=B_323 | k6_partfun1(k1_relat_1(A_322))!=k5_relat_1(A_322, B_323) | k2_relat_1(A_322)!=k1_relat_1(B_323) | ~v2_funct_1(A_322) | ~v1_funct_1(B_323) | ~v1_relat_1(B_323) | ~v1_funct_1(A_322) | ~v1_relat_1(A_322))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 4.84/1.93  tff(c_2942, plain, (![B_323]: (k2_funct_1('#skF_1')=B_323 | k5_relat_1('#skF_1', B_323)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_1')!=k1_relat_1(B_323) | ~v2_funct_1('#skF_1') | ~v1_funct_1(B_323) | ~v1_relat_1(B_323) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2122, c_2935])).
% 4.84/1.93  tff(c_2985, plain, (![B_327]: (k2_funct_1('#skF_1')=B_327 | k5_relat_1('#skF_1', B_327)!='#skF_1' | k1_relat_1(B_327)!='#skF_1' | ~v1_funct_1(B_327) | ~v1_relat_1(B_327))), inference(demodulation, [status(thm), theory('equality')], [c_2124, c_2130, c_2821, c_2180, c_2234, c_2942])).
% 4.84/1.93  tff(c_2988, plain, (k2_funct_1('#skF_1')='#skF_1' | k5_relat_1('#skF_1', '#skF_1')!='#skF_1' | k1_relat_1('#skF_1')!='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2124, c_2985])).
% 4.84/1.93  tff(c_2994, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2130, c_2122, c_2188, c_2988])).
% 4.84/1.93  tff(c_2128, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_70])).
% 4.84/1.93  tff(c_2872, plain, (![A_310, B_311]: (k2_funct_2(A_310, B_311)=k2_funct_1(B_311) | ~m1_subset_1(B_311, k1_zfmisc_1(k2_zfmisc_1(A_310, A_310))) | ~v3_funct_2(B_311, A_310, A_310) | ~v1_funct_2(B_311, A_310, A_310) | ~v1_funct_1(B_311))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.84/1.93  tff(c_2875, plain, (![A_48]: (k2_funct_2(A_48, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_48, A_48) | ~v1_funct_2('#skF_1', A_48, A_48) | ~v1_funct_1('#skF_1') | A_48!='#skF_1')), inference(resolution, [status(thm)], [c_2695, c_2872])).
% 4.84/1.93  tff(c_2884, plain, (![A_312]: (k2_funct_2(A_312, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_312, A_312) | ~v1_funct_2('#skF_1', A_312, A_312) | A_312!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2130, c_2875])).
% 4.84/1.93  tff(c_2887, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2129, c_2884])).
% 4.84/1.93  tff(c_2890, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2887])).
% 4.84/1.93  tff(c_264, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_246])).
% 4.84/1.93  tff(c_280, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_264, c_4])).
% 4.84/1.93  tff(c_2295, plain, (k2_relat_1('#skF_3')!='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2123, c_2123, c_280])).
% 4.84/1.93  tff(c_2296, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2295])).
% 4.84/1.93  tff(c_2167, plain, (![C_232, B_233, A_234]: (v5_relat_1(C_232, B_233) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_234, B_233))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.84/1.93  tff(c_2175, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_2167])).
% 4.84/1.93  tff(c_2332, plain, (![B_250, A_251]: (k2_relat_1(B_250)=A_251 | ~v2_funct_2(B_250, A_251) | ~v5_relat_1(B_250, A_251) | ~v1_relat_1(B_250))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.84/1.93  tff(c_2341, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2175, c_2332])).
% 4.84/1.93  tff(c_2350, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_2341])).
% 4.84/1.93  tff(c_2351, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2296, c_2350])).
% 4.84/1.93  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.84/1.93  tff(c_2547, plain, (![C_270, B_271, A_272]: (v2_funct_2(C_270, B_271) | ~v3_funct_2(C_270, A_272, B_271) | ~v1_funct_1(C_270) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_272, B_271))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.84/1.93  tff(c_2556, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2547])).
% 4.84/1.93  tff(c_2564, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2556])).
% 4.84/1.93  tff(c_2566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2351, c_2564])).
% 4.84/1.93  tff(c_2567, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_2295])).
% 4.84/1.93  tff(c_2126, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_54])).
% 4.84/1.93  tff(c_2607, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2567, c_2126])).
% 4.84/1.93  tff(c_2891, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2890, c_2607])).
% 4.84/1.93  tff(c_2998, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2994, c_2891])).
% 4.84/1.93  tff(c_3003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2715, c_2998])).
% 4.84/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.93  
% 4.84/1.93  Inference rules
% 4.84/1.93  ----------------------
% 4.84/1.93  #Ref     : 0
% 4.84/1.93  #Sup     : 634
% 4.84/1.93  #Fact    : 0
% 4.84/1.93  #Define  : 0
% 4.84/1.93  #Split   : 22
% 4.84/1.93  #Chain   : 0
% 4.84/1.93  #Close   : 0
% 4.84/1.93  
% 4.84/1.93  Ordering : KBO
% 4.84/1.93  
% 4.84/1.93  Simplification rules
% 4.84/1.93  ----------------------
% 4.84/1.93  #Subsume      : 82
% 4.84/1.93  #Demod        : 682
% 4.84/1.93  #Tautology    : 365
% 4.84/1.93  #SimpNegUnit  : 14
% 4.84/1.93  #BackRed      : 59
% 4.84/1.93  
% 4.84/1.93  #Partial instantiations: 0
% 4.84/1.93  #Strategies tried      : 1
% 4.84/1.93  
% 4.84/1.93  Timing (in seconds)
% 4.84/1.93  ----------------------
% 4.84/1.93  Preprocessing        : 0.37
% 4.84/1.93  Parsing              : 0.20
% 4.84/1.93  CNF conversion       : 0.03
% 4.84/1.93  Main loop            : 0.76
% 4.84/1.93  Inferencing          : 0.27
% 4.84/1.93  Reduction            : 0.28
% 4.84/1.93  Demodulation         : 0.20
% 4.84/1.93  BG Simplification    : 0.03
% 4.84/1.93  Subsumption          : 0.12
% 4.84/1.93  Abstraction          : 0.03
% 4.84/1.93  MUC search           : 0.00
% 4.84/1.93  Cooper               : 0.00
% 4.84/1.93  Total                : 1.19
% 4.84/1.93  Index Insertion      : 0.00
% 4.84/1.93  Index Deletion       : 0.00
% 4.84/1.93  Index Matching       : 0.00
% 4.84/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
