%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:58 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 691 expanded)
%              Number of leaves         :   37 ( 259 expanded)
%              Depth                    :   14
%              Number of atoms          :  285 (2468 expanded)
%              Number of equality atoms :   68 ( 249 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_175,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_99,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( ( k2_relat_1(A) = k1_xboole_0
              & k2_relat_1(B) = k1_xboole_0 )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_153,axiom,(
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

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_96,plain,(
    ! [A_50,B_51,D_52] :
      ( r2_relset_1(A_50,B_51,D_52,D_52)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_101,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_96])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_50,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_830,plain,(
    ! [A_149,B_150] :
      ( k2_funct_2(A_149,B_150) = k2_funct_1(B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k2_zfmisc_1(A_149,A_149)))
      | ~ v3_funct_2(B_150,A_149,A_149)
      | ~ v1_funct_2(B_150,A_149,A_149)
      | ~ v1_funct_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_833,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_830])).

tff(c_836,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_833])).

tff(c_856,plain,(
    ! [A_155,B_156] :
      ( m1_subset_1(k2_funct_2(A_155,B_156),k1_zfmisc_1(k2_zfmisc_1(A_155,A_155)))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_zfmisc_1(A_155,A_155)))
      | ~ v3_funct_2(B_156,A_155,A_155)
      | ~ v1_funct_2(B_156,A_155,A_155)
      | ~ v1_funct_1(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_889,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_856])).

tff(c_904,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_889])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_934,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_904,c_2])).

tff(c_959,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_934])).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_64,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_64])).

tff(c_76,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_70])).

tff(c_77,plain,(
    ! [C_43,B_44,A_45] :
      ( v5_relat_1(C_43,B_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_45,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_77])).

tff(c_103,plain,(
    ! [B_53,A_54] :
      ( k2_relat_1(B_53) = A_54
      | ~ v2_funct_2(B_53,A_54)
      | ~ v5_relat_1(B_53,A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_106,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_85,c_103])).

tff(c_112,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_106])).

tff(c_126,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_62,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_58,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_219,plain,(
    ! [C_75,B_76,A_77] :
      ( v2_funct_2(C_75,B_76)
      | ~ v3_funct_2(C_75,A_77,B_76)
      | ~ v1_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_225,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_219])).

tff(c_231,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_225])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_231])).

tff(c_234,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_116,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | k2_relat_1(B_55) != k1_xboole_0
      | k2_relat_1(A_56) != k1_xboole_0
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_123,plain,(
    ! [A_56] :
      ( A_56 = '#skF_2'
      | k2_relat_1('#skF_2') != k1_xboole_0
      | k2_relat_1(A_56) != k1_xboole_0
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_76,c_116])).

tff(c_325,plain,(
    ! [A_56] :
      ( A_56 = '#skF_2'
      | k1_xboole_0 != '#skF_1'
      | k2_relat_1(A_56) != k1_xboole_0
      | ~ v1_relat_1(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_123])).

tff(c_326,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_60,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_305,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_311,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_305])).

tff(c_315,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_311])).

tff(c_328,plain,(
    ! [C_93,A_94,B_95] :
      ( v2_funct_1(C_93)
      | ~ v3_funct_2(C_93,A_94,B_95)
      | ~ v1_funct_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_334,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_328])).

tff(c_340,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_334])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_667,plain,(
    ! [C_124,D_125,B_126,A_127] :
      ( k2_funct_1(C_124) = D_125
      | k1_xboole_0 = B_126
      | k1_xboole_0 = A_127
      | ~ v2_funct_1(C_124)
      | ~ r2_relset_1(A_127,A_127,k1_partfun1(A_127,B_126,B_126,A_127,C_124,D_125),k6_partfun1(A_127))
      | k2_relset_1(A_127,B_126,C_124) != B_126
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(B_126,A_127)))
      | ~ v1_funct_2(D_125,B_126,A_127)
      | ~ v1_funct_1(D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126)))
      | ~ v1_funct_2(C_124,A_127,B_126)
      | ~ v1_funct_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_670,plain,
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
    inference(resolution,[status(thm)],[c_46,c_667])).

tff(c_673,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_48,c_315,c_340,c_670])).

tff(c_674,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_673])).

tff(c_385,plain,(
    ! [A_108,B_109] :
      ( k2_funct_2(A_108,B_109) = k2_funct_1(B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ v3_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_391,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_385])).

tff(c_397,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_391])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_415,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_44])).

tff(c_690,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_415])).

tff(c_709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_690])).

tff(c_711,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_67,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_64])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_67])).

tff(c_84,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_77])).

tff(c_109,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_103])).

tff(c_115,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_109])).

tff(c_246,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_282,plain,(
    ! [C_87,B_88,A_89] :
      ( v2_funct_2(C_87,B_88)
      | ~ v3_funct_2(C_87,A_89,B_88)
      | ~ v1_funct_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_285,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_282])).

tff(c_291,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_285])).

tff(c_293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_291])).

tff(c_294,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_124,plain,(
    ! [A_56] :
      ( A_56 = '#skF_3'
      | k2_relat_1('#skF_3') != k1_xboole_0
      | k2_relat_1(A_56) != k1_xboole_0
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_73,c_116])).

tff(c_737,plain,(
    ! [A_56] :
      ( A_56 = '#skF_3'
      | k2_relat_1(A_56) != '#skF_1'
      | ~ v1_relat_1(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_711,c_294,c_124])).

tff(c_966,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_959,c_737])).

tff(c_998,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_966])).

tff(c_823,plain,(
    ! [A_147,B_148] :
      ( v1_funct_1(k2_funct_2(A_147,B_148))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k2_zfmisc_1(A_147,A_147)))
      | ~ v3_funct_2(B_148,A_147,A_147)
      | ~ v1_funct_2(B_148,A_147,A_147)
      | ~ v1_funct_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_826,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_823])).

tff(c_829,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_826])).

tff(c_837,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_829])).

tff(c_850,plain,(
    ! [A_153,B_154] :
      ( v3_funct_2(k2_funct_2(A_153,B_154),A_153,A_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k2_zfmisc_1(A_153,A_153)))
      | ~ v3_funct_2(B_154,A_153,A_153)
      | ~ v1_funct_2(B_154,A_153,A_153)
      | ~ v1_funct_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_852,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_850])).

tff(c_855,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_836,c_852])).

tff(c_18,plain,(
    ! [C_21,B_20,A_19] :
      ( v2_funct_2(C_21,B_20)
      | ~ v3_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_917,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_904,c_18])).

tff(c_949,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_855,c_917])).

tff(c_8,plain,(
    ! [C_11,B_10,A_9] :
      ( v5_relat_1(C_11,B_10)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_956,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_904,c_8])).

tff(c_26,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(B_23) = A_22
      | ~ v2_funct_2(B_23,A_22)
      | ~ v5_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_969,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_956,c_26])).

tff(c_972,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_969])).

tff(c_1004,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_949,c_972])).

tff(c_1005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_998,c_1004])).

tff(c_1006,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_966])).

tff(c_710,plain,(
    ! [A_56] :
      ( A_56 = '#skF_2'
      | k2_relat_1(A_56) != k1_xboole_0
      | ~ v1_relat_1(A_56) ) ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_718,plain,(
    ! [A_128] :
      ( A_128 = '#skF_2'
      | k2_relat_1(A_128) != '#skF_1'
      | ~ v1_relat_1(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_710])).

tff(c_724,plain,
    ( '#skF_2' = '#skF_3'
    | k2_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_73,c_718])).

tff(c_734,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_724])).

tff(c_765,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_44])).

tff(c_838,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_765])).

tff(c_1026,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_838])).

tff(c_1041,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_1026])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:55:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.56  
% 3.69/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.57  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.69/1.57  
% 3.69/1.57  %Foreground sorts:
% 3.69/1.57  
% 3.69/1.57  
% 3.69/1.57  %Background operators:
% 3.69/1.57  
% 3.69/1.57  
% 3.69/1.57  %Foreground operators:
% 3.69/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.69/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.69/1.57  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.69/1.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.69/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.57  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.69/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.57  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.69/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.69/1.57  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.69/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.69/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.69/1.57  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.69/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.69/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.57  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.69/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.69/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.69/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.69/1.57  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.69/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.57  
% 3.69/1.59  tff(f_175, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 3.69/1.59  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.69/1.59  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.69/1.59  tff(f_109, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 3.69/1.59  tff(f_99, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 3.69/1.59  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.69/1.59  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.69/1.59  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 3.69/1.59  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 3.69/1.59  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k2_relat_1(A) = k1_xboole_0) & (k2_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t197_relat_1)).
% 3.69/1.59  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.69/1.59  tff(f_153, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 3.69/1.59  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.69/1.59  tff(c_96, plain, (![A_50, B_51, D_52]: (r2_relset_1(A_50, B_51, D_52, D_52) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.69/1.59  tff(c_101, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_96])).
% 3.69/1.59  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.69/1.59  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.69/1.59  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.69/1.59  tff(c_50, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.69/1.59  tff(c_830, plain, (![A_149, B_150]: (k2_funct_2(A_149, B_150)=k2_funct_1(B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(k2_zfmisc_1(A_149, A_149))) | ~v3_funct_2(B_150, A_149, A_149) | ~v1_funct_2(B_150, A_149, A_149) | ~v1_funct_1(B_150))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.69/1.59  tff(c_833, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_830])).
% 3.69/1.59  tff(c_836, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_833])).
% 3.69/1.59  tff(c_856, plain, (![A_155, B_156]: (m1_subset_1(k2_funct_2(A_155, B_156), k1_zfmisc_1(k2_zfmisc_1(A_155, A_155))) | ~m1_subset_1(B_156, k1_zfmisc_1(k2_zfmisc_1(A_155, A_155))) | ~v3_funct_2(B_156, A_155, A_155) | ~v1_funct_2(B_156, A_155, A_155) | ~v1_funct_1(B_156))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.69/1.59  tff(c_889, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_836, c_856])).
% 3.69/1.59  tff(c_904, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_889])).
% 3.69/1.59  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.59  tff(c_934, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_904, c_2])).
% 3.69/1.59  tff(c_959, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_934])).
% 3.69/1.59  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.69/1.59  tff(c_64, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.59  tff(c_70, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_64])).
% 3.69/1.59  tff(c_76, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_70])).
% 3.69/1.59  tff(c_77, plain, (![C_43, B_44, A_45]: (v5_relat_1(C_43, B_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_45, B_44))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.69/1.59  tff(c_85, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_77])).
% 3.69/1.59  tff(c_103, plain, (![B_53, A_54]: (k2_relat_1(B_53)=A_54 | ~v2_funct_2(B_53, A_54) | ~v5_relat_1(B_53, A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.69/1.59  tff(c_106, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_85, c_103])).
% 3.69/1.59  tff(c_112, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_106])).
% 3.69/1.59  tff(c_126, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_112])).
% 3.69/1.59  tff(c_62, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.69/1.59  tff(c_58, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.69/1.59  tff(c_219, plain, (![C_75, B_76, A_77]: (v2_funct_2(C_75, B_76) | ~v3_funct_2(C_75, A_77, B_76) | ~v1_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.59  tff(c_225, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_219])).
% 3.69/1.59  tff(c_231, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_225])).
% 3.69/1.59  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_231])).
% 3.69/1.59  tff(c_234, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_112])).
% 3.69/1.59  tff(c_116, plain, (![B_55, A_56]: (B_55=A_56 | k2_relat_1(B_55)!=k1_xboole_0 | k2_relat_1(A_56)!=k1_xboole_0 | ~v1_relat_1(B_55) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.69/1.59  tff(c_123, plain, (![A_56]: (A_56='#skF_2' | k2_relat_1('#skF_2')!=k1_xboole_0 | k2_relat_1(A_56)!=k1_xboole_0 | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_76, c_116])).
% 3.69/1.59  tff(c_325, plain, (![A_56]: (A_56='#skF_2' | k1_xboole_0!='#skF_1' | k2_relat_1(A_56)!=k1_xboole_0 | ~v1_relat_1(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_123])).
% 3.69/1.59  tff(c_326, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_325])).
% 3.69/1.59  tff(c_60, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.69/1.59  tff(c_305, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.69/1.59  tff(c_311, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_305])).
% 3.69/1.59  tff(c_315, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_234, c_311])).
% 3.69/1.59  tff(c_328, plain, (![C_93, A_94, B_95]: (v2_funct_1(C_93) | ~v3_funct_2(C_93, A_94, B_95) | ~v1_funct_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.59  tff(c_334, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_328])).
% 3.69/1.59  tff(c_340, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_334])).
% 3.69/1.59  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.69/1.59  tff(c_667, plain, (![C_124, D_125, B_126, A_127]: (k2_funct_1(C_124)=D_125 | k1_xboole_0=B_126 | k1_xboole_0=A_127 | ~v2_funct_1(C_124) | ~r2_relset_1(A_127, A_127, k1_partfun1(A_127, B_126, B_126, A_127, C_124, D_125), k6_partfun1(A_127)) | k2_relset_1(A_127, B_126, C_124)!=B_126 | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(B_126, A_127))) | ~v1_funct_2(D_125, B_126, A_127) | ~v1_funct_1(D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))) | ~v1_funct_2(C_124, A_127, B_126) | ~v1_funct_1(C_124))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.69/1.59  tff(c_670, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_667])).
% 3.69/1.59  tff(c_673, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_48, c_315, c_340, c_670])).
% 3.69/1.59  tff(c_674, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_326, c_673])).
% 3.69/1.59  tff(c_385, plain, (![A_108, B_109]: (k2_funct_2(A_108, B_109)=k2_funct_1(B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~v3_funct_2(B_109, A_108, A_108) | ~v1_funct_2(B_109, A_108, A_108) | ~v1_funct_1(B_109))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.69/1.59  tff(c_391, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_385])).
% 3.69/1.59  tff(c_397, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_391])).
% 3.69/1.59  tff(c_44, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.69/1.59  tff(c_415, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_397, c_44])).
% 3.69/1.59  tff(c_690, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_674, c_415])).
% 3.69/1.59  tff(c_709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_690])).
% 3.69/1.59  tff(c_711, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_325])).
% 3.69/1.59  tff(c_67, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_64])).
% 3.69/1.59  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_67])).
% 3.69/1.59  tff(c_84, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_77])).
% 3.69/1.59  tff(c_109, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_103])).
% 3.69/1.59  tff(c_115, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_109])).
% 3.69/1.59  tff(c_246, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_115])).
% 3.69/1.59  tff(c_282, plain, (![C_87, B_88, A_89]: (v2_funct_2(C_87, B_88) | ~v3_funct_2(C_87, A_89, B_88) | ~v1_funct_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.59  tff(c_285, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_282])).
% 3.69/1.59  tff(c_291, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_285])).
% 3.69/1.59  tff(c_293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_291])).
% 3.69/1.59  tff(c_294, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_115])).
% 3.69/1.59  tff(c_124, plain, (![A_56]: (A_56='#skF_3' | k2_relat_1('#skF_3')!=k1_xboole_0 | k2_relat_1(A_56)!=k1_xboole_0 | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_73, c_116])).
% 3.69/1.59  tff(c_737, plain, (![A_56]: (A_56='#skF_3' | k2_relat_1(A_56)!='#skF_1' | ~v1_relat_1(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_711, c_711, c_294, c_124])).
% 3.69/1.59  tff(c_966, plain, (k2_funct_1('#skF_3')='#skF_3' | k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(resolution, [status(thm)], [c_959, c_737])).
% 3.69/1.59  tff(c_998, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_966])).
% 3.69/1.59  tff(c_823, plain, (![A_147, B_148]: (v1_funct_1(k2_funct_2(A_147, B_148)) | ~m1_subset_1(B_148, k1_zfmisc_1(k2_zfmisc_1(A_147, A_147))) | ~v3_funct_2(B_148, A_147, A_147) | ~v1_funct_2(B_148, A_147, A_147) | ~v1_funct_1(B_148))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.69/1.59  tff(c_826, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_823])).
% 3.69/1.59  tff(c_829, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_826])).
% 3.69/1.59  tff(c_837, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_836, c_829])).
% 3.69/1.59  tff(c_850, plain, (![A_153, B_154]: (v3_funct_2(k2_funct_2(A_153, B_154), A_153, A_153) | ~m1_subset_1(B_154, k1_zfmisc_1(k2_zfmisc_1(A_153, A_153))) | ~v3_funct_2(B_154, A_153, A_153) | ~v1_funct_2(B_154, A_153, A_153) | ~v1_funct_1(B_154))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.69/1.59  tff(c_852, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_850])).
% 3.69/1.59  tff(c_855, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_836, c_852])).
% 3.69/1.59  tff(c_18, plain, (![C_21, B_20, A_19]: (v2_funct_2(C_21, B_20) | ~v3_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.59  tff(c_917, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_904, c_18])).
% 3.69/1.59  tff(c_949, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_837, c_855, c_917])).
% 3.69/1.59  tff(c_8, plain, (![C_11, B_10, A_9]: (v5_relat_1(C_11, B_10) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.69/1.59  tff(c_956, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_904, c_8])).
% 3.69/1.59  tff(c_26, plain, (![B_23, A_22]: (k2_relat_1(B_23)=A_22 | ~v2_funct_2(B_23, A_22) | ~v5_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.69/1.59  tff(c_969, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_956, c_26])).
% 3.69/1.59  tff(c_972, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_959, c_969])).
% 3.69/1.59  tff(c_1004, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_949, c_972])).
% 3.69/1.59  tff(c_1005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_998, c_1004])).
% 3.69/1.59  tff(c_1006, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_966])).
% 3.69/1.59  tff(c_710, plain, (![A_56]: (A_56='#skF_2' | k2_relat_1(A_56)!=k1_xboole_0 | ~v1_relat_1(A_56))), inference(splitRight, [status(thm)], [c_325])).
% 3.69/1.59  tff(c_718, plain, (![A_128]: (A_128='#skF_2' | k2_relat_1(A_128)!='#skF_1' | ~v1_relat_1(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_711, c_710])).
% 3.69/1.59  tff(c_724, plain, ('#skF_2'='#skF_3' | k2_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_73, c_718])).
% 3.69/1.59  tff(c_734, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_294, c_724])).
% 3.69/1.59  tff(c_765, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_734, c_44])).
% 3.69/1.59  tff(c_838, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_836, c_765])).
% 3.69/1.59  tff(c_1026, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_838])).
% 3.69/1.59  tff(c_1041, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_1026])).
% 3.69/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.59  
% 3.69/1.59  Inference rules
% 3.69/1.59  ----------------------
% 3.69/1.59  #Ref     : 0
% 3.69/1.59  #Sup     : 185
% 3.69/1.59  #Fact    : 0
% 3.69/1.59  #Define  : 0
% 3.69/1.59  #Split   : 13
% 3.69/1.59  #Chain   : 0
% 3.69/1.59  #Close   : 0
% 3.69/1.59  
% 3.69/1.59  Ordering : KBO
% 3.69/1.59  
% 3.69/1.59  Simplification rules
% 3.69/1.59  ----------------------
% 3.69/1.59  #Subsume      : 5
% 3.69/1.59  #Demod        : 339
% 3.69/1.59  #Tautology    : 99
% 3.69/1.59  #SimpNegUnit  : 5
% 3.69/1.59  #BackRed      : 59
% 3.69/1.59  
% 3.69/1.59  #Partial instantiations: 0
% 3.69/1.59  #Strategies tried      : 1
% 3.69/1.59  
% 3.69/1.59  Timing (in seconds)
% 3.69/1.59  ----------------------
% 3.69/1.59  Preprocessing        : 0.36
% 3.69/1.59  Parsing              : 0.19
% 3.69/1.59  CNF conversion       : 0.02
% 3.69/1.59  Main loop            : 0.45
% 3.69/1.59  Inferencing          : 0.16
% 3.69/1.59  Reduction            : 0.15
% 3.69/1.59  Demodulation         : 0.11
% 3.69/1.59  BG Simplification    : 0.03
% 3.69/1.59  Subsumption          : 0.07
% 3.69/1.59  Abstraction          : 0.02
% 3.69/1.59  MUC search           : 0.00
% 3.69/1.59  Cooper               : 0.00
% 3.69/1.59  Total                : 0.86
% 3.69/1.59  Index Insertion      : 0.00
% 3.69/1.59  Index Deletion       : 0.00
% 3.69/1.59  Index Matching       : 0.00
% 3.69/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
