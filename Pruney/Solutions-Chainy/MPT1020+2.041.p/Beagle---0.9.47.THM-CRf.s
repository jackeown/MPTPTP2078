%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:56 EST 2020

% Result     : Theorem 5.94s
% Output     : CNFRefutation 6.35s
% Verified   : 
% Statistics : Number of formulae       :  187 (1079 expanded)
%              Number of leaves         :   41 ( 372 expanded)
%              Depth                    :   14
%              Number of atoms          :  329 (3076 expanded)
%              Number of equality atoms :  115 ( 716 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_165,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_99,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_143,axiom,(
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

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_43,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_256,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_268,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_256])).

tff(c_435,plain,(
    ! [A_73,B_74,D_75] :
      ( r2_relset_1(A_73,B_74,D_75,D_75)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_443,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_435])).

tff(c_42,plain,(
    ! [A_26] : k6_relat_1(A_26) = k6_partfun1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [A_2] : k1_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_2] : k1_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6])).

tff(c_10,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    ! [A_3] : v1_relat_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_114,plain,(
    ! [A_45] :
      ( k1_relat_1(A_45) != k1_xboole_0
      | k1_xboole_0 = A_45
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_117,plain,(
    ! [A_3] :
      ( k1_relat_1(k6_partfun1(A_3)) != k1_xboole_0
      | k6_partfun1(A_3) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_114])).

tff(c_119,plain,(
    ! [A_3] :
      ( k1_xboole_0 != A_3
      | k6_partfun1(A_3) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_117])).

tff(c_52,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_292,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_52])).

tff(c_315,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_68,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_66,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_269,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_256])).

tff(c_295,plain,(
    ! [C_54,B_55,A_56] :
      ( v5_relat_1(C_54,B_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_307,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_295])).

tff(c_452,plain,(
    ! [B_77,A_78] :
      ( k2_relat_1(B_77) = A_78
      | ~ v2_funct_2(B_77,A_78)
      | ~ v5_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_461,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_307,c_452])).

tff(c_473,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_461])).

tff(c_477,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_473])).

tff(c_64,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_640,plain,(
    ! [C_98,B_99,A_100] :
      ( v2_funct_2(C_98,B_99)
      | ~ v3_funct_2(C_98,A_100,B_99)
      | ~ v1_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_649,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_640])).

tff(c_657,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_649])).

tff(c_659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_477,c_657])).

tff(c_660,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_769,plain,(
    ! [A_112,B_113,C_114] :
      ( k2_relset_1(A_112,B_113,C_114) = k2_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_778,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_769])).

tff(c_784,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_778])).

tff(c_816,plain,(
    ! [C_117,A_118,B_119] :
      ( v2_funct_1(C_117)
      | ~ v3_funct_2(C_117,A_118,B_119)
      | ~ v1_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_825,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_816])).

tff(c_833,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_825])).

tff(c_1025,plain,(
    ! [C_149,D_150,B_151,A_152] :
      ( k2_funct_1(C_149) = D_150
      | k1_xboole_0 = B_151
      | k1_xboole_0 = A_152
      | ~ v2_funct_1(C_149)
      | ~ r2_relset_1(A_152,A_152,k1_partfun1(A_152,B_151,B_151,A_152,C_149,D_150),k6_partfun1(A_152))
      | k2_relset_1(A_152,B_151,C_149) != B_151
      | ~ m1_subset_1(D_150,k1_zfmisc_1(k2_zfmisc_1(B_151,A_152)))
      | ~ v1_funct_2(D_150,B_151,A_152)
      | ~ v1_funct_1(D_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151)))
      | ~ v1_funct_2(C_149,A_152,B_151)
      | ~ v1_funct_1(C_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1028,plain,
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
    inference(resolution,[status(thm)],[c_52,c_1025])).

tff(c_1034,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_60,c_58,c_54,c_784,c_833,c_1028])).

tff(c_1035,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_1034])).

tff(c_957,plain,(
    ! [A_132,B_133] :
      ( k2_funct_2(A_132,B_133) = k2_funct_1(B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k2_zfmisc_1(A_132,A_132)))
      | ~ v3_funct_2(B_133,A_132,A_132)
      | ~ v1_funct_2(B_133,A_132,A_132)
      | ~ v1_funct_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_969,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_957])).

tff(c_979,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_969])).

tff(c_50,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_994,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_50])).

tff(c_1036,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1035,c_994])).

tff(c_1040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_1036])).

tff(c_1042,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_276,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_268,c_2])).

tff(c_286,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_1045,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1042,c_286])).

tff(c_306,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_295])).

tff(c_1230,plain,(
    ! [B_172,A_173] :
      ( k2_relat_1(B_172) = A_173
      | ~ v2_funct_2(B_172,A_173)
      | ~ v5_relat_1(B_172,A_173)
      | ~ v1_relat_1(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1245,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_306,c_1230])).

tff(c_1261,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_1245])).

tff(c_1262,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1045,c_1261])).

tff(c_56,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1363,plain,(
    ! [C_185,B_186,A_187] :
      ( v2_funct_2(C_185,B_186)
      | ~ v3_funct_2(C_185,A_187,B_186)
      | ~ v1_funct_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_187,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1369,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1363])).

tff(c_1377,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1369])).

tff(c_1379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1262,c_1377])).

tff(c_1380,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_1381,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_1397,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1381])).

tff(c_2086,plain,(
    ! [C_247,B_248,A_249] :
      ( v5_relat_1(C_247,B_248)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_249,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2094,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_2086])).

tff(c_2197,plain,(
    ! [B_259,A_260] :
      ( k2_relat_1(B_259) = A_260
      | ~ v2_funct_2(B_259,A_260)
      | ~ v5_relat_1(B_259,A_260)
      | ~ v1_relat_1(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2209,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2094,c_2197])).

tff(c_2221,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_1397,c_2209])).

tff(c_2222,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2221])).

tff(c_2374,plain,(
    ! [C_278,B_279,A_280] :
      ( v2_funct_2(C_278,B_279)
      | ~ v3_funct_2(C_278,A_280,B_279)
      | ~ v1_funct_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_280,B_279))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2380,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2374])).

tff(c_2385,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_2380])).

tff(c_2387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2222,c_2385])).

tff(c_2388,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2221])).

tff(c_2410,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_54])).

tff(c_24,plain,(
    ! [A_14,B_15,D_17] :
      ( r2_relset_1(A_14,B_15,D_17,D_17)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2530,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2410,c_24])).

tff(c_2413,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_60])).

tff(c_2411,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_58])).

tff(c_2412,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_56])).

tff(c_121,plain,(
    ! [A_46] :
      ( k1_xboole_0 != A_46
      | k6_partfun1(A_46) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_117])).

tff(c_14,plain,(
    ! [A_4] : k2_funct_1(k6_relat_1(A_4)) = k6_relat_1(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    ! [A_4] : k2_funct_1(k6_partfun1(A_4)) = k6_partfun1(A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_14])).

tff(c_130,plain,(
    ! [A_46] :
      ( k6_partfun1(A_46) = k2_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_46 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_70])).

tff(c_1384,plain,(
    ! [A_46] :
      ( k6_partfun1(A_46) = k2_funct_1('#skF_3')
      | A_46 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1380,c_130])).

tff(c_2569,plain,(
    ! [A_295] :
      ( k6_partfun1(A_295) = k2_funct_1('#skF_1')
      | A_295 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_2388,c_1384])).

tff(c_8,plain,(
    ! [A_2] : k2_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_73,plain,(
    ! [A_2] : k2_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8])).

tff(c_2631,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2569,c_73])).

tff(c_193,plain,(
    ! [A_50] :
      ( k6_partfun1(A_50) = k2_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_50 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_70])).

tff(c_213,plain,(
    ! [A_50] :
      ( v1_relat_1(k2_funct_1(k1_xboole_0))
      | k1_xboole_0 != A_50 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_72])).

tff(c_224,plain,(
    ! [A_50] : k1_xboole_0 != A_50 ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_237,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_224])).

tff(c_238,plain,(
    v1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_1383,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_238])).

tff(c_2404,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_1383])).

tff(c_1386,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != '#skF_3'
      | A_1 = '#skF_3'
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1380,c_2])).

tff(c_2681,plain,(
    ! [A_305] :
      ( k2_relat_1(A_305) != '#skF_1'
      | A_305 = '#skF_1'
      | ~ v1_relat_1(A_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_2388,c_1386])).

tff(c_2684,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2404,c_2681])).

tff(c_2693,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2631,c_2684])).

tff(c_2770,plain,(
    ! [A_312,B_313] :
      ( k2_funct_2(A_312,B_313) = k2_funct_1(B_313)
      | ~ m1_subset_1(B_313,k1_zfmisc_1(k2_zfmisc_1(A_312,A_312)))
      | ~ v3_funct_2(B_313,A_312,A_312)
      | ~ v1_funct_2(B_313,A_312,A_312)
      | ~ v1_funct_1(B_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2773,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2410,c_2770])).

tff(c_2779,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2413,c_2411,c_2412,c_2693,c_2773])).

tff(c_133,plain,(
    ! [A_46] :
      ( k1_relat_1(k1_xboole_0) = A_46
      | k1_xboole_0 != A_46 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_74])).

tff(c_1489,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1380,c_133])).

tff(c_1421,plain,(
    ! [C_192,B_193,A_194] :
      ( v5_relat_1(C_192,B_193)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1432,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1421])).

tff(c_1496,plain,(
    ! [B_200,A_201] :
      ( k2_relat_1(B_200) = A_201
      | ~ v2_funct_2(B_200,A_201)
      | ~ v5_relat_1(B_200,A_201)
      | ~ v1_relat_1(B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1505,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1432,c_1496])).

tff(c_1514,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_1397,c_1505])).

tff(c_1515,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1514])).

tff(c_1690,plain,(
    ! [C_221,B_222,A_223] :
      ( v2_funct_2(C_221,B_222)
      | ~ v3_funct_2(C_221,A_223,B_222)
      | ~ v1_funct_1(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_223,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1696,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1690])).

tff(c_1704,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1696])).

tff(c_1706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1515,c_1704])).

tff(c_1707,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1514])).

tff(c_284,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_269,c_2])).

tff(c_1419,plain,
    ( k2_relat_1('#skF_2') != '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1380,c_284])).

tff(c_1420,plain,(
    k2_relat_1('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1419])).

tff(c_1712,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1707,c_1420])).

tff(c_1433,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_1421])).

tff(c_1502,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1433,c_1496])).

tff(c_1511,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_1502])).

tff(c_1946,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1712,c_1511])).

tff(c_1953,plain,(
    ! [C_242,B_243,A_244] :
      ( v2_funct_2(C_242,B_243)
      | ~ v3_funct_2(C_242,A_244,B_243)
      | ~ v1_funct_1(C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_244,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1962,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1953])).

tff(c_1970,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1962])).

tff(c_1972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1946,c_1970])).

tff(c_1973,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1419])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_285,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_269,c_4])).

tff(c_1417,plain,
    ( k1_relat_1('#skF_2') != '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1380,c_285])).

tff(c_1418,plain,(
    k1_relat_1('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1417])).

tff(c_1975,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1973,c_1418])).

tff(c_2028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1489,c_1975])).

tff(c_2029,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1417])).

tff(c_2034,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2029,c_50])).

tff(c_2398,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_2388,c_2034])).

tff(c_2782,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2779,c_2398])).

tff(c_2785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2530,c_2782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:06:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.94/2.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.52  
% 5.94/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.53  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.94/2.53  
% 5.94/2.53  %Foreground sorts:
% 5.94/2.53  
% 5.94/2.53  
% 5.94/2.53  %Background operators:
% 5.94/2.53  
% 5.94/2.53  
% 5.94/2.53  %Foreground operators:
% 5.94/2.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.94/2.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.94/2.53  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.94/2.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.94/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.94/2.53  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.94/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.94/2.53  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.94/2.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.94/2.53  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.94/2.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.94/2.53  tff('#skF_2', type, '#skF_2': $i).
% 5.94/2.53  tff('#skF_3', type, '#skF_3': $i).
% 5.94/2.53  tff('#skF_1', type, '#skF_1': $i).
% 5.94/2.53  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.94/2.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.94/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.94/2.53  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.94/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.94/2.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.94/2.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.94/2.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.94/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.94/2.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.94/2.53  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.94/2.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.94/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.94/2.53  
% 6.35/2.57  tff(f_165, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 6.35/2.57  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.35/2.57  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.35/2.57  tff(f_99, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.35/2.57  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.35/2.57  tff(f_41, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.35/2.57  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 6.35/2.57  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.35/2.57  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.35/2.57  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.35/2.57  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.35/2.57  tff(f_143, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.35/2.57  tff(f_97, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.35/2.57  tff(f_43, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 6.35/2.57  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.35/2.57  tff(c_256, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.35/2.57  tff(c_268, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_256])).
% 6.35/2.57  tff(c_435, plain, (![A_73, B_74, D_75]: (r2_relset_1(A_73, B_74, D_75, D_75) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.35/2.57  tff(c_443, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_435])).
% 6.35/2.57  tff(c_42, plain, (![A_26]: (k6_relat_1(A_26)=k6_partfun1(A_26))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.35/2.57  tff(c_6, plain, (![A_2]: (k1_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.35/2.57  tff(c_74, plain, (![A_2]: (k1_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6])).
% 6.35/2.57  tff(c_10, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.35/2.57  tff(c_72, plain, (![A_3]: (v1_relat_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 6.35/2.57  tff(c_114, plain, (![A_45]: (k1_relat_1(A_45)!=k1_xboole_0 | k1_xboole_0=A_45 | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.35/2.57  tff(c_117, plain, (![A_3]: (k1_relat_1(k6_partfun1(A_3))!=k1_xboole_0 | k6_partfun1(A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_114])).
% 6.35/2.57  tff(c_119, plain, (![A_3]: (k1_xboole_0!=A_3 | k6_partfun1(A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_117])).
% 6.35/2.57  tff(c_52, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.35/2.57  tff(c_292, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_119, c_52])).
% 6.35/2.57  tff(c_315, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_292])).
% 6.35/2.57  tff(c_68, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.35/2.57  tff(c_66, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.35/2.57  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.35/2.57  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.35/2.57  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.35/2.57  tff(c_269, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_256])).
% 6.35/2.57  tff(c_295, plain, (![C_54, B_55, A_56]: (v5_relat_1(C_54, B_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.35/2.57  tff(c_307, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_295])).
% 6.35/2.57  tff(c_452, plain, (![B_77, A_78]: (k2_relat_1(B_77)=A_78 | ~v2_funct_2(B_77, A_78) | ~v5_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.35/2.57  tff(c_461, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_307, c_452])).
% 6.35/2.57  tff(c_473, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_461])).
% 6.35/2.57  tff(c_477, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_473])).
% 6.35/2.57  tff(c_64, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.35/2.57  tff(c_640, plain, (![C_98, B_99, A_100]: (v2_funct_2(C_98, B_99) | ~v3_funct_2(C_98, A_100, B_99) | ~v1_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.35/2.57  tff(c_649, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_640])).
% 6.35/2.57  tff(c_657, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_649])).
% 6.35/2.57  tff(c_659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_477, c_657])).
% 6.35/2.57  tff(c_660, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_473])).
% 6.35/2.57  tff(c_769, plain, (![A_112, B_113, C_114]: (k2_relset_1(A_112, B_113, C_114)=k2_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.35/2.57  tff(c_778, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_769])).
% 6.35/2.57  tff(c_784, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_660, c_778])).
% 6.35/2.57  tff(c_816, plain, (![C_117, A_118, B_119]: (v2_funct_1(C_117) | ~v3_funct_2(C_117, A_118, B_119) | ~v1_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.35/2.57  tff(c_825, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_816])).
% 6.35/2.57  tff(c_833, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_825])).
% 6.35/2.57  tff(c_1025, plain, (![C_149, D_150, B_151, A_152]: (k2_funct_1(C_149)=D_150 | k1_xboole_0=B_151 | k1_xboole_0=A_152 | ~v2_funct_1(C_149) | ~r2_relset_1(A_152, A_152, k1_partfun1(A_152, B_151, B_151, A_152, C_149, D_150), k6_partfun1(A_152)) | k2_relset_1(A_152, B_151, C_149)!=B_151 | ~m1_subset_1(D_150, k1_zfmisc_1(k2_zfmisc_1(B_151, A_152))) | ~v1_funct_2(D_150, B_151, A_152) | ~v1_funct_1(D_150) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_152, B_151))) | ~v1_funct_2(C_149, A_152, B_151) | ~v1_funct_1(C_149))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.35/2.57  tff(c_1028, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1025])).
% 6.35/2.57  tff(c_1034, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_60, c_58, c_54, c_784, c_833, c_1028])).
% 6.35/2.57  tff(c_1035, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_315, c_1034])).
% 6.35/2.57  tff(c_957, plain, (![A_132, B_133]: (k2_funct_2(A_132, B_133)=k2_funct_1(B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(k2_zfmisc_1(A_132, A_132))) | ~v3_funct_2(B_133, A_132, A_132) | ~v1_funct_2(B_133, A_132, A_132) | ~v1_funct_1(B_133))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.35/2.57  tff(c_969, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_957])).
% 6.35/2.57  tff(c_979, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_969])).
% 6.35/2.57  tff(c_50, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.35/2.57  tff(c_994, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_979, c_50])).
% 6.35/2.57  tff(c_1036, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1035, c_994])).
% 6.35/2.57  tff(c_1040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_443, c_1036])).
% 6.35/2.57  tff(c_1042, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_292])).
% 6.35/2.57  tff(c_2, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.35/2.57  tff(c_276, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_268, c_2])).
% 6.35/2.57  tff(c_286, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_276])).
% 6.35/2.57  tff(c_1045, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1042, c_286])).
% 6.35/2.57  tff(c_306, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_295])).
% 6.35/2.57  tff(c_1230, plain, (![B_172, A_173]: (k2_relat_1(B_172)=A_173 | ~v2_funct_2(B_172, A_173) | ~v5_relat_1(B_172, A_173) | ~v1_relat_1(B_172))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.35/2.57  tff(c_1245, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_306, c_1230])).
% 6.35/2.57  tff(c_1261, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_1245])).
% 6.35/2.57  tff(c_1262, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1045, c_1261])).
% 6.35/2.57  tff(c_56, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.35/2.57  tff(c_1363, plain, (![C_185, B_186, A_187]: (v2_funct_2(C_185, B_186) | ~v3_funct_2(C_185, A_187, B_186) | ~v1_funct_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_187, B_186))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.35/2.57  tff(c_1369, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1363])).
% 6.35/2.57  tff(c_1377, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1369])).
% 6.35/2.57  tff(c_1379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1262, c_1377])).
% 6.35/2.57  tff(c_1380, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_276])).
% 6.35/2.57  tff(c_1381, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_276])).
% 6.35/2.57  tff(c_1397, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1381])).
% 6.35/2.57  tff(c_2086, plain, (![C_247, B_248, A_249]: (v5_relat_1(C_247, B_248) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_249, B_248))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.35/2.57  tff(c_2094, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_2086])).
% 6.35/2.57  tff(c_2197, plain, (![B_259, A_260]: (k2_relat_1(B_259)=A_260 | ~v2_funct_2(B_259, A_260) | ~v5_relat_1(B_259, A_260) | ~v1_relat_1(B_259))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.35/2.57  tff(c_2209, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2094, c_2197])).
% 6.35/2.57  tff(c_2221, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_1397, c_2209])).
% 6.35/2.57  tff(c_2222, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_2221])).
% 6.35/2.57  tff(c_2374, plain, (![C_278, B_279, A_280]: (v2_funct_2(C_278, B_279) | ~v3_funct_2(C_278, A_280, B_279) | ~v1_funct_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_280, B_279))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.35/2.57  tff(c_2380, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2374])).
% 6.35/2.57  tff(c_2385, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_2380])).
% 6.35/2.57  tff(c_2387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2222, c_2385])).
% 6.35/2.57  tff(c_2388, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_2221])).
% 6.35/2.57  tff(c_2410, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_54])).
% 6.35/2.57  tff(c_24, plain, (![A_14, B_15, D_17]: (r2_relset_1(A_14, B_15, D_17, D_17) | ~m1_subset_1(D_17, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.35/2.57  tff(c_2530, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2410, c_24])).
% 6.35/2.57  tff(c_2413, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_60])).
% 6.35/2.57  tff(c_2411, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_58])).
% 6.35/2.57  tff(c_2412, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_56])).
% 6.35/2.57  tff(c_121, plain, (![A_46]: (k1_xboole_0!=A_46 | k6_partfun1(A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_117])).
% 6.35/2.57  tff(c_14, plain, (![A_4]: (k2_funct_1(k6_relat_1(A_4))=k6_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.35/2.57  tff(c_70, plain, (![A_4]: (k2_funct_1(k6_partfun1(A_4))=k6_partfun1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_14])).
% 6.35/2.57  tff(c_130, plain, (![A_46]: (k6_partfun1(A_46)=k2_funct_1(k1_xboole_0) | k1_xboole_0!=A_46)), inference(superposition, [status(thm), theory('equality')], [c_121, c_70])).
% 6.35/2.57  tff(c_1384, plain, (![A_46]: (k6_partfun1(A_46)=k2_funct_1('#skF_3') | A_46!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1380, c_130])).
% 6.35/2.57  tff(c_2569, plain, (![A_295]: (k6_partfun1(A_295)=k2_funct_1('#skF_1') | A_295!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_2388, c_1384])).
% 6.35/2.57  tff(c_8, plain, (![A_2]: (k2_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.35/2.57  tff(c_73, plain, (![A_2]: (k2_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8])).
% 6.35/2.57  tff(c_2631, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2569, c_73])).
% 6.35/2.57  tff(c_193, plain, (![A_50]: (k6_partfun1(A_50)=k2_funct_1(k1_xboole_0) | k1_xboole_0!=A_50)), inference(superposition, [status(thm), theory('equality')], [c_121, c_70])).
% 6.35/2.57  tff(c_213, plain, (![A_50]: (v1_relat_1(k2_funct_1(k1_xboole_0)) | k1_xboole_0!=A_50)), inference(superposition, [status(thm), theory('equality')], [c_193, c_72])).
% 6.35/2.57  tff(c_224, plain, (![A_50]: (k1_xboole_0!=A_50)), inference(splitLeft, [status(thm)], [c_213])).
% 6.35/2.57  tff(c_237, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_224])).
% 6.35/2.57  tff(c_238, plain, (v1_relat_1(k2_funct_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_213])).
% 6.35/2.57  tff(c_1383, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_238])).
% 6.35/2.57  tff(c_2404, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_1383])).
% 6.35/2.57  tff(c_1386, plain, (![A_1]: (k2_relat_1(A_1)!='#skF_3' | A_1='#skF_3' | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1380, c_2])).
% 6.35/2.57  tff(c_2681, plain, (![A_305]: (k2_relat_1(A_305)!='#skF_1' | A_305='#skF_1' | ~v1_relat_1(A_305))), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_2388, c_1386])).
% 6.35/2.57  tff(c_2684, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_2404, c_2681])).
% 6.35/2.57  tff(c_2693, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2631, c_2684])).
% 6.35/2.57  tff(c_2770, plain, (![A_312, B_313]: (k2_funct_2(A_312, B_313)=k2_funct_1(B_313) | ~m1_subset_1(B_313, k1_zfmisc_1(k2_zfmisc_1(A_312, A_312))) | ~v3_funct_2(B_313, A_312, A_312) | ~v1_funct_2(B_313, A_312, A_312) | ~v1_funct_1(B_313))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.35/2.57  tff(c_2773, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2410, c_2770])).
% 6.35/2.57  tff(c_2779, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2413, c_2411, c_2412, c_2693, c_2773])).
% 6.35/2.57  tff(c_133, plain, (![A_46]: (k1_relat_1(k1_xboole_0)=A_46 | k1_xboole_0!=A_46)), inference(superposition, [status(thm), theory('equality')], [c_121, c_74])).
% 6.35/2.57  tff(c_1489, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1380, c_133])).
% 6.35/2.57  tff(c_1421, plain, (![C_192, B_193, A_194]: (v5_relat_1(C_192, B_193) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.35/2.57  tff(c_1432, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_1421])).
% 6.35/2.57  tff(c_1496, plain, (![B_200, A_201]: (k2_relat_1(B_200)=A_201 | ~v2_funct_2(B_200, A_201) | ~v5_relat_1(B_200, A_201) | ~v1_relat_1(B_200))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.35/2.57  tff(c_1505, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1432, c_1496])).
% 6.35/2.57  tff(c_1514, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_1397, c_1505])).
% 6.35/2.57  tff(c_1515, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1514])).
% 6.35/2.57  tff(c_1690, plain, (![C_221, B_222, A_223]: (v2_funct_2(C_221, B_222) | ~v3_funct_2(C_221, A_223, B_222) | ~v1_funct_1(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_223, B_222))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.35/2.57  tff(c_1696, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1690])).
% 6.35/2.57  tff(c_1704, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1696])).
% 6.35/2.57  tff(c_1706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1515, c_1704])).
% 6.35/2.57  tff(c_1707, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1514])).
% 6.35/2.57  tff(c_284, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_269, c_2])).
% 6.35/2.57  tff(c_1419, plain, (k2_relat_1('#skF_2')!='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1380, c_284])).
% 6.35/2.57  tff(c_1420, plain, (k2_relat_1('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_1419])).
% 6.35/2.57  tff(c_1712, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1707, c_1420])).
% 6.35/2.57  tff(c_1433, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_1421])).
% 6.35/2.57  tff(c_1502, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1433, c_1496])).
% 6.35/2.57  tff(c_1511, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_1502])).
% 6.35/2.57  tff(c_1946, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1712, c_1511])).
% 6.35/2.57  tff(c_1953, plain, (![C_242, B_243, A_244]: (v2_funct_2(C_242, B_243) | ~v3_funct_2(C_242, A_244, B_243) | ~v1_funct_1(C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_244, B_243))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.35/2.57  tff(c_1962, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_1953])).
% 6.35/2.57  tff(c_1970, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1962])).
% 6.35/2.57  tff(c_1972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1946, c_1970])).
% 6.35/2.57  tff(c_1973, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1419])).
% 6.35/2.57  tff(c_4, plain, (![A_1]: (k1_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.35/2.57  tff(c_285, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_269, c_4])).
% 6.35/2.57  tff(c_1417, plain, (k1_relat_1('#skF_2')!='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1380, c_285])).
% 6.35/2.57  tff(c_1418, plain, (k1_relat_1('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_1417])).
% 6.35/2.57  tff(c_1975, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1973, c_1418])).
% 6.35/2.57  tff(c_2028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1489, c_1975])).
% 6.35/2.57  tff(c_2029, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1417])).
% 6.35/2.57  tff(c_2034, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2029, c_50])).
% 6.35/2.57  tff(c_2398, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_2388, c_2034])).
% 6.35/2.57  tff(c_2782, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2779, c_2398])).
% 6.35/2.57  tff(c_2785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2530, c_2782])).
% 6.35/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.35/2.57  
% 6.35/2.57  Inference rules
% 6.35/2.57  ----------------------
% 6.35/2.57  #Ref     : 21
% 6.35/2.57  #Sup     : 536
% 6.35/2.57  #Fact    : 0
% 6.35/2.57  #Define  : 0
% 6.35/2.57  #Split   : 23
% 6.35/2.57  #Chain   : 0
% 6.35/2.57  #Close   : 0
% 6.35/2.57  
% 6.35/2.57  Ordering : KBO
% 6.35/2.57  
% 6.35/2.57  Simplification rules
% 6.35/2.57  ----------------------
% 6.35/2.57  #Subsume      : 78
% 6.35/2.57  #Demod        : 689
% 6.35/2.57  #Tautology    : 343
% 6.35/2.57  #SimpNegUnit  : 23
% 6.35/2.57  #BackRed      : 115
% 6.35/2.57  
% 6.35/2.57  #Partial instantiations: 0
% 6.35/2.57  #Strategies tried      : 1
% 6.35/2.57  
% 6.35/2.57  Timing (in seconds)
% 6.35/2.57  ----------------------
% 6.35/2.57  Preprocessing        : 0.53
% 6.35/2.57  Parsing              : 0.28
% 6.35/2.57  CNF conversion       : 0.04
% 6.35/2.57  Main loop            : 1.10
% 6.35/2.57  Inferencing          : 0.38
% 6.35/2.57  Reduction            : 0.41
% 6.35/2.57  Demodulation         : 0.30
% 6.35/2.58  BG Simplification    : 0.05
% 6.35/2.58  Subsumption          : 0.15
% 6.35/2.58  Abstraction          : 0.05
% 6.35/2.58  MUC search           : 0.00
% 6.35/2.58  Cooper               : 0.00
% 6.35/2.58  Total                : 1.72
% 6.35/2.58  Index Insertion      : 0.00
% 6.35/2.58  Index Deletion       : 0.00
% 6.35/2.58  Index Matching       : 0.00
% 6.35/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
