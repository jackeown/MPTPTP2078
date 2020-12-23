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
% DateTime   : Thu Dec  3 10:12:37 EST 2020

% Result     : Theorem 6.07s
% Output     : CNFRefutation 6.40s
% Verified   : 
% Statistics : Number of formulae       :  252 (3027 expanded)
%              Number of leaves         :   41 ( 960 expanded)
%              Depth                    :   15
%              Number of atoms          :  431 (7857 expanded)
%              Number of equality atoms :  159 (2402 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_48,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_3214,plain,(
    ! [C_305,A_306,B_307] :
      ( v1_relat_1(C_305)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3230,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3214])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_3435,plain,(
    ! [A_324,B_325,C_326] :
      ( k2_relset_1(A_324,B_325,C_326) = k2_relat_1(C_326)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_324,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3447,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3435])).

tff(c_3458,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3447])).

tff(c_30,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [A_9] :
      ( v1_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_139,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_142,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_139])).

tff(c_145,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_142])).

tff(c_234,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_240,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_234])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_240])).

tff(c_250,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_254,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_279,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_291,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_279])).

tff(c_466,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_475,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_466])).

tff(c_485,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_475])).

tff(c_26,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_251,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_20,plain,(
    ! [A_8] :
      ( k2_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_298,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_291,c_20])).

tff(c_362,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_486,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_362])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_501,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_519,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_501])).

tff(c_997,plain,(
    ! [B_116,A_117,C_118] :
      ( k1_xboole_0 = B_116
      | k1_relset_1(A_117,B_116,C_118) = A_117
      | ~ v1_funct_2(C_118,A_117,B_116)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1012,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_997])).

tff(c_1029,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_519,c_1012])).

tff(c_1030,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_486,c_1029])).

tff(c_28,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_692,plain,(
    ! [B_95,A_96] :
      ( m1_subset_1(B_95,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_95),A_96)))
      | ~ r1_tarski(k2_relat_1(B_95),A_96)
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_14,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_928,plain,(
    ! [B_110,A_111] :
      ( v1_xboole_0(B_110)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_110),A_111))
      | ~ r1_tarski(k2_relat_1(B_110),A_111)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_692,c_14])).

tff(c_935,plain,(
    ! [B_110] :
      ( v1_xboole_0(B_110)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(B_110),k1_xboole_0)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_928])).

tff(c_943,plain,(
    ! [B_112] :
      ( v1_xboole_0(B_112)
      | ~ r1_tarski(k2_relat_1(B_112),k1_xboole_0)
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_935])).

tff(c_1183,plain,(
    ! [A_128] :
      ( v1_xboole_0(k2_funct_1(A_128))
      | ~ r1_tarski(k1_relat_1(A_128),k1_xboole_0)
      | ~ v1_funct_1(k2_funct_1(A_128))
      | ~ v1_relat_1(k2_funct_1(A_128))
      | ~ v2_funct_1(A_128)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_943])).

tff(c_1186,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_1183])).

tff(c_1194,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_76,c_251,c_1186])).

tff(c_1197,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1194])).

tff(c_1200,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1197])).

tff(c_1204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_1200])).

tff(c_1206,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1194])).

tff(c_433,plain,(
    ! [A_65] :
      ( m1_subset_1(A_65,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_65),k2_relat_1(A_65))))
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1299,plain,(
    ! [A_132] :
      ( m1_subset_1(k2_funct_1(A_132),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_132)),k1_relat_1(A_132))))
      | ~ v1_funct_1(k2_funct_1(A_132))
      | ~ v1_relat_1(k2_funct_1(A_132))
      | ~ v2_funct_1(A_132)
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_433])).

tff(c_1320,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_1299])).

tff(c_1337,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_76,c_1206,c_251,c_1320])).

tff(c_1360,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1337])).

tff(c_1374,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_76,c_485,c_1360])).

tff(c_1376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_1374])).

tff(c_1377,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1391,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_1377,c_18])).

tff(c_22,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_299,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_291,c_22])).

tff(c_350,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_1380,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_350])).

tff(c_1426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_1380])).

tff(c_1427,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_1443,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1427,c_2])).

tff(c_1435,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1427,c_1427,c_10])).

tff(c_16,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1437,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1427,c_1427,c_16])).

tff(c_1676,plain,(
    ! [A_156,B_157,C_158] :
      ( k2_relset_1(A_156,B_157,C_158) = k2_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1691,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1676])).

tff(c_1695,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_74,c_1691])).

tff(c_300,plain,(
    ! [B_52,A_53] :
      ( v1_xboole_0(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_314,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_300])).

tff(c_342,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_1696,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_342])).

tff(c_1703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1443,c_1435,c_1696])).

tff(c_1704,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1709,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1704,c_4])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_130,plain,(
    ! [A_34] : m1_subset_1(k6_relat_1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_134,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_130])).

tff(c_303,plain,
    ( v1_xboole_0(k6_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_134,c_300])).

tff(c_312,plain,(
    v1_xboole_0(k6_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_303])).

tff(c_327,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_312,c_4])).

tff(c_329,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_134])).

tff(c_1809,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_1709,c_329])).

tff(c_1717,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_1709,c_16])).

tff(c_255,plain,(
    ! [A_47] :
      ( k1_relat_1(A_47) != k1_xboole_0
      | k1_xboole_0 = A_47
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_262,plain,(
    ! [A_9] :
      ( k1_relat_1(k2_funct_1(A_9)) != k1_xboole_0
      | k2_funct_1(A_9) = k1_xboole_0
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_26,c_255])).

tff(c_2728,plain,(
    ! [A_249] :
      ( k1_relat_1(k2_funct_1(A_249)) != '#skF_3'
      | k2_funct_1(A_249) = '#skF_3'
      | ~ v1_funct_1(A_249)
      | ~ v1_relat_1(A_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_1709,c_262])).

tff(c_3176,plain,(
    ! [A_302] :
      ( k2_relat_1(A_302) != '#skF_3'
      | k2_funct_1(A_302) = '#skF_3'
      | ~ v1_funct_1(A_302)
      | ~ v1_relat_1(A_302)
      | ~ v2_funct_1(A_302)
      | ~ v1_funct_1(A_302)
      | ~ v1_relat_1(A_302) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2728])).

tff(c_3179,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_3176])).

tff(c_3182,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_1717,c_3179])).

tff(c_1713,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_1709,c_12])).

tff(c_1705,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_1753,plain,(
    ! [A_163] :
      ( A_163 = '#skF_3'
      | ~ v1_xboole_0(A_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_4])).

tff(c_1760,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1705,c_1753])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1732,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_3'
      | A_3 = '#skF_3'
      | k2_zfmisc_1(A_3,B_4) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_1709,c_1709,c_8])).

tff(c_1843,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1760,c_1732])).

tff(c_1847,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1843])).

tff(c_1861,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_1709])).

tff(c_48,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_22,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_85,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_1874,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_1888,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1861,c_1861,c_1874])).

tff(c_1710,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_1709,c_327])).

tff(c_1854,plain,(
    k6_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_1847,c_1710])).

tff(c_1921,plain,(
    ! [B_169] : k2_zfmisc_1('#skF_1',B_169) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_1847,c_1713])).

tff(c_46,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1929,plain,(
    m1_subset_1(k6_relat_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1921,c_46])).

tff(c_1933,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1854,c_1929])).

tff(c_1935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1888,c_1933])).

tff(c_1937,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_1942,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1861,c_1861,c_1937])).

tff(c_1863,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_291])).

tff(c_1869,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_82])).

tff(c_1857,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_1847,c_1717])).

tff(c_1868,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_76])).

tff(c_2387,plain,(
    ! [A_215] :
      ( k1_relat_1(k2_funct_1(A_215)) != '#skF_1'
      | k2_funct_1(A_215) = '#skF_1'
      | ~ v1_funct_1(A_215)
      | ~ v1_relat_1(A_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1861,c_1861,c_262])).

tff(c_2602,plain,(
    ! [A_239] :
      ( k2_relat_1(A_239) != '#skF_1'
      | k2_funct_1(A_239) = '#skF_1'
      | ~ v1_funct_1(A_239)
      | ~ v1_relat_1(A_239)
      | ~ v2_funct_1(A_239)
      | ~ v1_funct_1(A_239)
      | ~ v1_relat_1(A_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2387])).

tff(c_2605,plain,
    ( k2_relat_1('#skF_1') != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1'
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1868,c_2602])).

tff(c_2608,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_1869,c_1857,c_2605])).

tff(c_1715,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_1709,c_10])).

tff(c_1852,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_1847,c_1715])).

tff(c_1864,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_254])).

tff(c_2081,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1852,c_1864])).

tff(c_2609,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2608,c_2081])).

tff(c_2613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1942,c_2609])).

tff(c_2614,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1843])).

tff(c_2617,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2614,c_254])).

tff(c_2621,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1713,c_2617])).

tff(c_3183,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3182,c_2621])).

tff(c_3187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1809,c_3183])).

tff(c_3188,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_3237,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3230,c_20])).

tff(c_3256,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3237])).

tff(c_3459,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3458,c_3256])).

tff(c_3474,plain,(
    ! [A_327,B_328,C_329] :
      ( k1_relset_1(A_327,B_328,C_329) = k1_relat_1(C_329)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_327,B_328))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3496,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3474])).

tff(c_3831,plain,(
    ! [B_361,A_362,C_363] :
      ( k1_xboole_0 = B_361
      | k1_relset_1(A_362,B_361,C_363) = A_362
      | ~ v1_funct_2(C_363,A_362,B_361)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_362,B_361))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3849,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_3831])).

tff(c_3868,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3496,c_3849])).

tff(c_3869,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_3459,c_3868])).

tff(c_3238,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3230,c_22])).

tff(c_3257,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3238])).

tff(c_3877,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3869,c_3257])).

tff(c_3189,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_3494,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3189,c_3474])).

tff(c_3931,plain,(
    ! [B_364,C_365,A_366] :
      ( k1_xboole_0 = B_364
      | v1_funct_2(C_365,A_366,B_364)
      | k1_relset_1(A_366,B_364,C_365) != A_366
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(A_366,B_364))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3940,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_3189,c_3931])).

tff(c_3956,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3494,c_3940])).

tff(c_3957,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3188,c_3877,c_3956])).

tff(c_3967,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3957])).

tff(c_3970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3230,c_82,c_76,c_3458,c_3967])).

tff(c_3971,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3238])).

tff(c_3973,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3971,c_3256])).

tff(c_3981,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3971,c_3971,c_16])).

tff(c_3999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3973,c_3981])).

tff(c_4000,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3237])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4010,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4000,c_6])).

tff(c_4009,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4000,c_4000,c_16])).

tff(c_4011,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4000,c_4000,c_18])).

tff(c_4777,plain,(
    ! [B_422,A_423] :
      ( v1_funct_2(B_422,k1_relat_1(B_422),A_423)
      | ~ r1_tarski(k2_relat_1(B_422),A_423)
      | ~ v1_funct_1(B_422)
      | ~ v1_relat_1(B_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4786,plain,(
    ! [A_423] :
      ( v1_funct_2('#skF_3','#skF_3',A_423)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_423)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4011,c_4777])).

tff(c_4789,plain,(
    ! [A_423] : v1_funct_2('#skF_3','#skF_3',A_423) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3230,c_82,c_4010,c_4009,c_4786])).

tff(c_4015,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4000,c_2])).

tff(c_4005,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4000,c_4000,c_12])).

tff(c_4408,plain,(
    ! [A_394,B_395,C_396] :
      ( k2_relset_1(A_394,B_395,C_396) = k2_relat_1(C_396)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_394,B_395))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4423,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_4408])).

tff(c_4428,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4009,c_4423])).

tff(c_4061,plain,(
    ! [B_373,A_374] :
      ( v1_xboole_0(B_373)
      | ~ m1_subset_1(B_373,k1_zfmisc_1(A_374))
      | ~ v1_xboole_0(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4071,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_3189,c_4061])).

tff(c_4111,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4071])).

tff(c_4431,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4428,c_4111])).

tff(c_4438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4015,c_4005,c_4431])).

tff(c_4440,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4071])).

tff(c_4006,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4000,c_4])).

tff(c_4484,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4440,c_4006])).

tff(c_4022,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_3'
      | A_3 = '#skF_3'
      | k2_zfmisc_1(A_3,B_4) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4000,c_4000,c_4000,c_8])).

tff(c_4495,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4484,c_4022])).

tff(c_4503,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4495])).

tff(c_4439,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4071])).

tff(c_4444,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4439,c_4006])).

tff(c_4448,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4444,c_3188])).

tff(c_4516,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4503,c_4448])).

tff(c_4793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4789,c_4516])).

tff(c_4794,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4495])).

tff(c_4795,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4495])).

tff(c_4822,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4794,c_4795])).

tff(c_4004,plain,(
    m1_subset_1(k6_relat_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4000,c_4000,c_134])).

tff(c_4103,plain,
    ( v1_xboole_0(k6_relat_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4004,c_14])).

tff(c_4106,plain,(
    v1_xboole_0(k6_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4015,c_4103])).

tff(c_4110,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4106,c_4006])).

tff(c_4468,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4110,c_4004])).

tff(c_4796,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4794,c_4794,c_4468])).

tff(c_4811,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4794,c_4000])).

tff(c_4878,plain,(
    ! [A_22] :
      ( v1_funct_2('#skF_1',A_22,'#skF_1')
      | A_22 = '#skF_1'
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4811,c_4811,c_4811,c_4811,c_4811,c_85])).

tff(c_4879,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4878])).

tff(c_4934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4796,c_4879])).

tff(c_5044,plain,(
    ! [A_436] :
      ( v1_funct_2('#skF_1',A_436,'#skF_1')
      | A_436 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_4878])).

tff(c_4799,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4794,c_4448])).

tff(c_5047,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5044,c_4799])).

tff(c_5051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4822,c_5047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.07/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.23  
% 6.07/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.23  %$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.07/2.23  
% 6.07/2.23  %Foreground sorts:
% 6.07/2.23  
% 6.07/2.23  
% 6.07/2.23  %Background operators:
% 6.07/2.23  
% 6.07/2.23  
% 6.07/2.23  %Foreground operators:
% 6.07/2.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.07/2.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.07/2.23  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.07/2.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.07/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.07/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.07/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.07/2.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.07/2.23  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 6.07/2.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.07/2.23  tff('#skF_2', type, '#skF_2': $i).
% 6.07/2.23  tff('#skF_3', type, '#skF_3': $i).
% 6.07/2.23  tff('#skF_1', type, '#skF_1': $i).
% 6.07/2.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.07/2.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.07/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.07/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.07/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.07/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.07/2.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.07/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.07/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.07/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.07/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.07/2.23  
% 6.40/2.27  tff(f_153, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 6.40/2.27  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.40/2.27  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.40/2.27  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.40/2.27  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.40/2.27  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 6.40/2.27  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.40/2.27  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.40/2.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.40/2.27  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.40/2.27  tff(f_136, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 6.40/2.27  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.40/2.27  tff(f_124, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 6.40/2.27  tff(f_48, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.40/2.27  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.40/2.27  tff(f_96, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.40/2.27  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.40/2.27  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.40/2.27  tff(c_3214, plain, (![C_305, A_306, B_307]: (v1_relat_1(C_305) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.40/2.27  tff(c_3230, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3214])).
% 6.40/2.27  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.40/2.27  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.40/2.27  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.40/2.27  tff(c_3435, plain, (![A_324, B_325, C_326]: (k2_relset_1(A_324, B_325, C_326)=k2_relat_1(C_326) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_324, B_325))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.40/2.27  tff(c_3447, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3435])).
% 6.40/2.27  tff(c_3458, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3447])).
% 6.40/2.27  tff(c_30, plain, (![A_10]: (k1_relat_1(k2_funct_1(A_10))=k2_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.40/2.27  tff(c_24, plain, (![A_9]: (v1_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.40/2.27  tff(c_72, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.40/2.27  tff(c_139, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_72])).
% 6.40/2.27  tff(c_142, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_139])).
% 6.40/2.27  tff(c_145, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_142])).
% 6.40/2.27  tff(c_234, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.40/2.27  tff(c_240, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_234])).
% 6.40/2.27  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_240])).
% 6.40/2.27  tff(c_250, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_72])).
% 6.40/2.27  tff(c_254, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_250])).
% 6.40/2.27  tff(c_279, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.40/2.27  tff(c_291, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_279])).
% 6.40/2.27  tff(c_466, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.40/2.27  tff(c_475, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_466])).
% 6.40/2.27  tff(c_485, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_475])).
% 6.40/2.27  tff(c_26, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.40/2.27  tff(c_251, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_72])).
% 6.40/2.27  tff(c_20, plain, (![A_8]: (k2_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.40/2.27  tff(c_298, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_291, c_20])).
% 6.40/2.27  tff(c_362, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_298])).
% 6.40/2.27  tff(c_486, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_485, c_362])).
% 6.40/2.27  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.40/2.27  tff(c_501, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.40/2.27  tff(c_519, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_501])).
% 6.40/2.27  tff(c_997, plain, (![B_116, A_117, C_118]: (k1_xboole_0=B_116 | k1_relset_1(A_117, B_116, C_118)=A_117 | ~v1_funct_2(C_118, A_117, B_116) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.40/2.27  tff(c_1012, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_997])).
% 6.40/2.27  tff(c_1029, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_519, c_1012])).
% 6.40/2.27  tff(c_1030, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_486, c_1029])).
% 6.40/2.27  tff(c_28, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.40/2.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.40/2.27  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.40/2.27  tff(c_692, plain, (![B_95, A_96]: (m1_subset_1(B_95, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_95), A_96))) | ~r1_tarski(k2_relat_1(B_95), A_96) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.40/2.27  tff(c_14, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.40/2.27  tff(c_928, plain, (![B_110, A_111]: (v1_xboole_0(B_110) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_110), A_111)) | ~r1_tarski(k2_relat_1(B_110), A_111) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_692, c_14])).
% 6.40/2.27  tff(c_935, plain, (![B_110]: (v1_xboole_0(B_110) | ~v1_xboole_0(k1_xboole_0) | ~r1_tarski(k2_relat_1(B_110), k1_xboole_0) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(superposition, [status(thm), theory('equality')], [c_10, c_928])).
% 6.40/2.27  tff(c_943, plain, (![B_112]: (v1_xboole_0(B_112) | ~r1_tarski(k2_relat_1(B_112), k1_xboole_0) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_935])).
% 6.40/2.27  tff(c_1183, plain, (![A_128]: (v1_xboole_0(k2_funct_1(A_128)) | ~r1_tarski(k1_relat_1(A_128), k1_xboole_0) | ~v1_funct_1(k2_funct_1(A_128)) | ~v1_relat_1(k2_funct_1(A_128)) | ~v2_funct_1(A_128) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(superposition, [status(thm), theory('equality')], [c_28, c_943])).
% 6.40/2.27  tff(c_1186, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1030, c_1183])).
% 6.40/2.27  tff(c_1194, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_76, c_251, c_1186])).
% 6.40/2.27  tff(c_1197, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1194])).
% 6.40/2.27  tff(c_1200, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1197])).
% 6.40/2.27  tff(c_1204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_1200])).
% 6.40/2.27  tff(c_1206, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1194])).
% 6.40/2.27  tff(c_433, plain, (![A_65]: (m1_subset_1(A_65, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_65), k2_relat_1(A_65)))) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.40/2.27  tff(c_1299, plain, (![A_132]: (m1_subset_1(k2_funct_1(A_132), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_132)), k1_relat_1(A_132)))) | ~v1_funct_1(k2_funct_1(A_132)) | ~v1_relat_1(k2_funct_1(A_132)) | ~v2_funct_1(A_132) | ~v1_funct_1(A_132) | ~v1_relat_1(A_132))), inference(superposition, [status(thm), theory('equality')], [c_28, c_433])).
% 6.40/2.27  tff(c_1320, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1030, c_1299])).
% 6.40/2.27  tff(c_1337, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_76, c_1206, c_251, c_1320])).
% 6.40/2.27  tff(c_1360, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1337])).
% 6.40/2.27  tff(c_1374, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_76, c_485, c_1360])).
% 6.40/2.27  tff(c_1376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_1374])).
% 6.40/2.27  tff(c_1377, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_298])).
% 6.40/2.27  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.40/2.27  tff(c_1391, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_1377, c_18])).
% 6.40/2.27  tff(c_22, plain, (![A_8]: (k1_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.40/2.27  tff(c_299, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_291, c_22])).
% 6.40/2.27  tff(c_350, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_299])).
% 6.40/2.27  tff(c_1380, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_350])).
% 6.40/2.27  tff(c_1426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1391, c_1380])).
% 6.40/2.27  tff(c_1427, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_299])).
% 6.40/2.27  tff(c_1443, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1427, c_2])).
% 6.40/2.27  tff(c_1435, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1427, c_1427, c_10])).
% 6.40/2.27  tff(c_16, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.40/2.27  tff(c_1437, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1427, c_1427, c_16])).
% 6.40/2.27  tff(c_1676, plain, (![A_156, B_157, C_158]: (k2_relset_1(A_156, B_157, C_158)=k2_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.40/2.27  tff(c_1691, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1676])).
% 6.40/2.27  tff(c_1695, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_74, c_1691])).
% 6.40/2.27  tff(c_300, plain, (![B_52, A_53]: (v1_xboole_0(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.40/2.27  tff(c_314, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_300])).
% 6.40/2.27  tff(c_342, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_314])).
% 6.40/2.27  tff(c_1696, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_342])).
% 6.40/2.27  tff(c_1703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1443, c_1435, c_1696])).
% 6.40/2.27  tff(c_1704, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_314])).
% 6.40/2.27  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.40/2.27  tff(c_1709, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1704, c_4])).
% 6.40/2.27  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.40/2.27  tff(c_130, plain, (![A_34]: (m1_subset_1(k6_relat_1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.40/2.27  tff(c_134, plain, (m1_subset_1(k6_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_130])).
% 6.40/2.27  tff(c_303, plain, (v1_xboole_0(k6_relat_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_134, c_300])).
% 6.40/2.27  tff(c_312, plain, (v1_xboole_0(k6_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_303])).
% 6.40/2.27  tff(c_327, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_312, c_4])).
% 6.40/2.27  tff(c_329, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_134])).
% 6.40/2.27  tff(c_1809, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_1709, c_329])).
% 6.40/2.27  tff(c_1717, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_1709, c_16])).
% 6.40/2.27  tff(c_255, plain, (![A_47]: (k1_relat_1(A_47)!=k1_xboole_0 | k1_xboole_0=A_47 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.40/2.27  tff(c_262, plain, (![A_9]: (k1_relat_1(k2_funct_1(A_9))!=k1_xboole_0 | k2_funct_1(A_9)=k1_xboole_0 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_26, c_255])).
% 6.40/2.27  tff(c_2728, plain, (![A_249]: (k1_relat_1(k2_funct_1(A_249))!='#skF_3' | k2_funct_1(A_249)='#skF_3' | ~v1_funct_1(A_249) | ~v1_relat_1(A_249))), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_1709, c_262])).
% 6.40/2.27  tff(c_3176, plain, (![A_302]: (k2_relat_1(A_302)!='#skF_3' | k2_funct_1(A_302)='#skF_3' | ~v1_funct_1(A_302) | ~v1_relat_1(A_302) | ~v2_funct_1(A_302) | ~v1_funct_1(A_302) | ~v1_relat_1(A_302))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2728])).
% 6.40/2.27  tff(c_3179, plain, (k2_relat_1('#skF_3')!='#skF_3' | k2_funct_1('#skF_3')='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_3176])).
% 6.40/2.27  tff(c_3182, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_1717, c_3179])).
% 6.40/2.27  tff(c_1713, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_1709, c_12])).
% 6.40/2.27  tff(c_1705, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_314])).
% 6.40/2.27  tff(c_1753, plain, (![A_163]: (A_163='#skF_3' | ~v1_xboole_0(A_163))), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_4])).
% 6.40/2.27  tff(c_1760, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_1705, c_1753])).
% 6.40/2.27  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.40/2.27  tff(c_1732, plain, (![B_4, A_3]: (B_4='#skF_3' | A_3='#skF_3' | k2_zfmisc_1(A_3, B_4)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_1709, c_1709, c_8])).
% 6.40/2.27  tff(c_1843, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1760, c_1732])).
% 6.40/2.27  tff(c_1847, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_1843])).
% 6.40/2.27  tff(c_1861, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_1709])).
% 6.40/2.27  tff(c_48, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_22, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.40/2.27  tff(c_85, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 6.40/2.27  tff(c_1874, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_85])).
% 6.40/2.27  tff(c_1888, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1861, c_1861, c_1874])).
% 6.40/2.27  tff(c_1710, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_1709, c_327])).
% 6.40/2.27  tff(c_1854, plain, (k6_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_1847, c_1710])).
% 6.40/2.27  tff(c_1921, plain, (![B_169]: (k2_zfmisc_1('#skF_1', B_169)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_1847, c_1713])).
% 6.40/2.27  tff(c_46, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.40/2.27  tff(c_1929, plain, (m1_subset_1(k6_relat_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1921, c_46])).
% 6.40/2.27  tff(c_1933, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1854, c_1929])).
% 6.40/2.27  tff(c_1935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1888, c_1933])).
% 6.40/2.27  tff(c_1937, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_85])).
% 6.40/2.27  tff(c_1942, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1861, c_1861, c_1937])).
% 6.40/2.27  tff(c_1863, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_291])).
% 6.40/2.27  tff(c_1869, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_82])).
% 6.40/2.27  tff(c_1857, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_1847, c_1717])).
% 6.40/2.27  tff(c_1868, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_76])).
% 6.40/2.27  tff(c_2387, plain, (![A_215]: (k1_relat_1(k2_funct_1(A_215))!='#skF_1' | k2_funct_1(A_215)='#skF_1' | ~v1_funct_1(A_215) | ~v1_relat_1(A_215))), inference(demodulation, [status(thm), theory('equality')], [c_1861, c_1861, c_262])).
% 6.40/2.27  tff(c_2602, plain, (![A_239]: (k2_relat_1(A_239)!='#skF_1' | k2_funct_1(A_239)='#skF_1' | ~v1_funct_1(A_239) | ~v1_relat_1(A_239) | ~v2_funct_1(A_239) | ~v1_funct_1(A_239) | ~v1_relat_1(A_239))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2387])).
% 6.40/2.27  tff(c_2605, plain, (k2_relat_1('#skF_1')!='#skF_1' | k2_funct_1('#skF_1')='#skF_1' | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1868, c_2602])).
% 6.40/2.27  tff(c_2608, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_1869, c_1857, c_2605])).
% 6.40/2.27  tff(c_1715, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_1709, c_10])).
% 6.40/2.27  tff(c_1852, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_1847, c_1715])).
% 6.40/2.27  tff(c_1864, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_254])).
% 6.40/2.27  tff(c_2081, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1852, c_1864])).
% 6.40/2.27  tff(c_2609, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2608, c_2081])).
% 6.40/2.27  tff(c_2613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1942, c_2609])).
% 6.40/2.27  tff(c_2614, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1843])).
% 6.40/2.27  tff(c_2617, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2614, c_254])).
% 6.40/2.27  tff(c_2621, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1713, c_2617])).
% 6.40/2.27  tff(c_3183, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3182, c_2621])).
% 6.40/2.27  tff(c_3187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1809, c_3183])).
% 6.40/2.27  tff(c_3188, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_250])).
% 6.40/2.27  tff(c_3237, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3230, c_20])).
% 6.40/2.27  tff(c_3256, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3237])).
% 6.40/2.27  tff(c_3459, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3458, c_3256])).
% 6.40/2.27  tff(c_3474, plain, (![A_327, B_328, C_329]: (k1_relset_1(A_327, B_328, C_329)=k1_relat_1(C_329) | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_327, B_328))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.40/2.27  tff(c_3496, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3474])).
% 6.40/2.27  tff(c_3831, plain, (![B_361, A_362, C_363]: (k1_xboole_0=B_361 | k1_relset_1(A_362, B_361, C_363)=A_362 | ~v1_funct_2(C_363, A_362, B_361) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_362, B_361))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.40/2.27  tff(c_3849, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_3831])).
% 6.40/2.27  tff(c_3868, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3496, c_3849])).
% 6.40/2.27  tff(c_3869, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_3459, c_3868])).
% 6.40/2.27  tff(c_3238, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3230, c_22])).
% 6.40/2.27  tff(c_3257, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3238])).
% 6.40/2.27  tff(c_3877, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3869, c_3257])).
% 6.40/2.27  tff(c_3189, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_250])).
% 6.40/2.27  tff(c_3494, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3189, c_3474])).
% 6.40/2.27  tff(c_3931, plain, (![B_364, C_365, A_366]: (k1_xboole_0=B_364 | v1_funct_2(C_365, A_366, B_364) | k1_relset_1(A_366, B_364, C_365)!=A_366 | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(A_366, B_364))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.40/2.27  tff(c_3940, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_3189, c_3931])).
% 6.40/2.27  tff(c_3956, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3494, c_3940])).
% 6.40/2.27  tff(c_3957, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3188, c_3877, c_3956])).
% 6.40/2.27  tff(c_3967, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_3957])).
% 6.40/2.27  tff(c_3970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3230, c_82, c_76, c_3458, c_3967])).
% 6.40/2.27  tff(c_3971, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3238])).
% 6.40/2.27  tff(c_3973, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3971, c_3256])).
% 6.40/2.27  tff(c_3981, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3971, c_3971, c_16])).
% 6.40/2.27  tff(c_3999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3973, c_3981])).
% 6.40/2.27  tff(c_4000, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3237])).
% 6.40/2.27  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.40/2.27  tff(c_4010, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_4000, c_6])).
% 6.40/2.27  tff(c_4009, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4000, c_4000, c_16])).
% 6.40/2.27  tff(c_4011, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4000, c_4000, c_18])).
% 6.40/2.27  tff(c_4777, plain, (![B_422, A_423]: (v1_funct_2(B_422, k1_relat_1(B_422), A_423) | ~r1_tarski(k2_relat_1(B_422), A_423) | ~v1_funct_1(B_422) | ~v1_relat_1(B_422))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.40/2.27  tff(c_4786, plain, (![A_423]: (v1_funct_2('#skF_3', '#skF_3', A_423) | ~r1_tarski(k2_relat_1('#skF_3'), A_423) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4011, c_4777])).
% 6.40/2.27  tff(c_4789, plain, (![A_423]: (v1_funct_2('#skF_3', '#skF_3', A_423))), inference(demodulation, [status(thm), theory('equality')], [c_3230, c_82, c_4010, c_4009, c_4786])).
% 6.40/2.27  tff(c_4015, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4000, c_2])).
% 6.40/2.27  tff(c_4005, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4000, c_4000, c_12])).
% 6.40/2.27  tff(c_4408, plain, (![A_394, B_395, C_396]: (k2_relset_1(A_394, B_395, C_396)=k2_relat_1(C_396) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(A_394, B_395))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.40/2.27  tff(c_4423, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_4408])).
% 6.40/2.27  tff(c_4428, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4009, c_4423])).
% 6.40/2.27  tff(c_4061, plain, (![B_373, A_374]: (v1_xboole_0(B_373) | ~m1_subset_1(B_373, k1_zfmisc_1(A_374)) | ~v1_xboole_0(A_374))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.40/2.27  tff(c_4071, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_3189, c_4061])).
% 6.40/2.27  tff(c_4111, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_4071])).
% 6.40/2.27  tff(c_4431, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4428, c_4111])).
% 6.40/2.27  tff(c_4438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4015, c_4005, c_4431])).
% 6.40/2.27  tff(c_4440, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_4071])).
% 6.40/2.27  tff(c_4006, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4000, c_4])).
% 6.40/2.27  tff(c_4484, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_4440, c_4006])).
% 6.40/2.27  tff(c_4022, plain, (![B_4, A_3]: (B_4='#skF_3' | A_3='#skF_3' | k2_zfmisc_1(A_3, B_4)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4000, c_4000, c_4000, c_8])).
% 6.40/2.27  tff(c_4495, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4484, c_4022])).
% 6.40/2.27  tff(c_4503, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_4495])).
% 6.40/2.27  tff(c_4439, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4071])).
% 6.40/2.27  tff(c_4444, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_4439, c_4006])).
% 6.40/2.27  tff(c_4448, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4444, c_3188])).
% 6.40/2.27  tff(c_4516, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4503, c_4448])).
% 6.40/2.27  tff(c_4793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4789, c_4516])).
% 6.40/2.27  tff(c_4794, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_4495])).
% 6.40/2.27  tff(c_4795, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_4495])).
% 6.40/2.27  tff(c_4822, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4794, c_4795])).
% 6.40/2.27  tff(c_4004, plain, (m1_subset_1(k6_relat_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4000, c_4000, c_134])).
% 6.40/2.27  tff(c_4103, plain, (v1_xboole_0(k6_relat_1('#skF_3')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4004, c_14])).
% 6.40/2.27  tff(c_4106, plain, (v1_xboole_0(k6_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4015, c_4103])).
% 6.40/2.27  tff(c_4110, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_4106, c_4006])).
% 6.40/2.27  tff(c_4468, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4110, c_4004])).
% 6.40/2.27  tff(c_4796, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4794, c_4794, c_4468])).
% 6.40/2.27  tff(c_4811, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4794, c_4000])).
% 6.40/2.27  tff(c_4878, plain, (![A_22]: (v1_funct_2('#skF_1', A_22, '#skF_1') | A_22='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4811, c_4811, c_4811, c_4811, c_4811, c_85])).
% 6.40/2.27  tff(c_4879, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_4878])).
% 6.40/2.27  tff(c_4934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4796, c_4879])).
% 6.40/2.27  tff(c_5044, plain, (![A_436]: (v1_funct_2('#skF_1', A_436, '#skF_1') | A_436='#skF_1')), inference(splitRight, [status(thm)], [c_4878])).
% 6.40/2.27  tff(c_4799, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4794, c_4448])).
% 6.40/2.27  tff(c_5047, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_5044, c_4799])).
% 6.40/2.27  tff(c_5051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4822, c_5047])).
% 6.40/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.40/2.27  
% 6.40/2.27  Inference rules
% 6.40/2.27  ----------------------
% 6.40/2.27  #Ref     : 0
% 6.40/2.27  #Sup     : 1069
% 6.40/2.27  #Fact    : 0
% 6.40/2.27  #Define  : 0
% 6.40/2.27  #Split   : 29
% 6.40/2.27  #Chain   : 0
% 6.40/2.27  #Close   : 0
% 6.40/2.27  
% 6.40/2.27  Ordering : KBO
% 6.40/2.27  
% 6.40/2.27  Simplification rules
% 6.40/2.27  ----------------------
% 6.40/2.27  #Subsume      : 101
% 6.40/2.27  #Demod        : 1551
% 6.40/2.27  #Tautology    : 703
% 6.40/2.27  #SimpNegUnit  : 18
% 6.40/2.27  #BackRed      : 191
% 6.40/2.27  
% 6.40/2.27  #Partial instantiations: 0
% 6.40/2.27  #Strategies tried      : 1
% 6.40/2.27  
% 6.40/2.27  Timing (in seconds)
% 6.40/2.27  ----------------------
% 6.40/2.27  Preprocessing        : 0.34
% 6.40/2.27  Parsing              : 0.19
% 6.40/2.27  CNF conversion       : 0.02
% 6.40/2.27  Main loop            : 1.08
% 6.40/2.27  Inferencing          : 0.37
% 6.40/2.27  Reduction            : 0.38
% 6.40/2.27  Demodulation         : 0.27
% 6.40/2.27  BG Simplification    : 0.04
% 6.40/2.27  Subsumption          : 0.18
% 6.40/2.27  Abstraction          : 0.04
% 6.40/2.27  MUC search           : 0.00
% 6.40/2.27  Cooper               : 0.00
% 6.40/2.27  Total                : 1.51
% 6.40/2.27  Index Insertion      : 0.00
% 6.40/2.27  Index Deletion       : 0.00
% 6.40/2.27  Index Matching       : 0.00
% 6.40/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
