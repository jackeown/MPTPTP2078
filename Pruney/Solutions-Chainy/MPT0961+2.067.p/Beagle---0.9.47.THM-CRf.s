%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:50 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 508 expanded)
%              Number of leaves         :   23 ( 173 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 (1250 expanded)
%              Number of equality atoms :   55 ( 587 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_72,axiom,(
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

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_519,plain,(
    ! [A_95,B_96] :
      ( m1_subset_1(A_95,k1_zfmisc_1(B_96))
      | ~ r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_296,plain,(
    ! [A_67] :
      ( r1_tarski(A_67,k2_zfmisc_1(k1_relat_1(A_67),k2_relat_1(A_67)))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5] :
      ( r1_tarski(A_5,k2_zfmisc_1(k1_relat_1(A_5),k2_relat_1(A_5)))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    ! [A_24,B_25,C_26] :
      ( k1_relset_1(A_24,B_25,C_26) = k1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_160,plain,(
    ! [A_40,B_41,A_42] :
      ( k1_relset_1(A_40,B_41,A_42) = k1_relat_1(A_42)
      | ~ r1_tarski(A_42,k2_zfmisc_1(A_40,B_41)) ) ),
    inference(resolution,[status(thm)],[c_10,c_117])).

tff(c_170,plain,(
    ! [A_5] :
      ( k1_relset_1(k1_relat_1(A_5),k2_relat_1(A_5),A_5) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_160])).

tff(c_78,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_83,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_194,plain,(
    ! [B_48,C_49,A_50] :
      ( k1_xboole_0 = B_48
      | v1_funct_2(C_49,A_50,B_48)
      | k1_relset_1(A_50,B_48,C_49) != A_50
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_216,plain,(
    ! [B_53,A_54,A_55] :
      ( k1_xboole_0 = B_53
      | v1_funct_2(A_54,A_55,B_53)
      | k1_relset_1(A_55,B_53,A_54) != A_55
      | ~ r1_tarski(A_54,k2_zfmisc_1(A_55,B_53)) ) ),
    inference(resolution,[status(thm)],[c_10,c_194])).

tff(c_245,plain,(
    ! [A_61] :
      ( k2_relat_1(A_61) = k1_xboole_0
      | v1_funct_2(A_61,k1_relat_1(A_61),k2_relat_1(A_61))
      | k1_relset_1(k1_relat_1(A_61),k2_relat_1(A_61),A_61) != k1_relat_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_12,c_216])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_84,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_248,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_245,c_84])).

tff(c_257,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_248])).

tff(c_258,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_257])).

tff(c_263,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_258])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_263])).

tff(c_268,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_284,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_268])).

tff(c_299,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_296,c_284])).

tff(c_309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_299])).

tff(c_310,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_316,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_310,c_16])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_313,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_310,c_4])).

tff(c_311,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_321,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_311])).

tff(c_387,plain,(
    ! [A_76] :
      ( r1_tarski(A_76,k2_zfmisc_1(k1_relat_1(A_76),k2_relat_1(A_76)))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_390,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1('#skF_1',k2_relat_1('#skF_1')))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_387])).

tff(c_395,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_313,c_321,c_390])).

tff(c_24,plain,(
    ! [A_10] :
      ( v1_funct_2(k1_xboole_0,A_10,k1_xboole_0)
      | k1_xboole_0 = A_10
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_10,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_45,plain,(
    ! [A_10] :
      ( v1_funct_2(k1_xboole_0,A_10,k1_xboole_0)
      | k1_xboole_0 = A_10
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_399,plain,(
    ! [A_10] :
      ( v1_funct_2('#skF_1',A_10,'#skF_1')
      | A_10 = '#skF_1'
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_310,c_310,c_310,c_310,c_45])).

tff(c_400,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_399])).

tff(c_415,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_400])).

tff(c_419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_415])).

tff(c_421,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_314,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_310,c_6])).

tff(c_441,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_474,plain,(
    ! [B_89,C_90] :
      ( k1_relset_1('#skF_1',B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_441])).

tff(c_476,plain,(
    ! [B_89] : k1_relset_1('#skF_1',B_89,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_421,c_474])).

tff(c_481,plain,(
    ! [B_89] : k1_relset_1('#skF_1',B_89,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_476])).

tff(c_28,plain,(
    ! [C_12,B_11] :
      ( v1_funct_2(C_12,k1_xboole_0,B_11)
      | k1_relset_1(k1_xboole_0,B_11,C_12) != k1_xboole_0
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    ! [C_12,B_11] :
      ( v1_funct_2(C_12,k1_xboole_0,B_11)
      | k1_relset_1(k1_xboole_0,B_11,C_12) != k1_xboole_0
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_454,plain,(
    ! [C_86,B_87] :
      ( v1_funct_2(C_86,'#skF_1',B_87)
      | k1_relset_1('#skF_1',B_87,C_86) != '#skF_1'
      | ~ m1_subset_1(C_86,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_310,c_310,c_310,c_44])).

tff(c_462,plain,(
    ! [B_88] :
      ( v1_funct_2('#skF_1','#skF_1',B_88)
      | k1_relset_1('#skF_1',B_88,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_421,c_454])).

tff(c_345,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_321,c_313,c_316,c_321,c_42])).

tff(c_346,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_473,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_462,c_346])).

tff(c_501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_473])).

tff(c_502,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_526,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_519,c_502])).

tff(c_548,plain,(
    ! [A_100] :
      ( r1_tarski(A_100,k2_zfmisc_1(k1_relat_1(A_100),k2_relat_1(A_100)))
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_551,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1('#skF_1',k2_relat_1('#skF_1')))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_548])).

tff(c_556,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_313,c_321,c_551])).

tff(c_558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_526,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.34  
% 2.52/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.34  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.52/1.34  
% 2.52/1.34  %Foreground sorts:
% 2.52/1.34  
% 2.52/1.34  
% 2.52/1.34  %Background operators:
% 2.52/1.34  
% 2.52/1.34  
% 2.52/1.34  %Foreground operators:
% 2.52/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.52/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.52/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.52/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.52/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.52/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.52/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.52/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.52/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.52/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.52/1.34  
% 2.52/1.36  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.52/1.36  tff(f_83, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 2.52/1.36  tff(f_39, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.52/1.36  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.52/1.36  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.52/1.36  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.52/1.36  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.52/1.36  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.52/1.36  tff(c_519, plain, (![A_95, B_96]: (m1_subset_1(A_95, k1_zfmisc_1(B_96)) | ~r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.52/1.36  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.36  tff(c_296, plain, (![A_67]: (r1_tarski(A_67, k2_zfmisc_1(k1_relat_1(A_67), k2_relat_1(A_67))) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.52/1.36  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.52/1.36  tff(c_12, plain, (![A_5]: (r1_tarski(A_5, k2_zfmisc_1(k1_relat_1(A_5), k2_relat_1(A_5))) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.52/1.36  tff(c_117, plain, (![A_24, B_25, C_26]: (k1_relset_1(A_24, B_25, C_26)=k1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.52/1.36  tff(c_160, plain, (![A_40, B_41, A_42]: (k1_relset_1(A_40, B_41, A_42)=k1_relat_1(A_42) | ~r1_tarski(A_42, k2_zfmisc_1(A_40, B_41)))), inference(resolution, [status(thm)], [c_10, c_117])).
% 2.52/1.36  tff(c_170, plain, (![A_5]: (k1_relset_1(k1_relat_1(A_5), k2_relat_1(A_5), A_5)=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_12, c_160])).
% 2.52/1.36  tff(c_78, plain, (![A_17]: (k2_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.52/1.36  tff(c_82, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_40, c_78])).
% 2.52/1.36  tff(c_83, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_82])).
% 2.52/1.36  tff(c_194, plain, (![B_48, C_49, A_50]: (k1_xboole_0=B_48 | v1_funct_2(C_49, A_50, B_48) | k1_relset_1(A_50, B_48, C_49)!=A_50 | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_48))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.36  tff(c_216, plain, (![B_53, A_54, A_55]: (k1_xboole_0=B_53 | v1_funct_2(A_54, A_55, B_53) | k1_relset_1(A_55, B_53, A_54)!=A_55 | ~r1_tarski(A_54, k2_zfmisc_1(A_55, B_53)))), inference(resolution, [status(thm)], [c_10, c_194])).
% 2.52/1.36  tff(c_245, plain, (![A_61]: (k2_relat_1(A_61)=k1_xboole_0 | v1_funct_2(A_61, k1_relat_1(A_61), k2_relat_1(A_61)) | k1_relset_1(k1_relat_1(A_61), k2_relat_1(A_61), A_61)!=k1_relat_1(A_61) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_12, c_216])).
% 2.52/1.36  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.36  tff(c_36, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.36  tff(c_42, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 2.52/1.36  tff(c_84, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.52/1.36  tff(c_248, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_245, c_84])).
% 2.52/1.36  tff(c_257, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_248])).
% 2.52/1.36  tff(c_258, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_83, c_257])).
% 2.52/1.36  tff(c_263, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_170, c_258])).
% 2.52/1.36  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_263])).
% 2.52/1.36  tff(c_268, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_42])).
% 2.52/1.36  tff(c_284, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_268])).
% 2.52/1.36  tff(c_299, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_296, c_284])).
% 2.52/1.36  tff(c_309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_299])).
% 2.52/1.36  tff(c_310, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_82])).
% 2.52/1.36  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.52/1.36  tff(c_316, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_310, c_310, c_16])).
% 2.52/1.36  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.36  tff(c_313, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_310, c_4])).
% 2.52/1.36  tff(c_311, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_82])).
% 2.52/1.36  tff(c_321, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_310, c_311])).
% 2.52/1.36  tff(c_387, plain, (![A_76]: (r1_tarski(A_76, k2_zfmisc_1(k1_relat_1(A_76), k2_relat_1(A_76))) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.52/1.36  tff(c_390, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_1', k2_relat_1('#skF_1'))) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_316, c_387])).
% 2.52/1.36  tff(c_395, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_313, c_321, c_390])).
% 2.52/1.36  tff(c_24, plain, (![A_10]: (v1_funct_2(k1_xboole_0, A_10, k1_xboole_0) | k1_xboole_0=A_10 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_10, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.36  tff(c_45, plain, (![A_10]: (v1_funct_2(k1_xboole_0, A_10, k1_xboole_0) | k1_xboole_0=A_10 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_24])).
% 2.52/1.36  tff(c_399, plain, (![A_10]: (v1_funct_2('#skF_1', A_10, '#skF_1') | A_10='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_310, c_310, c_310, c_310, c_45])).
% 2.52/1.36  tff(c_400, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_399])).
% 2.52/1.36  tff(c_415, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_10, c_400])).
% 2.52/1.36  tff(c_419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_395, c_415])).
% 2.52/1.36  tff(c_421, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_399])).
% 2.52/1.36  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.36  tff(c_314, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_310, c_6])).
% 2.52/1.36  tff(c_441, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.52/1.36  tff(c_474, plain, (![B_89, C_90]: (k1_relset_1('#skF_1', B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_314, c_441])).
% 2.52/1.36  tff(c_476, plain, (![B_89]: (k1_relset_1('#skF_1', B_89, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_421, c_474])).
% 2.52/1.36  tff(c_481, plain, (![B_89]: (k1_relset_1('#skF_1', B_89, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_476])).
% 2.52/1.36  tff(c_28, plain, (![C_12, B_11]: (v1_funct_2(C_12, k1_xboole_0, B_11) | k1_relset_1(k1_xboole_0, B_11, C_12)!=k1_xboole_0 | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_11))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.36  tff(c_44, plain, (![C_12, B_11]: (v1_funct_2(C_12, k1_xboole_0, B_11) | k1_relset_1(k1_xboole_0, B_11, C_12)!=k1_xboole_0 | ~m1_subset_1(C_12, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_28])).
% 2.52/1.36  tff(c_454, plain, (![C_86, B_87]: (v1_funct_2(C_86, '#skF_1', B_87) | k1_relset_1('#skF_1', B_87, C_86)!='#skF_1' | ~m1_subset_1(C_86, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_310, c_310, c_310, c_44])).
% 2.52/1.36  tff(c_462, plain, (![B_88]: (v1_funct_2('#skF_1', '#skF_1', B_88) | k1_relset_1('#skF_1', B_88, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_421, c_454])).
% 2.52/1.36  tff(c_345, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_321, c_313, c_316, c_321, c_42])).
% 2.52/1.36  tff(c_346, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_345])).
% 2.52/1.36  tff(c_473, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_462, c_346])).
% 2.52/1.36  tff(c_501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_481, c_473])).
% 2.52/1.36  tff(c_502, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_345])).
% 2.52/1.36  tff(c_526, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_519, c_502])).
% 2.52/1.36  tff(c_548, plain, (![A_100]: (r1_tarski(A_100, k2_zfmisc_1(k1_relat_1(A_100), k2_relat_1(A_100))) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.52/1.36  tff(c_551, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_1', k2_relat_1('#skF_1'))) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_316, c_548])).
% 2.52/1.36  tff(c_556, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_313, c_321, c_551])).
% 2.52/1.36  tff(c_558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_526, c_556])).
% 2.52/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.36  
% 2.52/1.36  Inference rules
% 2.52/1.36  ----------------------
% 2.52/1.36  #Ref     : 0
% 2.52/1.36  #Sup     : 107
% 2.52/1.36  #Fact    : 0
% 2.52/1.36  #Define  : 0
% 2.52/1.36  #Split   : 8
% 2.52/1.36  #Chain   : 0
% 2.52/1.36  #Close   : 0
% 2.52/1.36  
% 2.52/1.36  Ordering : KBO
% 2.52/1.36  
% 2.52/1.36  Simplification rules
% 2.52/1.36  ----------------------
% 2.52/1.36  #Subsume      : 12
% 2.52/1.36  #Demod        : 84
% 2.52/1.36  #Tautology    : 57
% 2.52/1.36  #SimpNegUnit  : 2
% 2.52/1.36  #BackRed      : 7
% 2.52/1.36  
% 2.52/1.36  #Partial instantiations: 0
% 2.52/1.36  #Strategies tried      : 1
% 2.52/1.36  
% 2.52/1.36  Timing (in seconds)
% 2.52/1.36  ----------------------
% 2.52/1.36  Preprocessing        : 0.31
% 2.52/1.36  Parsing              : 0.17
% 2.52/1.36  CNF conversion       : 0.02
% 2.52/1.36  Main loop            : 0.28
% 2.52/1.36  Inferencing          : 0.10
% 2.52/1.36  Reduction            : 0.08
% 2.52/1.36  Demodulation         : 0.05
% 2.52/1.36  BG Simplification    : 0.02
% 2.52/1.36  Subsumption          : 0.06
% 2.52/1.36  Abstraction          : 0.02
% 2.52/1.36  MUC search           : 0.00
% 2.52/1.36  Cooper               : 0.00
% 2.52/1.36  Total                : 0.62
% 2.52/1.36  Index Insertion      : 0.00
% 2.52/1.36  Index Deletion       : 0.00
% 2.52/1.36  Index Matching       : 0.00
% 2.52/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
