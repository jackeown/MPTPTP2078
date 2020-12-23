%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:48 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 247 expanded)
%              Number of leaves         :   26 (  90 expanded)
%              Depth                    :    9
%              Number of atoms          :  146 ( 578 expanded)
%              Number of equality atoms :   63 ( 243 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_81,axiom,(
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

tff(f_40,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_49,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_771,plain,(
    ! [C_123,A_124,B_125] :
      ( m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ r1_tarski(k2_relat_1(C_123),B_125)
      | ~ r1_tarski(k1_relat_1(C_123),A_124)
      | ~ v1_relat_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_188,plain,(
    ! [C_37,A_38,B_39] :
      ( m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ r1_tarski(k2_relat_1(C_37),B_39)
      | ~ r1_tarski(k1_relat_1(C_37),A_38)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( k1_relset_1(A_6,B_7,C_8) = k1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_333,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ r1_tarski(k2_relat_1(C_62),B_61)
      | ~ r1_tarski(k1_relat_1(C_62),A_60)
      | ~ v1_relat_1(C_62) ) ),
    inference(resolution,[status(thm)],[c_188,c_24])).

tff(c_341,plain,(
    ! [A_63,C_64] :
      ( k1_relset_1(A_63,k2_relat_1(C_64),C_64) = k1_relat_1(C_64)
      | ~ r1_tarski(k1_relat_1(C_64),A_63)
      | ~ v1_relat_1(C_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_333])).

tff(c_347,plain,(
    ! [C_64] :
      ( k1_relset_1(k1_relat_1(C_64),k2_relat_1(C_64),C_64) = k1_relat_1(C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_341])).

tff(c_112,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_116,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_112])).

tff(c_118,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_26,plain,(
    ! [C_11,A_9,B_10] :
      ( m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ r1_tarski(k2_relat_1(C_11),B_10)
      | ~ r1_tarski(k1_relat_1(C_11),A_9)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_246,plain,(
    ! [B_47,C_48,A_49] :
      ( k1_xboole_0 = B_47
      | v1_funct_2(C_48,A_49,B_47)
      | k1_relset_1(A_49,B_47,C_48) != A_49
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_383,plain,(
    ! [B_69,C_70,A_71] :
      ( k1_xboole_0 = B_69
      | v1_funct_2(C_70,A_71,B_69)
      | k1_relset_1(A_71,B_69,C_70) != A_71
      | ~ r1_tarski(k2_relat_1(C_70),B_69)
      | ~ r1_tarski(k1_relat_1(C_70),A_71)
      | ~ v1_relat_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_26,c_246])).

tff(c_391,plain,(
    ! [C_72,A_73] :
      ( k2_relat_1(C_72) = k1_xboole_0
      | v1_funct_2(C_72,A_73,k2_relat_1(C_72))
      | k1_relset_1(A_73,k2_relat_1(C_72),C_72) != A_73
      | ~ r1_tarski(k1_relat_1(C_72),A_73)
      | ~ v1_relat_1(C_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_383])).

tff(c_44,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_104,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_399,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_391,c_104])).

tff(c_409,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6,c_399])).

tff(c_410,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_409])).

tff(c_414,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_410])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_414])).

tff(c_419,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_429,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_419,c_16])).

tff(c_107,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_111,plain,
    ( k1_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_107])).

tff(c_117,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_421,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_117])).

tff(c_455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_421])).

tff(c_456,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_457,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_471,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_457])).

tff(c_22,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [A_19] : m1_subset_1(k6_relat_1(A_19),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_93,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_89])).

tff(c_101,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_93])).

tff(c_460,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_101])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_462,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_12])).

tff(c_575,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_614,plain,(
    ! [B_94,C_95] :
      ( k1_relset_1('#skF_1',B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_575])).

tff(c_616,plain,(
    ! [B_94] : k1_relset_1('#skF_1',B_94,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_460,c_614])).

tff(c_618,plain,(
    ! [B_94] : k1_relset_1('#skF_1',B_94,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_616])).

tff(c_34,plain,(
    ! [C_15,B_14] :
      ( v1_funct_2(C_15,k1_xboole_0,B_14)
      | k1_relset_1(k1_xboole_0,B_14,C_15) != k1_xboole_0
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_50,plain,(
    ! [C_15,B_14] :
      ( v1_funct_2(C_15,k1_xboole_0,B_14)
      | k1_relset_1(k1_xboole_0,B_14,C_15) != k1_xboole_0
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_648,plain,(
    ! [C_100,B_101] :
      ( v1_funct_2(C_100,'#skF_1',B_101)
      | k1_relset_1('#skF_1',B_101,C_100) != '#skF_1'
      | ~ m1_subset_1(C_100,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_456,c_456,c_50])).

tff(c_650,plain,(
    ! [B_101] :
      ( v1_funct_2('#skF_1','#skF_1',B_101)
      | k1_relset_1('#skF_1',B_101,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_460,c_648])).

tff(c_653,plain,(
    ! [B_101] : v1_funct_2('#skF_1','#skF_1',B_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_650])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_464,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_14])).

tff(c_472,plain,(
    ~ v1_funct_2('#skF_1','#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_104])).

tff(c_534,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_472])).

tff(c_665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_534])).

tff(c_666,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_777,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_771,c_666])).

tff(c_788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6,c_6,c_777])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:10:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.40  
% 2.70/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.41  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.70/1.41  
% 2.70/1.41  %Foreground sorts:
% 2.70/1.41  
% 2.70/1.41  
% 2.70/1.41  %Background operators:
% 2.70/1.41  
% 2.70/1.41  
% 2.70/1.41  %Foreground operators:
% 2.70/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.70/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.70/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.41  
% 2.92/1.42  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 2.92/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.92/1.42  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.92/1.42  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.92/1.42  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.92/1.42  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.92/1.42  tff(f_40, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.92/1.42  tff(f_49, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.92/1.42  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.92/1.42  tff(f_63, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.92/1.42  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.92/1.42  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.42  tff(c_771, plain, (![C_123, A_124, B_125]: (m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~r1_tarski(k2_relat_1(C_123), B_125) | ~r1_tarski(k1_relat_1(C_123), A_124) | ~v1_relat_1(C_123))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.92/1.42  tff(c_188, plain, (![C_37, A_38, B_39]: (m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~r1_tarski(k2_relat_1(C_37), B_39) | ~r1_tarski(k1_relat_1(C_37), A_38) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.92/1.42  tff(c_24, plain, (![A_6, B_7, C_8]: (k1_relset_1(A_6, B_7, C_8)=k1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.92/1.42  tff(c_333, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~r1_tarski(k2_relat_1(C_62), B_61) | ~r1_tarski(k1_relat_1(C_62), A_60) | ~v1_relat_1(C_62))), inference(resolution, [status(thm)], [c_188, c_24])).
% 2.92/1.42  tff(c_341, plain, (![A_63, C_64]: (k1_relset_1(A_63, k2_relat_1(C_64), C_64)=k1_relat_1(C_64) | ~r1_tarski(k1_relat_1(C_64), A_63) | ~v1_relat_1(C_64))), inference(resolution, [status(thm)], [c_6, c_333])).
% 2.92/1.42  tff(c_347, plain, (![C_64]: (k1_relset_1(k1_relat_1(C_64), k2_relat_1(C_64), C_64)=k1_relat_1(C_64) | ~v1_relat_1(C_64))), inference(resolution, [status(thm)], [c_6, c_341])).
% 2.92/1.42  tff(c_112, plain, (![A_21]: (k2_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.92/1.42  tff(c_116, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_112])).
% 2.92/1.42  tff(c_118, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_116])).
% 2.92/1.42  tff(c_26, plain, (![C_11, A_9, B_10]: (m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~r1_tarski(k2_relat_1(C_11), B_10) | ~r1_tarski(k1_relat_1(C_11), A_9) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.92/1.42  tff(c_246, plain, (![B_47, C_48, A_49]: (k1_xboole_0=B_47 | v1_funct_2(C_48, A_49, B_47) | k1_relset_1(A_49, B_47, C_48)!=A_49 | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_47))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.92/1.42  tff(c_383, plain, (![B_69, C_70, A_71]: (k1_xboole_0=B_69 | v1_funct_2(C_70, A_71, B_69) | k1_relset_1(A_71, B_69, C_70)!=A_71 | ~r1_tarski(k2_relat_1(C_70), B_69) | ~r1_tarski(k1_relat_1(C_70), A_71) | ~v1_relat_1(C_70))), inference(resolution, [status(thm)], [c_26, c_246])).
% 2.92/1.42  tff(c_391, plain, (![C_72, A_73]: (k2_relat_1(C_72)=k1_xboole_0 | v1_funct_2(C_72, A_73, k2_relat_1(C_72)) | k1_relset_1(A_73, k2_relat_1(C_72), C_72)!=A_73 | ~r1_tarski(k1_relat_1(C_72), A_73) | ~v1_relat_1(C_72))), inference(resolution, [status(thm)], [c_6, c_383])).
% 2.92/1.42  tff(c_44, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.92/1.42  tff(c_42, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.92/1.42  tff(c_48, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 2.92/1.42  tff(c_104, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.92/1.42  tff(c_399, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_391, c_104])).
% 2.92/1.42  tff(c_409, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6, c_399])).
% 2.92/1.42  tff(c_410, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_118, c_409])).
% 2.92/1.42  tff(c_414, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_347, c_410])).
% 2.92/1.42  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_414])).
% 2.92/1.42  tff(c_419, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_116])).
% 2.92/1.42  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.92/1.42  tff(c_429, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_419, c_419, c_16])).
% 2.92/1.42  tff(c_107, plain, (![A_20]: (k1_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.92/1.42  tff(c_111, plain, (k1_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_107])).
% 2.92/1.42  tff(c_117, plain, (k1_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_111])).
% 2.92/1.42  tff(c_421, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_419, c_117])).
% 2.92/1.42  tff(c_455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_429, c_421])).
% 2.92/1.42  tff(c_456, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_111])).
% 2.92/1.42  tff(c_457, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_111])).
% 2.92/1.42  tff(c_471, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_456, c_457])).
% 2.92/1.42  tff(c_22, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.92/1.42  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.92/1.42  tff(c_89, plain, (![A_19]: (m1_subset_1(k6_relat_1(A_19), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.92/1.42  tff(c_93, plain, (m1_subset_1(k6_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_89])).
% 2.92/1.42  tff(c_101, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_93])).
% 2.92/1.42  tff(c_460, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_456, c_456, c_101])).
% 2.92/1.42  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.92/1.42  tff(c_462, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_456, c_456, c_12])).
% 2.92/1.42  tff(c_575, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.92/1.42  tff(c_614, plain, (![B_94, C_95]: (k1_relset_1('#skF_1', B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_462, c_575])).
% 2.92/1.42  tff(c_616, plain, (![B_94]: (k1_relset_1('#skF_1', B_94, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_460, c_614])).
% 2.92/1.42  tff(c_618, plain, (![B_94]: (k1_relset_1('#skF_1', B_94, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_471, c_616])).
% 2.92/1.42  tff(c_34, plain, (![C_15, B_14]: (v1_funct_2(C_15, k1_xboole_0, B_14) | k1_relset_1(k1_xboole_0, B_14, C_15)!=k1_xboole_0 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.92/1.42  tff(c_50, plain, (![C_15, B_14]: (v1_funct_2(C_15, k1_xboole_0, B_14) | k1_relset_1(k1_xboole_0, B_14, C_15)!=k1_xboole_0 | ~m1_subset_1(C_15, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 2.92/1.42  tff(c_648, plain, (![C_100, B_101]: (v1_funct_2(C_100, '#skF_1', B_101) | k1_relset_1('#skF_1', B_101, C_100)!='#skF_1' | ~m1_subset_1(C_100, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_456, c_456, c_456, c_456, c_50])).
% 2.92/1.42  tff(c_650, plain, (![B_101]: (v1_funct_2('#skF_1', '#skF_1', B_101) | k1_relset_1('#skF_1', B_101, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_460, c_648])).
% 2.92/1.42  tff(c_653, plain, (![B_101]: (v1_funct_2('#skF_1', '#skF_1', B_101))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_650])).
% 2.92/1.42  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.92/1.42  tff(c_464, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_456, c_456, c_14])).
% 2.92/1.42  tff(c_472, plain, (~v1_funct_2('#skF_1', '#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_104])).
% 2.92/1.42  tff(c_534, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_472])).
% 2.92/1.42  tff(c_665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_653, c_534])).
% 2.92/1.42  tff(c_666, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_48])).
% 2.92/1.42  tff(c_777, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_771, c_666])).
% 2.92/1.42  tff(c_788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_6, c_6, c_777])).
% 2.92/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.42  
% 2.92/1.42  Inference rules
% 2.92/1.42  ----------------------
% 2.92/1.42  #Ref     : 0
% 2.92/1.42  #Sup     : 159
% 2.92/1.42  #Fact    : 0
% 2.92/1.42  #Define  : 0
% 2.92/1.42  #Split   : 6
% 2.92/1.42  #Chain   : 0
% 2.92/1.42  #Close   : 0
% 2.92/1.42  
% 2.92/1.42  Ordering : KBO
% 2.92/1.42  
% 2.92/1.42  Simplification rules
% 2.92/1.42  ----------------------
% 2.92/1.42  #Subsume      : 5
% 2.92/1.42  #Demod        : 179
% 2.92/1.42  #Tautology    : 117
% 2.92/1.42  #SimpNegUnit  : 1
% 2.92/1.42  #BackRed      : 20
% 2.92/1.42  
% 2.92/1.42  #Partial instantiations: 0
% 2.92/1.42  #Strategies tried      : 1
% 2.92/1.42  
% 2.92/1.42  Timing (in seconds)
% 2.92/1.42  ----------------------
% 2.92/1.43  Preprocessing        : 0.31
% 2.92/1.43  Parsing              : 0.16
% 2.92/1.43  CNF conversion       : 0.02
% 2.92/1.43  Main loop            : 0.34
% 2.92/1.43  Inferencing          : 0.12
% 2.92/1.43  Reduction            : 0.11
% 2.92/1.43  Demodulation         : 0.08
% 2.92/1.43  BG Simplification    : 0.02
% 2.92/1.43  Subsumption          : 0.06
% 2.92/1.43  Abstraction          : 0.02
% 2.92/1.43  MUC search           : 0.00
% 2.92/1.43  Cooper               : 0.00
% 2.92/1.43  Total                : 0.69
% 2.92/1.43  Index Insertion      : 0.00
% 2.92/1.43  Index Deletion       : 0.00
% 2.92/1.43  Index Matching       : 0.00
% 2.92/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
