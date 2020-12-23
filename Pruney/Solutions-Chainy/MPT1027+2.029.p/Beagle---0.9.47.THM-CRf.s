%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:46 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   94 (1504 expanded)
%              Number of leaves         :   21 ( 466 expanded)
%              Depth                    :   14
%              Number of atoms          :  149 (3694 expanded)
%              Number of equality atoms :   71 (1666 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_67,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34])).

tff(c_36,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_189,plain,(
    ! [B_47,C_48,A_49] :
      ( k1_xboole_0 = B_47
      | v1_funct_2(C_48,A_49,B_47)
      | k1_relset_1(A_49,B_47,C_48) != A_49
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_196,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_189])).

tff(c_210,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_196])).

tff(c_211,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_210])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_223,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_91])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_225,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_211,c_10])).

tff(c_90,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_104,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_104])).

tff(c_142,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_258,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_142])).

tff(c_264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_258])).

tff(c_265,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_269,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_38])).

tff(c_327,plain,(
    ! [B_66,A_67,C_68] :
      ( k1_xboole_0 = B_66
      | k1_relset_1(A_67,B_66,C_68) = A_67
      | ~ v1_funct_2(C_68,A_67,B_66)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_330,plain,(
    ! [C_68] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_68) = '#skF_1'
      | ~ v1_funct_2(C_68,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_68,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_327])).

tff(c_373,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_274,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_8])).

tff(c_295,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_380,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_295])).

tff(c_398,plain,(
    ! [A_74] : k2_zfmisc_1(A_74,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_373,c_10])).

tff(c_402,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_265])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_380,c_402])).

tff(c_411,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_428,plain,(
    ! [B_76,C_77,A_78] :
      ( k1_xboole_0 = B_76
      | v1_funct_2(C_77,A_78,B_76)
      | k1_relset_1(A_78,B_76,C_77) != A_78
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_431,plain,(
    ! [C_77] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_77,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_77) != '#skF_1'
      | ~ m1_subset_1(C_77,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_428])).

tff(c_475,plain,(
    ! [C_81] :
      ( v1_funct_2(C_81,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_81) != '#skF_1'
      | ~ m1_subset_1(C_81,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_431])).

tff(c_478,plain,
    ( v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_269,c_475])).

tff(c_489,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_478])).

tff(c_491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_489])).

tff(c_493,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_22,plain,(
    ! [A_11] :
      ( v1_funct_2(k1_xboole_0,A_11,k1_xboole_0)
      | k1_xboole_0 = A_11
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_11,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44,plain,(
    ! [A_11] :
      ( v1_funct_2(k1_xboole_0,A_11,k1_xboole_0)
      | k1_xboole_0 = A_11 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_572,plain,(
    ! [A_89] :
      ( v1_funct_2('#skF_3',A_89,'#skF_3')
      | A_89 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_493,c_493,c_44])).

tff(c_492,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_521,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_493,c_492])).

tff(c_522,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_521])).

tff(c_525,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_42])).

tff(c_579,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_572,c_525])).

tff(c_524,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_36])).

tff(c_587,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_579,c_524])).

tff(c_594,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_493])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [C_13,B_12] :
      ( v1_funct_2(C_13,k1_xboole_0,B_12)
      | k1_relset_1(k1_xboole_0,B_12,C_13) != k1_xboole_0
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_601,plain,(
    ! [C_90,B_91] :
      ( v1_funct_2(C_90,k1_xboole_0,B_91)
      | k1_relset_1(k1_xboole_0,B_91,C_90) != k1_xboole_0
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_605,plain,(
    ! [A_6,B_91] :
      ( v1_funct_2(A_6,k1_xboole_0,B_91)
      | k1_relset_1(k1_xboole_0,B_91,A_6) != k1_xboole_0
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_601])).

tff(c_746,plain,(
    ! [A_115,B_116] :
      ( v1_funct_2(A_115,'#skF_1',B_116)
      | k1_relset_1('#skF_1',B_116,A_115) != '#skF_1'
      | ~ r1_tarski(A_115,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_594,c_594,c_594,c_605])).

tff(c_586,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_579,c_525])).

tff(c_753,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_746,c_586])).

tff(c_760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_587,c_753])).

tff(c_761,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_521])).

tff(c_768,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_36])).

tff(c_502,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_14])).

tff(c_763,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_502])).

tff(c_765,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_493])).

tff(c_45,plain,(
    ! [C_13,B_12] :
      ( v1_funct_2(C_13,k1_xboole_0,B_12)
      | k1_relset_1(k1_xboole_0,B_12,C_13) != k1_xboole_0
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_794,plain,(
    ! [C_119,B_120] :
      ( v1_funct_2(C_119,'#skF_1',B_120)
      | k1_relset_1('#skF_1',B_120,C_119) != '#skF_1'
      | ~ m1_subset_1(C_119,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_765,c_765,c_765,c_45])).

tff(c_894,plain,(
    ! [B_138] :
      ( v1_funct_2('#skF_1','#skF_1',B_138)
      | k1_relset_1('#skF_1',B_138,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_763,c_794])).

tff(c_769,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_42])).

tff(c_899,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_894,c_769])).

tff(c_906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:44:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.46  
% 2.61/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.47  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.99/1.47  
% 2.99/1.47  %Foreground sorts:
% 2.99/1.47  
% 2.99/1.47  
% 2.99/1.47  %Background operators:
% 2.99/1.47  
% 2.99/1.47  
% 2.99/1.47  %Foreground operators:
% 2.99/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.99/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.99/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.47  
% 2.99/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.99/1.48  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 2.99/1.48  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.99/1.48  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.99/1.48  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.99/1.48  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.99/1.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.48  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.48  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.48  tff(c_34, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.48  tff(c_42, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34])).
% 2.99/1.48  tff(c_36, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.48  tff(c_189, plain, (![B_47, C_48, A_49]: (k1_xboole_0=B_47 | v1_funct_2(C_48, A_49, B_47) | k1_relset_1(A_49, B_47, C_48)!=A_49 | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_47))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.48  tff(c_196, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_38, c_189])).
% 2.99/1.48  tff(c_210, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_196])).
% 2.99/1.48  tff(c_211, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_210])).
% 2.99/1.48  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.99/1.48  tff(c_79, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.99/1.48  tff(c_91, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_79])).
% 2.99/1.48  tff(c_223, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_91])).
% 2.99/1.48  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.48  tff(c_225, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_211, c_10])).
% 2.99/1.48  tff(c_90, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_79])).
% 2.99/1.48  tff(c_104, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.48  tff(c_111, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_90, c_104])).
% 2.99/1.48  tff(c_142, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_111])).
% 2.99/1.48  tff(c_258, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_142])).
% 2.99/1.48  tff(c_264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_258])).
% 2.99/1.48  tff(c_265, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_111])).
% 2.99/1.48  tff(c_269, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_38])).
% 2.99/1.48  tff(c_327, plain, (![B_66, A_67, C_68]: (k1_xboole_0=B_66 | k1_relset_1(A_67, B_66, C_68)=A_67 | ~v1_funct_2(C_68, A_67, B_66) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.48  tff(c_330, plain, (![C_68]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_68)='#skF_1' | ~v1_funct_2(C_68, '#skF_1', '#skF_2') | ~m1_subset_1(C_68, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_265, c_327])).
% 2.99/1.48  tff(c_373, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_330])).
% 2.99/1.48  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.48  tff(c_274, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_265, c_8])).
% 2.99/1.48  tff(c_295, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_274])).
% 2.99/1.48  tff(c_380, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_373, c_295])).
% 2.99/1.48  tff(c_398, plain, (![A_74]: (k2_zfmisc_1(A_74, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_373, c_373, c_10])).
% 2.99/1.48  tff(c_402, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_398, c_265])).
% 2.99/1.48  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_380, c_402])).
% 2.99/1.48  tff(c_411, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_330])).
% 2.99/1.48  tff(c_428, plain, (![B_76, C_77, A_78]: (k1_xboole_0=B_76 | v1_funct_2(C_77, A_78, B_76) | k1_relset_1(A_78, B_76, C_77)!=A_78 | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_76))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.48  tff(c_431, plain, (![C_77]: (k1_xboole_0='#skF_2' | v1_funct_2(C_77, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_77)!='#skF_1' | ~m1_subset_1(C_77, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_265, c_428])).
% 2.99/1.48  tff(c_475, plain, (![C_81]: (v1_funct_2(C_81, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_81)!='#skF_1' | ~m1_subset_1(C_81, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_411, c_431])).
% 2.99/1.48  tff(c_478, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_269, c_475])).
% 2.99/1.48  tff(c_489, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_478])).
% 2.99/1.48  tff(c_491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_489])).
% 2.99/1.48  tff(c_493, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_274])).
% 2.99/1.48  tff(c_22, plain, (![A_11]: (v1_funct_2(k1_xboole_0, A_11, k1_xboole_0) | k1_xboole_0=A_11 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_11, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.48  tff(c_44, plain, (![A_11]: (v1_funct_2(k1_xboole_0, A_11, k1_xboole_0) | k1_xboole_0=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22])).
% 2.99/1.48  tff(c_572, plain, (![A_89]: (v1_funct_2('#skF_3', A_89, '#skF_3') | A_89='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_493, c_493, c_44])).
% 2.99/1.48  tff(c_492, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_274])).
% 2.99/1.48  tff(c_521, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_493, c_493, c_492])).
% 2.99/1.48  tff(c_522, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_521])).
% 2.99/1.48  tff(c_525, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_522, c_42])).
% 2.99/1.48  tff(c_579, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_572, c_525])).
% 2.99/1.48  tff(c_524, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_522, c_36])).
% 2.99/1.48  tff(c_587, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_579, c_524])).
% 2.99/1.48  tff(c_594, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_493])).
% 2.99/1.48  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.99/1.48  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.48  tff(c_26, plain, (![C_13, B_12]: (v1_funct_2(C_13, k1_xboole_0, B_12) | k1_relset_1(k1_xboole_0, B_12, C_13)!=k1_xboole_0 | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_12))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.48  tff(c_601, plain, (![C_90, B_91]: (v1_funct_2(C_90, k1_xboole_0, B_91) | k1_relset_1(k1_xboole_0, B_91, C_90)!=k1_xboole_0 | ~m1_subset_1(C_90, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 2.99/1.48  tff(c_605, plain, (![A_6, B_91]: (v1_funct_2(A_6, k1_xboole_0, B_91) | k1_relset_1(k1_xboole_0, B_91, A_6)!=k1_xboole_0 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_601])).
% 2.99/1.48  tff(c_746, plain, (![A_115, B_116]: (v1_funct_2(A_115, '#skF_1', B_116) | k1_relset_1('#skF_1', B_116, A_115)!='#skF_1' | ~r1_tarski(A_115, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_594, c_594, c_594, c_594, c_605])).
% 2.99/1.48  tff(c_586, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_579, c_579, c_525])).
% 2.99/1.48  tff(c_753, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_746, c_586])).
% 2.99/1.48  tff(c_760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_587, c_753])).
% 2.99/1.48  tff(c_761, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_521])).
% 2.99/1.48  tff(c_768, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_761, c_36])).
% 2.99/1.48  tff(c_502, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_14])).
% 2.99/1.48  tff(c_763, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_761, c_502])).
% 2.99/1.48  tff(c_765, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_761, c_493])).
% 2.99/1.49  tff(c_45, plain, (![C_13, B_12]: (v1_funct_2(C_13, k1_xboole_0, B_12) | k1_relset_1(k1_xboole_0, B_12, C_13)!=k1_xboole_0 | ~m1_subset_1(C_13, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 2.99/1.49  tff(c_794, plain, (![C_119, B_120]: (v1_funct_2(C_119, '#skF_1', B_120) | k1_relset_1('#skF_1', B_120, C_119)!='#skF_1' | ~m1_subset_1(C_119, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_765, c_765, c_765, c_765, c_45])).
% 2.99/1.49  tff(c_894, plain, (![B_138]: (v1_funct_2('#skF_1', '#skF_1', B_138) | k1_relset_1('#skF_1', B_138, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_763, c_794])).
% 2.99/1.49  tff(c_769, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_761, c_42])).
% 2.99/1.49  tff(c_899, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_894, c_769])).
% 2.99/1.49  tff(c_906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_768, c_899])).
% 2.99/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.49  
% 2.99/1.49  Inference rules
% 2.99/1.49  ----------------------
% 2.99/1.49  #Ref     : 0
% 2.99/1.49  #Sup     : 168
% 2.99/1.49  #Fact    : 0
% 2.99/1.49  #Define  : 0
% 2.99/1.49  #Split   : 5
% 2.99/1.49  #Chain   : 0
% 2.99/1.49  #Close   : 0
% 2.99/1.49  
% 2.99/1.49  Ordering : KBO
% 2.99/1.49  
% 2.99/1.49  Simplification rules
% 2.99/1.49  ----------------------
% 2.99/1.49  #Subsume      : 19
% 2.99/1.49  #Demod        : 230
% 2.99/1.49  #Tautology    : 111
% 2.99/1.49  #SimpNegUnit  : 5
% 2.99/1.49  #BackRed      : 71
% 2.99/1.49  
% 2.99/1.49  #Partial instantiations: 0
% 2.99/1.49  #Strategies tried      : 1
% 2.99/1.49  
% 2.99/1.49  Timing (in seconds)
% 2.99/1.49  ----------------------
% 2.99/1.49  Preprocessing        : 0.29
% 2.99/1.49  Parsing              : 0.16
% 2.99/1.49  CNF conversion       : 0.02
% 2.99/1.49  Main loop            : 0.42
% 2.99/1.49  Inferencing          : 0.15
% 2.99/1.49  Reduction            : 0.13
% 2.99/1.49  Demodulation         : 0.09
% 2.99/1.49  BG Simplification    : 0.02
% 2.99/1.49  Subsumption          : 0.09
% 2.99/1.49  Abstraction          : 0.02
% 2.99/1.49  MUC search           : 0.00
% 2.99/1.49  Cooper               : 0.00
% 2.99/1.49  Total                : 0.75
% 2.99/1.49  Index Insertion      : 0.00
% 2.99/1.49  Index Deletion       : 0.00
% 2.99/1.49  Index Matching       : 0.00
% 2.99/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
