%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:53 EST 2020

% Result     : Theorem 7.52s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 326 expanded)
%              Number of leaves         :   30 ( 118 expanded)
%              Depth                    :   10
%              Number of atoms          :  175 ( 845 expanded)
%              Number of equality atoms :   65 ( 330 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ~ ( ~ ( A = k1_xboole_0
            & B != k1_xboole_0 )
        & ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ~ ( B = k1_relat_1(C)
                & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_76,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_10384,plain,(
    ! [C_599,A_600,B_601] :
      ( m1_subset_1(C_599,k1_zfmisc_1(k2_zfmisc_1(A_600,B_601)))
      | ~ r1_tarski(k2_relat_1(C_599),B_601)
      | ~ r1_tarski(k1_relat_1(C_599),A_600)
      | ~ v1_relat_1(C_599) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_78,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70])).

tff(c_116,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_2419,plain,(
    ! [C_199,A_200,B_201] :
      ( m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ r1_tarski(k2_relat_1(C_199),B_201)
      | ~ r1_tarski(k1_relat_1(C_199),A_200)
      | ~ v1_relat_1(C_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5753,plain,(
    ! [C_316,A_317,B_318] :
      ( r1_tarski(C_316,k2_zfmisc_1(A_317,B_318))
      | ~ r1_tarski(k2_relat_1(C_316),B_318)
      | ~ r1_tarski(k1_relat_1(C_316),A_317)
      | ~ v1_relat_1(C_316) ) ),
    inference(resolution,[status(thm)],[c_2419,c_18])).

tff(c_5809,plain,(
    ! [A_317] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_317,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_317)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_72,c_5753])).

tff(c_5862,plain,(
    ! [A_319] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_319,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_319) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5809])).

tff(c_5901,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_5862])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1109,plain,(
    ! [A_121,B_122,C_123] :
      ( k1_relset_1(A_121,B_122,C_123) = k1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1120,plain,(
    ! [A_121,B_122,A_10] :
      ( k1_relset_1(A_121,B_122,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_121,B_122)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1109])).

tff(c_5920,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5901,c_1120])).

tff(c_2934,plain,(
    ! [B_220,C_221,A_222] :
      ( k1_xboole_0 = B_220
      | v1_funct_2(C_221,A_222,B_220)
      | k1_relset_1(A_222,B_220,C_221) != A_222
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_222,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6801,plain,(
    ! [B_342,A_343,A_344] :
      ( k1_xboole_0 = B_342
      | v1_funct_2(A_343,A_344,B_342)
      | k1_relset_1(A_344,B_342,A_343) != A_344
      | ~ r1_tarski(A_343,k2_zfmisc_1(A_344,B_342)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2934])).

tff(c_6813,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5901,c_6801])).

tff(c_6859,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5920,c_6813])).

tff(c_6860,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_6859])).

tff(c_140,plain,(
    ! [A_50] :
      ( k2_relat_1(A_50) != k1_xboole_0
      | k1_xboole_0 = A_50
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_163,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_76,c_140])).

tff(c_164,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_165,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(A_51,B_52) = B_52
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_176,plain,(
    k2_xboole_0(k2_relat_1('#skF_3'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_72,c_165])).

tff(c_316,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_tarski(A_63,C_64)
      | ~ r1_tarski(k2_xboole_0(A_63,B_65),C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_357,plain,(
    ! [C_68] :
      ( r1_tarski(k2_relat_1('#skF_3'),C_68)
      | ~ r1_tarski('#skF_2',C_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_316])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    ! [A_21] : k1_relat_1('#skF_1'(A_21,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_50,plain,(
    ! [A_21] : v1_relat_1('#skF_1'(A_21,k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_211,plain,(
    ! [A_56] :
      ( k1_relat_1(A_56) != k1_xboole_0
      | k1_xboole_0 = A_56
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_223,plain,(
    ! [A_21] :
      ( k1_relat_1('#skF_1'(A_21,k1_xboole_0)) != k1_xboole_0
      | '#skF_1'(A_21,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_211])).

tff(c_235,plain,(
    ! [A_21] : '#skF_1'(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_223])).

tff(c_38,plain,(
    ! [A_21] : r1_tarski(k2_relat_1('#skF_1'(A_21,k1_xboole_0)),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_238,plain,(
    ! [A_21] : r1_tarski(k2_relat_1(k1_xboole_0),A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_38])).

tff(c_242,plain,(
    ! [A_21] : r1_tarski(k1_xboole_0,A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_238])).

tff(c_269,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_276,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_242,c_269])).

tff(c_361,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_357,c_276])).

tff(c_369,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_361])).

tff(c_6930,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6860,c_369])).

tff(c_6950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6930])).

tff(c_6951,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6964,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6951,c_6951,c_32])).

tff(c_14,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_30,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_82,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_58])).

tff(c_7419,plain,(
    ! [A_30] :
      ( v1_funct_2('#skF_3',A_30,'#skF_3')
      | A_30 = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6951,c_6951,c_6951,c_6951,c_6951,c_82])).

tff(c_7420,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7419])).

tff(c_7423,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_7420])).

tff(c_7427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7423])).

tff(c_7429,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7419])).

tff(c_16,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6960,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_3',B_9) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6951,c_6951,c_16])).

tff(c_7349,plain,(
    ! [A_387,B_388,C_389] :
      ( k1_relset_1(A_387,B_388,C_389) = k1_relat_1(C_389)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(A_387,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7923,plain,(
    ! [B_430,C_431] :
      ( k1_relset_1('#skF_3',B_430,C_431) = k1_relat_1(C_431)
      | ~ m1_subset_1(C_431,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6960,c_7349])).

tff(c_7925,plain,(
    ! [B_430] : k1_relset_1('#skF_3',B_430,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7429,c_7923])).

tff(c_7930,plain,(
    ! [B_430] : k1_relset_1('#skF_3',B_430,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6964,c_7925])).

tff(c_62,plain,(
    ! [C_32,B_31] :
      ( v1_funct_2(C_32,k1_xboole_0,B_31)
      | k1_relset_1(k1_xboole_0,B_31,C_32) != k1_xboole_0
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_79,plain,(
    ! [C_32,B_31] :
      ( v1_funct_2(C_32,k1_xboole_0,B_31)
      | k1_relset_1(k1_xboole_0,B_31,C_32) != k1_xboole_0
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_62])).

tff(c_8293,plain,(
    ! [C_451,B_452] :
      ( v1_funct_2(C_451,'#skF_3',B_452)
      | k1_relset_1('#skF_3',B_452,C_451) != '#skF_3'
      | ~ m1_subset_1(C_451,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6951,c_6951,c_6951,c_6951,c_79])).

tff(c_8295,plain,(
    ! [B_452] :
      ( v1_funct_2('#skF_3','#skF_3',B_452)
      | k1_relset_1('#skF_3',B_452,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_7429,c_8293])).

tff(c_8301,plain,(
    ! [B_452] : v1_funct_2('#skF_3','#skF_3',B_452) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7930,c_8295])).

tff(c_6977,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6964,c_116])).

tff(c_8305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8301,c_6977])).

tff(c_8306,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_10393,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10384,c_8306])).

tff(c_10410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6,c_72,c_10393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:27:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.52/2.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.52/2.76  
% 7.52/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.52/2.76  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.52/2.76  
% 7.52/2.76  %Foreground sorts:
% 7.52/2.76  
% 7.52/2.76  
% 7.52/2.76  %Background operators:
% 7.52/2.76  
% 7.52/2.76  
% 7.52/2.76  %Foreground operators:
% 7.52/2.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.52/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.52/2.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.52/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.52/2.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.52/2.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.52/2.76  tff('#skF_2', type, '#skF_2': $i).
% 7.52/2.76  tff('#skF_3', type, '#skF_3': $i).
% 7.52/2.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.52/2.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.52/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.52/2.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.52/2.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.52/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.52/2.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.52/2.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.52/2.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.52/2.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.52/2.76  
% 7.85/2.78  tff(f_140, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 7.85/2.78  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.85/2.78  tff(f_109, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 7.85/2.78  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.85/2.78  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.85/2.78  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.85/2.78  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.85/2.78  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.85/2.78  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.85/2.78  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 7.85/2.78  tff(f_97, axiom, (![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 7.85/2.78  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.85/2.78  tff(c_76, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.85/2.78  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.85/2.78  tff(c_72, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.85/2.78  tff(c_10384, plain, (![C_599, A_600, B_601]: (m1_subset_1(C_599, k1_zfmisc_1(k2_zfmisc_1(A_600, B_601))) | ~r1_tarski(k2_relat_1(C_599), B_601) | ~r1_tarski(k1_relat_1(C_599), A_600) | ~v1_relat_1(C_599))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.85/2.78  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.85/2.78  tff(c_70, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.85/2.78  tff(c_78, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70])).
% 7.85/2.78  tff(c_116, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_78])).
% 7.85/2.78  tff(c_2419, plain, (![C_199, A_200, B_201]: (m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~r1_tarski(k2_relat_1(C_199), B_201) | ~r1_tarski(k1_relat_1(C_199), A_200) | ~v1_relat_1(C_199))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.85/2.78  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.85/2.78  tff(c_5753, plain, (![C_316, A_317, B_318]: (r1_tarski(C_316, k2_zfmisc_1(A_317, B_318)) | ~r1_tarski(k2_relat_1(C_316), B_318) | ~r1_tarski(k1_relat_1(C_316), A_317) | ~v1_relat_1(C_316))), inference(resolution, [status(thm)], [c_2419, c_18])).
% 7.85/2.78  tff(c_5809, plain, (![A_317]: (r1_tarski('#skF_3', k2_zfmisc_1(A_317, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_317) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_72, c_5753])).
% 7.85/2.78  tff(c_5862, plain, (![A_319]: (r1_tarski('#skF_3', k2_zfmisc_1(A_319, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_319))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5809])).
% 7.85/2.78  tff(c_5901, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_5862])).
% 7.85/2.78  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.85/2.78  tff(c_1109, plain, (![A_121, B_122, C_123]: (k1_relset_1(A_121, B_122, C_123)=k1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.85/2.78  tff(c_1120, plain, (![A_121, B_122, A_10]: (k1_relset_1(A_121, B_122, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_121, B_122)))), inference(resolution, [status(thm)], [c_20, c_1109])).
% 7.85/2.78  tff(c_5920, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5901, c_1120])).
% 7.85/2.78  tff(c_2934, plain, (![B_220, C_221, A_222]: (k1_xboole_0=B_220 | v1_funct_2(C_221, A_222, B_220) | k1_relset_1(A_222, B_220, C_221)!=A_222 | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_222, B_220))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.85/2.78  tff(c_6801, plain, (![B_342, A_343, A_344]: (k1_xboole_0=B_342 | v1_funct_2(A_343, A_344, B_342) | k1_relset_1(A_344, B_342, A_343)!=A_344 | ~r1_tarski(A_343, k2_zfmisc_1(A_344, B_342)))), inference(resolution, [status(thm)], [c_20, c_2934])).
% 7.85/2.78  tff(c_6813, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5901, c_6801])).
% 7.85/2.78  tff(c_6859, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5920, c_6813])).
% 7.85/2.78  tff(c_6860, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_116, c_6859])).
% 7.85/2.78  tff(c_140, plain, (![A_50]: (k2_relat_1(A_50)!=k1_xboole_0 | k1_xboole_0=A_50 | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.85/2.78  tff(c_163, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_76, c_140])).
% 7.85/2.78  tff(c_164, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_163])).
% 7.85/2.78  tff(c_165, plain, (![A_51, B_52]: (k2_xboole_0(A_51, B_52)=B_52 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.85/2.78  tff(c_176, plain, (k2_xboole_0(k2_relat_1('#skF_3'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_72, c_165])).
% 7.85/2.78  tff(c_316, plain, (![A_63, C_64, B_65]: (r1_tarski(A_63, C_64) | ~r1_tarski(k2_xboole_0(A_63, B_65), C_64))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.85/2.78  tff(c_357, plain, (![C_68]: (r1_tarski(k2_relat_1('#skF_3'), C_68) | ~r1_tarski('#skF_2', C_68))), inference(superposition, [status(thm), theory('equality')], [c_176, c_316])).
% 7.85/2.78  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.85/2.78  tff(c_42, plain, (![A_21]: (k1_relat_1('#skF_1'(A_21, k1_xboole_0))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.85/2.78  tff(c_50, plain, (![A_21]: (v1_relat_1('#skF_1'(A_21, k1_xboole_0)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.85/2.78  tff(c_211, plain, (![A_56]: (k1_relat_1(A_56)!=k1_xboole_0 | k1_xboole_0=A_56 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.85/2.78  tff(c_223, plain, (![A_21]: (k1_relat_1('#skF_1'(A_21, k1_xboole_0))!=k1_xboole_0 | '#skF_1'(A_21, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_211])).
% 7.85/2.78  tff(c_235, plain, (![A_21]: ('#skF_1'(A_21, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_223])).
% 7.85/2.78  tff(c_38, plain, (![A_21]: (r1_tarski(k2_relat_1('#skF_1'(A_21, k1_xboole_0)), A_21))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.85/2.78  tff(c_238, plain, (![A_21]: (r1_tarski(k2_relat_1(k1_xboole_0), A_21))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_38])).
% 7.85/2.78  tff(c_242, plain, (![A_21]: (r1_tarski(k1_xboole_0, A_21))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_238])).
% 7.85/2.78  tff(c_269, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.85/2.78  tff(c_276, plain, (![A_21]: (k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_xboole_0))), inference(resolution, [status(thm)], [c_242, c_269])).
% 7.85/2.78  tff(c_361, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_357, c_276])).
% 7.85/2.78  tff(c_369, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_164, c_361])).
% 7.85/2.78  tff(c_6930, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6860, c_369])).
% 7.85/2.78  tff(c_6950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_6930])).
% 7.85/2.78  tff(c_6951, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_163])).
% 7.85/2.78  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.85/2.78  tff(c_6964, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6951, c_6951, c_32])).
% 7.85/2.78  tff(c_14, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.85/2.78  tff(c_58, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_30, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.85/2.78  tff(c_82, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_58])).
% 7.85/2.78  tff(c_7419, plain, (![A_30]: (v1_funct_2('#skF_3', A_30, '#skF_3') | A_30='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6951, c_6951, c_6951, c_6951, c_6951, c_82])).
% 7.85/2.78  tff(c_7420, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_7419])).
% 7.85/2.78  tff(c_7423, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_7420])).
% 7.85/2.78  tff(c_7427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_7423])).
% 7.85/2.78  tff(c_7429, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_7419])).
% 7.85/2.78  tff(c_16, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.85/2.78  tff(c_6960, plain, (![B_9]: (k2_zfmisc_1('#skF_3', B_9)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6951, c_6951, c_16])).
% 7.85/2.78  tff(c_7349, plain, (![A_387, B_388, C_389]: (k1_relset_1(A_387, B_388, C_389)=k1_relat_1(C_389) | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(A_387, B_388))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.85/2.78  tff(c_7923, plain, (![B_430, C_431]: (k1_relset_1('#skF_3', B_430, C_431)=k1_relat_1(C_431) | ~m1_subset_1(C_431, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6960, c_7349])).
% 7.85/2.78  tff(c_7925, plain, (![B_430]: (k1_relset_1('#skF_3', B_430, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_7429, c_7923])).
% 7.85/2.78  tff(c_7930, plain, (![B_430]: (k1_relset_1('#skF_3', B_430, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6964, c_7925])).
% 7.85/2.78  tff(c_62, plain, (![C_32, B_31]: (v1_funct_2(C_32, k1_xboole_0, B_31) | k1_relset_1(k1_xboole_0, B_31, C_32)!=k1_xboole_0 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_31))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.85/2.78  tff(c_79, plain, (![C_32, B_31]: (v1_funct_2(C_32, k1_xboole_0, B_31) | k1_relset_1(k1_xboole_0, B_31, C_32)!=k1_xboole_0 | ~m1_subset_1(C_32, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_62])).
% 7.85/2.78  tff(c_8293, plain, (![C_451, B_452]: (v1_funct_2(C_451, '#skF_3', B_452) | k1_relset_1('#skF_3', B_452, C_451)!='#skF_3' | ~m1_subset_1(C_451, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6951, c_6951, c_6951, c_6951, c_79])).
% 7.85/2.78  tff(c_8295, plain, (![B_452]: (v1_funct_2('#skF_3', '#skF_3', B_452) | k1_relset_1('#skF_3', B_452, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_7429, c_8293])).
% 7.85/2.78  tff(c_8301, plain, (![B_452]: (v1_funct_2('#skF_3', '#skF_3', B_452))), inference(demodulation, [status(thm), theory('equality')], [c_7930, c_8295])).
% 7.85/2.78  tff(c_6977, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6964, c_116])).
% 7.85/2.78  tff(c_8305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8301, c_6977])).
% 7.85/2.78  tff(c_8306, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_78])).
% 7.85/2.78  tff(c_10393, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10384, c_8306])).
% 7.85/2.78  tff(c_10410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_6, c_72, c_10393])).
% 7.85/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/2.78  
% 7.85/2.78  Inference rules
% 7.85/2.78  ----------------------
% 7.85/2.78  #Ref     : 0
% 7.85/2.78  #Sup     : 2407
% 7.85/2.78  #Fact    : 0
% 7.85/2.78  #Define  : 0
% 7.85/2.78  #Split   : 22
% 7.85/2.78  #Chain   : 0
% 7.85/2.78  #Close   : 0
% 7.85/2.78  
% 7.85/2.78  Ordering : KBO
% 7.85/2.78  
% 7.85/2.78  Simplification rules
% 7.85/2.78  ----------------------
% 7.85/2.78  #Subsume      : 695
% 7.85/2.78  #Demod        : 1414
% 7.85/2.78  #Tautology    : 874
% 7.85/2.78  #SimpNegUnit  : 64
% 7.85/2.78  #BackRed      : 174
% 7.85/2.78  
% 7.85/2.78  #Partial instantiations: 0
% 7.85/2.78  #Strategies tried      : 1
% 7.85/2.78  
% 7.85/2.78  Timing (in seconds)
% 7.85/2.78  ----------------------
% 7.85/2.79  Preprocessing        : 0.33
% 7.85/2.79  Parsing              : 0.17
% 7.85/2.79  CNF conversion       : 0.02
% 7.85/2.79  Main loop            : 1.64
% 7.89/2.79  Inferencing          : 0.49
% 7.89/2.79  Reduction            : 0.58
% 7.89/2.79  Demodulation         : 0.43
% 7.89/2.79  BG Simplification    : 0.06
% 7.89/2.79  Subsumption          : 0.40
% 7.89/2.79  Abstraction          : 0.07
% 7.89/2.79  MUC search           : 0.00
% 7.89/2.79  Cooper               : 0.00
% 7.89/2.79  Total                : 2.01
% 7.89/2.79  Index Insertion      : 0.00
% 7.89/2.79  Index Deletion       : 0.00
% 7.89/2.79  Index Matching       : 0.00
% 7.89/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
