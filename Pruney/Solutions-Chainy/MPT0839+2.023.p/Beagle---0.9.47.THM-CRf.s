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
% DateTime   : Thu Dec  3 10:08:24 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 394 expanded)
%              Number of leaves         :   34 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  151 ( 876 expanded)
%              Number of equality atoms :   44 ( 190 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_172,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_176,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_172])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_10] :
      ( v1_xboole_0(k2_relat_1(A_10))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_41] :
      ( v1_xboole_0(k2_relat_1(A_41))
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [A_42] :
      ( k2_relat_1(A_42) = k1_xboole_0
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_64,plain,(
    ! [A_43] :
      ( k2_relat_1(k2_relat_1(A_43)) = k1_xboole_0
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_73,plain,(
    ! [A_43] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_43))
      | ~ v1_xboole_0(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_20])).

tff(c_92,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(k2_relat_1(A_45))
      | ~ v1_xboole_0(A_45) ) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_99,plain,(
    ! [A_10] : ~ v1_xboole_0(A_10) ),
    inference(resolution,[status(thm)],[c_20,c_92])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( ~ r1_xboole_0(B_6,A_5)
      | ~ r1_tarski(B_6,A_5)
      | v1_xboole_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_117,plain,(
    ! [B_53,A_54] :
      ( ~ r1_xboole_0(B_53,A_54)
      | ~ r1_tarski(B_53,A_54) ) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_14])).

tff(c_120,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_117])).

tff(c_124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_120])).

tff(c_125,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_160,plain,(
    ! [A_59,B_60] :
      ( v1_xboole_0(k7_relat_1(A_59,B_60))
      | ~ v1_xboole_0(B_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_185,plain,(
    ! [A_67,B_68] :
      ( k7_relat_1(A_67,B_68) = k1_xboole_0
      | ~ v1_xboole_0(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_195,plain,(
    ! [A_69] :
      ( k7_relat_1(A_69,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_125,c_185])).

tff(c_202,plain,(
    k7_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_176,c_195])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1('#skF_1'(A_7,B_8),A_7)
      | k1_xboole_0 = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),B_8)
      | k1_xboole_0 = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_366,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_375,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_366])).

tff(c_36,plain,(
    ! [D_37] :
      ( ~ r2_hidden(D_37,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_37,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_381,plain,(
    ! [D_85] :
      ( ~ r2_hidden(D_85,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(D_85,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_36])).

tff(c_386,plain,(
    ! [A_7] :
      ( ~ m1_subset_1('#skF_1'(A_7,k1_relat_1('#skF_4')),'#skF_3')
      | k1_relat_1('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_16,c_381])).

tff(c_388,plain,(
    ! [A_86] :
      ( ~ m1_subset_1('#skF_1'(A_86,k1_relat_1('#skF_4')),'#skF_3')
      | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_86)) ) ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_393,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_388])).

tff(c_394,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_410,plain,(
    ! [A_90,B_91,C_92] :
      ( m1_subset_1(k1_relset_1(A_90,B_91,C_92),k1_zfmisc_1(A_90))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_425,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_410])).

tff(c_430,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_425])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_394,c_430])).

tff(c_433,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_26,plain,(
    ! [A_13] :
      ( k7_relat_1(A_13,k1_relat_1(A_13)) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_447,plain,
    ( k7_relat_1('#skF_4',k1_xboole_0) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_26])).

tff(c_455,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_202,c_447])).

tff(c_38,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_484,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_38])).

tff(c_58,plain,(
    ! [A_41] :
      ( k2_relat_1(A_41) = k1_xboole_0
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_246,plain,(
    ! [A_73,B_74] :
      ( k2_relat_1(k7_relat_1(A_73,B_74)) = k1_xboole_0
      | ~ v1_xboole_0(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_160,c_58])).

tff(c_267,plain,(
    ! [A_13] :
      ( k2_relat_1(A_13) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(A_13))
      | ~ v1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_246])).

tff(c_441,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_267])).

tff(c_451,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_176,c_125,c_441])).

tff(c_495,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_451])).

tff(c_526,plain,(
    ! [A_93,B_94,C_95] :
      ( k2_relset_1(A_93,B_94,C_95) = k2_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_529,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_526])).

tff(c_531,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_529])).

tff(c_533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_484,c_531])).

tff(c_534,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_169,plain,(
    ! [A_13] :
      ( v1_xboole_0(A_13)
      | ~ v1_xboole_0(k1_relat_1(A_13))
      | ~ v1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_160])).

tff(c_543,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_169])).

tff(c_552,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_176,c_125,c_543])).

tff(c_566,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_552,c_2])).

tff(c_583,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_38])).

tff(c_132,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_125,c_58])).

tff(c_579,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_566,c_132])).

tff(c_624,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_627,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_624])).

tff(c_629,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_627])).

tff(c_631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_583,c_629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:35:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.36  
% 2.55/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.55/1.37  
% 2.55/1.37  %Foreground sorts:
% 2.55/1.37  
% 2.55/1.37  
% 2.55/1.37  %Background operators:
% 2.55/1.37  
% 2.55/1.37  
% 2.55/1.37  %Foreground operators:
% 2.55/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.55/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.55/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.55/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.55/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.55/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.37  
% 2.55/1.38  tff(f_120, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.55/1.38  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.55/1.38  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.55/1.38  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.55/1.38  tff(f_71, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 2.55/1.38  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.55/1.38  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.55/1.38  tff(f_79, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_relat_1)).
% 2.55/1.38  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 2.55/1.38  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.55/1.38  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.55/1.38  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.55/1.38  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.55/1.38  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.55/1.38  tff(c_172, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.55/1.38  tff(c_176, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_172])).
% 2.55/1.38  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.55/1.38  tff(c_10, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.55/1.38  tff(c_20, plain, (![A_10]: (v1_xboole_0(k2_relat_1(A_10)) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.55/1.38  tff(c_54, plain, (![A_41]: (v1_xboole_0(k2_relat_1(A_41)) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.55/1.38  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.38  tff(c_59, plain, (![A_42]: (k2_relat_1(A_42)=k1_xboole_0 | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_54, c_2])).
% 2.55/1.38  tff(c_64, plain, (![A_43]: (k2_relat_1(k2_relat_1(A_43))=k1_xboole_0 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_20, c_59])).
% 2.55/1.38  tff(c_73, plain, (![A_43]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_43)) | ~v1_xboole_0(A_43))), inference(superposition, [status(thm), theory('equality')], [c_64, c_20])).
% 2.55/1.38  tff(c_92, plain, (![A_45]: (~v1_xboole_0(k2_relat_1(A_45)) | ~v1_xboole_0(A_45))), inference(splitLeft, [status(thm)], [c_73])).
% 2.55/1.38  tff(c_99, plain, (![A_10]: (~v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_20, c_92])).
% 2.55/1.38  tff(c_14, plain, (![B_6, A_5]: (~r1_xboole_0(B_6, A_5) | ~r1_tarski(B_6, A_5) | v1_xboole_0(B_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.55/1.38  tff(c_117, plain, (![B_53, A_54]: (~r1_xboole_0(B_53, A_54) | ~r1_tarski(B_53, A_54))), inference(negUnitSimplification, [status(thm)], [c_99, c_14])).
% 2.55/1.38  tff(c_120, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_117])).
% 2.55/1.38  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_120])).
% 2.55/1.38  tff(c_125, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_73])).
% 2.55/1.38  tff(c_160, plain, (![A_59, B_60]: (v1_xboole_0(k7_relat_1(A_59, B_60)) | ~v1_xboole_0(B_60) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.55/1.38  tff(c_185, plain, (![A_67, B_68]: (k7_relat_1(A_67, B_68)=k1_xboole_0 | ~v1_xboole_0(B_68) | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_160, c_2])).
% 2.55/1.38  tff(c_195, plain, (![A_69]: (k7_relat_1(A_69, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_125, c_185])).
% 2.55/1.38  tff(c_202, plain, (k7_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_176, c_195])).
% 2.55/1.38  tff(c_18, plain, (![A_7, B_8]: (m1_subset_1('#skF_1'(A_7, B_8), A_7) | k1_xboole_0=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.55/1.38  tff(c_16, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), B_8) | k1_xboole_0=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.55/1.38  tff(c_366, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.55/1.38  tff(c_375, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_366])).
% 2.55/1.38  tff(c_36, plain, (![D_37]: (~r2_hidden(D_37, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_37, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.55/1.38  tff(c_381, plain, (![D_85]: (~r2_hidden(D_85, k1_relat_1('#skF_4')) | ~m1_subset_1(D_85, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_375, c_36])).
% 2.55/1.38  tff(c_386, plain, (![A_7]: (~m1_subset_1('#skF_1'(A_7, k1_relat_1('#skF_4')), '#skF_3') | k1_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_16, c_381])).
% 2.55/1.38  tff(c_388, plain, (![A_86]: (~m1_subset_1('#skF_1'(A_86, k1_relat_1('#skF_4')), '#skF_3') | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(A_86)))), inference(splitLeft, [status(thm)], [c_386])).
% 2.55/1.38  tff(c_393, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_388])).
% 2.55/1.38  tff(c_394, plain, (~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_393])).
% 2.55/1.38  tff(c_410, plain, (![A_90, B_91, C_92]: (m1_subset_1(k1_relset_1(A_90, B_91, C_92), k1_zfmisc_1(A_90)) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.55/1.38  tff(c_425, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_375, c_410])).
% 2.55/1.38  tff(c_430, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_425])).
% 2.55/1.38  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_394, c_430])).
% 2.55/1.38  tff(c_433, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_393])).
% 2.55/1.38  tff(c_26, plain, (![A_13]: (k7_relat_1(A_13, k1_relat_1(A_13))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.55/1.38  tff(c_447, plain, (k7_relat_1('#skF_4', k1_xboole_0)='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_433, c_26])).
% 2.55/1.38  tff(c_455, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_202, c_447])).
% 2.55/1.38  tff(c_38, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.55/1.38  tff(c_484, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_455, c_38])).
% 2.55/1.38  tff(c_58, plain, (![A_41]: (k2_relat_1(A_41)=k1_xboole_0 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_54, c_2])).
% 2.55/1.38  tff(c_246, plain, (![A_73, B_74]: (k2_relat_1(k7_relat_1(A_73, B_74))=k1_xboole_0 | ~v1_xboole_0(B_74) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_160, c_58])).
% 2.55/1.38  tff(c_267, plain, (![A_13]: (k2_relat_1(A_13)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(A_13)) | ~v1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_26, c_246])).
% 2.55/1.38  tff(c_441, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_433, c_267])).
% 2.55/1.38  tff(c_451, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_176, c_176, c_125, c_441])).
% 2.55/1.38  tff(c_495, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_455, c_451])).
% 2.55/1.38  tff(c_526, plain, (![A_93, B_94, C_95]: (k2_relset_1(A_93, B_94, C_95)=k2_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.55/1.38  tff(c_529, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_526])).
% 2.55/1.38  tff(c_531, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_495, c_529])).
% 2.55/1.38  tff(c_533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_484, c_531])).
% 2.55/1.38  tff(c_534, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_386])).
% 2.55/1.38  tff(c_169, plain, (![A_13]: (v1_xboole_0(A_13) | ~v1_xboole_0(k1_relat_1(A_13)) | ~v1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_26, c_160])).
% 2.55/1.38  tff(c_543, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_534, c_169])).
% 2.55/1.38  tff(c_552, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_176, c_125, c_543])).
% 2.55/1.38  tff(c_566, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_552, c_2])).
% 2.55/1.38  tff(c_583, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_566, c_38])).
% 2.55/1.38  tff(c_132, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_125, c_58])).
% 2.55/1.38  tff(c_579, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_566, c_566, c_132])).
% 2.55/1.38  tff(c_624, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.55/1.38  tff(c_627, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_624])).
% 2.55/1.38  tff(c_629, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_627])).
% 2.55/1.38  tff(c_631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_583, c_629])).
% 2.55/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.38  
% 2.55/1.38  Inference rules
% 2.55/1.38  ----------------------
% 2.55/1.38  #Ref     : 0
% 2.55/1.38  #Sup     : 122
% 2.55/1.38  #Fact    : 0
% 2.55/1.38  #Define  : 0
% 2.55/1.38  #Split   : 4
% 2.55/1.38  #Chain   : 0
% 2.55/1.38  #Close   : 0
% 2.55/1.38  
% 2.55/1.38  Ordering : KBO
% 2.55/1.38  
% 2.55/1.38  Simplification rules
% 2.55/1.38  ----------------------
% 2.55/1.38  #Subsume      : 14
% 2.55/1.39  #Demod        : 161
% 2.55/1.39  #Tautology    : 79
% 2.55/1.39  #SimpNegUnit  : 6
% 2.55/1.39  #BackRed      : 47
% 2.55/1.39  
% 2.55/1.39  #Partial instantiations: 0
% 2.55/1.39  #Strategies tried      : 1
% 2.55/1.39  
% 2.55/1.39  Timing (in seconds)
% 2.55/1.39  ----------------------
% 2.55/1.39  Preprocessing        : 0.33
% 2.55/1.39  Parsing              : 0.18
% 2.55/1.39  CNF conversion       : 0.02
% 2.55/1.39  Main loop            : 0.27
% 2.55/1.39  Inferencing          : 0.10
% 2.55/1.39  Reduction            : 0.09
% 2.55/1.39  Demodulation         : 0.06
% 2.55/1.39  BG Simplification    : 0.02
% 2.55/1.39  Subsumption          : 0.05
% 2.55/1.39  Abstraction          : 0.02
% 2.55/1.39  MUC search           : 0.00
% 2.55/1.39  Cooper               : 0.00
% 2.55/1.39  Total                : 0.64
% 2.55/1.39  Index Insertion      : 0.00
% 2.55/1.39  Index Deletion       : 0.00
% 2.55/1.39  Index Matching       : 0.00
% 2.55/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
