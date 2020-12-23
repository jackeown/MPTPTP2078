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
% DateTime   : Thu Dec  3 09:55:51 EST 2020

% Result     : Theorem 37.21s
% Output     : CNFRefutation 37.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 269 expanded)
%              Number of leaves         :   41 ( 104 expanded)
%              Depth                    :   17
%              Number of atoms          :  171 ( 436 expanded)
%              Number of equality atoms :   48 ( 109 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_104,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_110,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_101,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_68,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | r1_tarski(k3_subset_1('#skF_5','#skF_7'),k3_subset_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_95,plain,(
    r1_tarski(k3_subset_1('#skF_5','#skF_7'),k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_62,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_5','#skF_7'),k3_subset_1('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_150,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_62])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_52,plain,(
    ! [A_38] : ~ v1_xboole_0(k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_359,plain,(
    ! [B_107,A_108] :
      ( r2_hidden(B_107,A_108)
      | ~ m1_subset_1(B_107,A_108)
      | v1_xboole_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [C_31,A_27] :
      ( r1_tarski(C_31,A_27)
      | ~ r2_hidden(C_31,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_374,plain,(
    ! [B_107,A_27] :
      ( r1_tarski(B_107,A_27)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_27))
      | v1_xboole_0(k1_zfmisc_1(A_27)) ) ),
    inference(resolution,[status(thm)],[c_359,c_28])).

tff(c_826,plain,(
    ! [B_134,A_135] :
      ( r1_tarski(B_134,A_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_135)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_374])).

tff(c_852,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_826])).

tff(c_16,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_325,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k4_xboole_0(B_102,A_101)) = k2_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_334,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = k2_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_325])).

tff(c_337,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_334])).

tff(c_854,plain,(
    ! [A_136,B_137] :
      ( k4_xboole_0(A_136,B_137) = k3_subset_1(A_136,B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_878,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_854])).

tff(c_12,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_xboole_0(A_12,C_14)
      | ~ r1_tarski(A_12,k4_xboole_0(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4982,plain,(
    ! [A_225] :
      ( r1_xboole_0(A_225,'#skF_6')
      | ~ r1_tarski(A_225,k3_subset_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_878,c_12])).

tff(c_5052,plain,(
    r1_xboole_0(k3_subset_1('#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_95,c_4982])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5061,plain,(
    r1_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_5052,c_2])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_176,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_181,plain,(
    ! [A_76,B_77] :
      ( ~ r1_xboole_0(A_76,B_77)
      | k3_xboole_0(A_76,B_77) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_176])).

tff(c_5067,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5061,c_181])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5111,plain,(
    k4_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5067,c_10])).

tff(c_5124,plain,(
    k4_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_5111])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_498,plain,(
    ! [A_115,B_116] :
      ( k3_subset_1(A_115,k3_subset_1(A_115,B_116)) = B_116
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_517,plain,(
    k3_subset_1('#skF_5',k3_subset_1('#skF_5','#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_58,c_498])).

tff(c_879,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_854])).

tff(c_56,plain,(
    ! [A_41,B_42] : k6_subset_1(A_41,B_42) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_50,plain,(
    ! [A_36,B_37] : m1_subset_1(k6_subset_1(A_36,B_37),k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_69,plain,(
    ! [A_36,B_37] : m1_subset_1(k4_xboole_0(A_36,B_37),k1_zfmisc_1(A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50])).

tff(c_2787,plain,(
    ! [A_199,B_200] : k4_xboole_0(A_199,k4_xboole_0(A_199,B_200)) = k3_subset_1(A_199,k4_xboole_0(A_199,B_200)) ),
    inference(resolution,[status(thm)],[c_69,c_854])).

tff(c_18,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(k4_xboole_0(A_16,C_18),k4_xboole_0(B_17,C_18))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20496,plain,(
    ! [A_465,A_466,B_467] :
      ( r1_tarski(k4_xboole_0(A_465,k4_xboole_0(A_466,B_467)),k3_subset_1(A_466,k4_xboole_0(A_466,B_467)))
      | ~ r1_tarski(A_465,A_466) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2787,c_18])).

tff(c_20650,plain,(
    ! [A_465] :
      ( r1_tarski(k4_xboole_0(A_465,k3_subset_1('#skF_5','#skF_7')),k3_subset_1('#skF_5',k4_xboole_0('#skF_5','#skF_7')))
      | ~ r1_tarski(A_465,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_20496])).

tff(c_56788,plain,(
    ! [A_740] :
      ( r1_tarski(k4_xboole_0(A_740,k3_subset_1('#skF_5','#skF_7')),'#skF_7')
      | ~ r1_tarski(A_740,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_879,c_20650])).

tff(c_56815,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5124,c_56788])).

tff(c_56837,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_56815])).

tff(c_56839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_56837])).

tff(c_56841,plain,(
    ~ r1_tarski(k3_subset_1('#skF_5','#skF_7'),k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_57359,plain,(
    ! [A_809,B_810] :
      ( k4_xboole_0(A_809,B_810) = k3_subset_1(A_809,B_810)
      | ~ m1_subset_1(B_810,k1_zfmisc_1(A_809)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_57380,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_57359])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_57503,plain,(
    r1_tarski(k3_subset_1('#skF_5','#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_57380,c_20])).

tff(c_56940,plain,(
    ! [A_771,B_772] : k5_xboole_0(A_771,k4_xboole_0(B_772,A_771)) = k2_xboole_0(A_771,B_772) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_56949,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = k2_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_56940])).

tff(c_56952,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_56949])).

tff(c_56840,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_30,plain,(
    ! [C_31,A_27] :
      ( r2_hidden(C_31,k1_zfmisc_1(A_27))
      | ~ r1_tarski(C_31,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_57182,plain,(
    ! [B_795,A_796] :
      ( m1_subset_1(B_795,A_796)
      | ~ r2_hidden(B_795,A_796)
      | v1_xboole_0(A_796) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_57188,plain,(
    ! [C_31,A_27] :
      ( m1_subset_1(C_31,k1_zfmisc_1(A_27))
      | v1_xboole_0(k1_zfmisc_1(A_27))
      | ~ r1_tarski(C_31,A_27) ) ),
    inference(resolution,[status(thm)],[c_30,c_57182])).

tff(c_58553,plain,(
    ! [C_843,A_844] :
      ( m1_subset_1(C_843,k1_zfmisc_1(A_844))
      | ~ r1_tarski(C_843,A_844) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_57188])).

tff(c_54,plain,(
    ! [A_39,B_40] :
      ( k3_subset_1(A_39,k3_subset_1(A_39,B_40)) = B_40
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_58566,plain,(
    ! [A_844,C_843] :
      ( k3_subset_1(A_844,k3_subset_1(A_844,C_843)) = C_843
      | ~ r1_tarski(C_843,A_844) ) ),
    inference(resolution,[status(thm)],[c_58553,c_54])).

tff(c_48,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k3_subset_1(A_34,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_66908,plain,(
    ! [A_1036,C_1037] :
      ( k4_xboole_0(A_1036,C_1037) = k3_subset_1(A_1036,C_1037)
      | ~ r1_tarski(C_1037,A_1036) ) ),
    inference(resolution,[status(thm)],[c_58553,c_48])).

tff(c_67093,plain,(
    k4_xboole_0('#skF_7','#skF_6') = k3_subset_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_56840,c_66908])).

tff(c_59996,plain,(
    ! [A_899,B_900] : k4_xboole_0(A_899,k4_xboole_0(A_899,B_900)) = k3_subset_1(A_899,k4_xboole_0(A_899,B_900)) ),
    inference(resolution,[status(thm)],[c_69,c_57359])).

tff(c_60157,plain,(
    ! [A_899,B_900] : m1_subset_1(k3_subset_1(A_899,k4_xboole_0(A_899,B_900)),k1_zfmisc_1(A_899)) ),
    inference(superposition,[status(thm),theory(equality)],[c_59996,c_69])).

tff(c_67124,plain,(
    m1_subset_1(k3_subset_1('#skF_7',k3_subset_1('#skF_7','#skF_6')),k1_zfmisc_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_67093,c_60157])).

tff(c_75358,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1('#skF_7'))
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_58566,c_67124])).

tff(c_75365,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56840,c_75358])).

tff(c_75379,plain,(
    k3_subset_1('#skF_7',k3_subset_1('#skF_7','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_75365,c_54])).

tff(c_57297,plain,(
    ! [A_805,B_806] :
      ( k3_subset_1(A_805,k3_subset_1(A_805,B_806)) = B_806
      | ~ m1_subset_1(B_806,k1_zfmisc_1(A_805)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_57313,plain,(
    k3_subset_1('#skF_5',k3_subset_1('#skF_5','#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_58,c_57297])).

tff(c_57500,plain,(
    m1_subset_1(k3_subset_1('#skF_5','#skF_7'),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_57380,c_69])).

tff(c_57525,plain,(
    k4_xboole_0('#skF_5',k3_subset_1('#skF_5','#skF_7')) = k3_subset_1('#skF_5',k3_subset_1('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_57500,c_48])).

tff(c_57535,plain,(
    k4_xboole_0('#skF_5',k3_subset_1('#skF_5','#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57313,c_57525])).

tff(c_56888,plain,(
    ! [A_754,C_755,B_756] :
      ( r1_xboole_0(A_754,C_755)
      | ~ r1_tarski(A_754,k4_xboole_0(B_756,C_755)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56896,plain,(
    ! [B_756,C_755,B_20] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_756,C_755),B_20),C_755) ),
    inference(resolution,[status(thm)],[c_20,c_56888])).

tff(c_70800,plain,(
    ! [B_1086,C_1087,B_1088] : r1_xboole_0(k3_subset_1(k4_xboole_0(B_1086,C_1087),k4_xboole_0(k4_xboole_0(B_1086,C_1087),B_1088)),C_1087) ),
    inference(superposition,[status(thm),theory(equality)],[c_59996,c_56896])).

tff(c_70924,plain,(
    ! [B_1088] : r1_xboole_0(k3_subset_1('#skF_7',k4_xboole_0(k4_xboole_0('#skF_5',k3_subset_1('#skF_5','#skF_7')),B_1088)),k3_subset_1('#skF_5','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_57535,c_70800])).

tff(c_130138,plain,(
    ! [B_1555] : r1_xboole_0(k3_subset_1('#skF_7',k4_xboole_0('#skF_7',B_1555)),k3_subset_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57535,c_70924])).

tff(c_130195,plain,(
    r1_xboole_0(k3_subset_1('#skF_7',k3_subset_1('#skF_7','#skF_6')),k3_subset_1('#skF_5','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_67093,c_130138])).

tff(c_130239,plain,(
    r1_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75379,c_130195])).

tff(c_130254,plain,(
    r1_xboole_0(k3_subset_1('#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_130239,c_2])).

tff(c_57002,plain,(
    ! [A_781,B_782,C_783] :
      ( ~ r1_xboole_0(A_781,B_782)
      | ~ r2_hidden(C_783,k3_xboole_0(A_781,B_782)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57012,plain,(
    ! [A_781,B_782] :
      ( ~ r1_xboole_0(A_781,B_782)
      | k3_xboole_0(A_781,B_782) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_57002])).

tff(c_130261,plain,(
    k3_xboole_0(k3_subset_1('#skF_5','#skF_7'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130254,c_57012])).

tff(c_130347,plain,(
    k5_xboole_0(k3_subset_1('#skF_5','#skF_7'),k1_xboole_0) = k4_xboole_0(k3_subset_1('#skF_5','#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_130261,c_10])).

tff(c_130371,plain,(
    k4_xboole_0(k3_subset_1('#skF_5','#skF_7'),'#skF_6') = k3_subset_1('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56952,c_130347])).

tff(c_57379,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_57359])).

tff(c_57434,plain,(
    ! [A_811,C_812,B_813] :
      ( r1_tarski(k4_xboole_0(A_811,C_812),k4_xboole_0(B_813,C_812))
      | ~ r1_tarski(A_811,B_813) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_57446,plain,(
    ! [A_811] :
      ( r1_tarski(k4_xboole_0(A_811,'#skF_6'),k3_subset_1('#skF_5','#skF_6'))
      | ~ r1_tarski(A_811,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57379,c_57434])).

tff(c_132010,plain,
    ( r1_tarski(k3_subset_1('#skF_5','#skF_7'),k3_subset_1('#skF_5','#skF_6'))
    | ~ r1_tarski(k3_subset_1('#skF_5','#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_130371,c_57446])).

tff(c_132229,plain,(
    r1_tarski(k3_subset_1('#skF_5','#skF_7'),k3_subset_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57503,c_132010])).

tff(c_132231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56841,c_132229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:49:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.21/27.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.21/27.21  
% 37.21/27.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.21/27.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 37.21/27.21  
% 37.21/27.21  %Foreground sorts:
% 37.21/27.21  
% 37.21/27.21  
% 37.21/27.21  %Background operators:
% 37.21/27.21  
% 37.21/27.21  
% 37.21/27.21  %Foreground operators:
% 37.21/27.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 37.21/27.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.21/27.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 37.21/27.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 37.21/27.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 37.21/27.21  tff('#skF_7', type, '#skF_7': $i).
% 37.21/27.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 37.21/27.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 37.21/27.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 37.21/27.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 37.21/27.21  tff('#skF_5', type, '#skF_5': $i).
% 37.21/27.21  tff('#skF_6', type, '#skF_6': $i).
% 37.21/27.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 37.21/27.21  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 37.21/27.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 37.21/27.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.21/27.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.21/27.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 37.21/27.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 37.21/27.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 37.21/27.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 37.21/27.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 37.21/27.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 37.21/27.21  
% 37.21/27.23  tff(f_120, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 37.21/27.23  tff(f_104, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 37.21/27.23  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 37.21/27.23  tff(f_82, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 37.21/27.23  tff(f_61, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 37.21/27.23  tff(f_69, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 37.21/27.23  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 37.21/27.23  tff(f_99, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 37.21/27.23  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 37.21/27.23  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 37.21/27.23  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 37.21/27.23  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 37.21/27.23  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 37.21/27.23  tff(f_108, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 37.21/27.23  tff(f_110, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 37.21/27.23  tff(f_101, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 37.21/27.23  tff(f_65, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_xboole_1)).
% 37.21/27.23  tff(f_67, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 37.21/27.23  tff(c_68, plain, (r1_tarski('#skF_6', '#skF_7') | r1_tarski(k3_subset_1('#skF_5', '#skF_7'), k3_subset_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 37.21/27.23  tff(c_95, plain, (r1_tarski(k3_subset_1('#skF_5', '#skF_7'), k3_subset_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_68])).
% 37.21/27.23  tff(c_62, plain, (~r1_tarski(k3_subset_1('#skF_5', '#skF_7'), k3_subset_1('#skF_5', '#skF_6')) | ~r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 37.21/27.23  tff(c_150, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_62])).
% 37.21/27.23  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 37.21/27.23  tff(c_52, plain, (![A_38]: (~v1_xboole_0(k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 37.21/27.23  tff(c_359, plain, (![B_107, A_108]: (r2_hidden(B_107, A_108) | ~m1_subset_1(B_107, A_108) | v1_xboole_0(A_108))), inference(cnfTransformation, [status(thm)], [f_95])).
% 37.21/27.23  tff(c_28, plain, (![C_31, A_27]: (r1_tarski(C_31, A_27) | ~r2_hidden(C_31, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 37.21/27.23  tff(c_374, plain, (![B_107, A_27]: (r1_tarski(B_107, A_27) | ~m1_subset_1(B_107, k1_zfmisc_1(A_27)) | v1_xboole_0(k1_zfmisc_1(A_27)))), inference(resolution, [status(thm)], [c_359, c_28])).
% 37.21/27.23  tff(c_826, plain, (![B_134, A_135]: (r1_tarski(B_134, A_135) | ~m1_subset_1(B_134, k1_zfmisc_1(A_135)))), inference(negUnitSimplification, [status(thm)], [c_52, c_374])).
% 37.21/27.23  tff(c_852, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_826])).
% 37.21/27.23  tff(c_16, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_61])).
% 37.21/27.23  tff(c_22, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 37.21/27.23  tff(c_325, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k4_xboole_0(B_102, A_101))=k2_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_75])).
% 37.21/27.23  tff(c_334, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=k2_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_325])).
% 37.21/27.23  tff(c_337, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_334])).
% 37.21/27.23  tff(c_854, plain, (![A_136, B_137]: (k4_xboole_0(A_136, B_137)=k3_subset_1(A_136, B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 37.21/27.23  tff(c_878, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_854])).
% 37.21/27.23  tff(c_12, plain, (![A_12, C_14, B_13]: (r1_xboole_0(A_12, C_14) | ~r1_tarski(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 37.21/27.23  tff(c_4982, plain, (![A_225]: (r1_xboole_0(A_225, '#skF_6') | ~r1_tarski(A_225, k3_subset_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_878, c_12])).
% 37.21/27.23  tff(c_5052, plain, (r1_xboole_0(k3_subset_1('#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_95, c_4982])).
% 37.21/27.23  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 37.21/27.23  tff(c_5061, plain, (r1_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_5052, c_2])).
% 37.21/27.23  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 37.21/27.23  tff(c_176, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 37.21/27.23  tff(c_181, plain, (![A_76, B_77]: (~r1_xboole_0(A_76, B_77) | k3_xboole_0(A_76, B_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_176])).
% 37.21/27.23  tff(c_5067, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_5061, c_181])).
% 37.21/27.23  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 37.21/27.23  tff(c_5111, plain, (k4_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5067, c_10])).
% 37.21/27.23  tff(c_5124, plain, (k4_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_337, c_5111])).
% 37.21/27.23  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 37.21/27.23  tff(c_498, plain, (![A_115, B_116]: (k3_subset_1(A_115, k3_subset_1(A_115, B_116))=B_116 | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 37.21/27.23  tff(c_517, plain, (k3_subset_1('#skF_5', k3_subset_1('#skF_5', '#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_58, c_498])).
% 37.21/27.23  tff(c_879, plain, (k4_xboole_0('#skF_5', '#skF_7')=k3_subset_1('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_58, c_854])).
% 37.21/27.23  tff(c_56, plain, (![A_41, B_42]: (k6_subset_1(A_41, B_42)=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_110])).
% 37.21/27.23  tff(c_50, plain, (![A_36, B_37]: (m1_subset_1(k6_subset_1(A_36, B_37), k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 37.21/27.23  tff(c_69, plain, (![A_36, B_37]: (m1_subset_1(k4_xboole_0(A_36, B_37), k1_zfmisc_1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50])).
% 37.21/27.23  tff(c_2787, plain, (![A_199, B_200]: (k4_xboole_0(A_199, k4_xboole_0(A_199, B_200))=k3_subset_1(A_199, k4_xboole_0(A_199, B_200)))), inference(resolution, [status(thm)], [c_69, c_854])).
% 37.21/27.23  tff(c_18, plain, (![A_16, C_18, B_17]: (r1_tarski(k4_xboole_0(A_16, C_18), k4_xboole_0(B_17, C_18)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 37.21/27.23  tff(c_20496, plain, (![A_465, A_466, B_467]: (r1_tarski(k4_xboole_0(A_465, k4_xboole_0(A_466, B_467)), k3_subset_1(A_466, k4_xboole_0(A_466, B_467))) | ~r1_tarski(A_465, A_466))), inference(superposition, [status(thm), theory('equality')], [c_2787, c_18])).
% 37.21/27.24  tff(c_20650, plain, (![A_465]: (r1_tarski(k4_xboole_0(A_465, k3_subset_1('#skF_5', '#skF_7')), k3_subset_1('#skF_5', k4_xboole_0('#skF_5', '#skF_7'))) | ~r1_tarski(A_465, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_879, c_20496])).
% 37.21/27.24  tff(c_56788, plain, (![A_740]: (r1_tarski(k4_xboole_0(A_740, k3_subset_1('#skF_5', '#skF_7')), '#skF_7') | ~r1_tarski(A_740, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_517, c_879, c_20650])).
% 37.21/27.24  tff(c_56815, plain, (r1_tarski('#skF_6', '#skF_7') | ~r1_tarski('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5124, c_56788])).
% 37.21/27.24  tff(c_56837, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_852, c_56815])).
% 37.21/27.24  tff(c_56839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_56837])).
% 37.21/27.24  tff(c_56841, plain, (~r1_tarski(k3_subset_1('#skF_5', '#skF_7'), k3_subset_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_68])).
% 37.21/27.24  tff(c_57359, plain, (![A_809, B_810]: (k4_xboole_0(A_809, B_810)=k3_subset_1(A_809, B_810) | ~m1_subset_1(B_810, k1_zfmisc_1(A_809)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 37.21/27.24  tff(c_57380, plain, (k4_xboole_0('#skF_5', '#skF_7')=k3_subset_1('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_58, c_57359])).
% 37.21/27.24  tff(c_20, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 37.21/27.24  tff(c_57503, plain, (r1_tarski(k3_subset_1('#skF_5', '#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_57380, c_20])).
% 37.21/27.24  tff(c_56940, plain, (![A_771, B_772]: (k5_xboole_0(A_771, k4_xboole_0(B_772, A_771))=k2_xboole_0(A_771, B_772))), inference(cnfTransformation, [status(thm)], [f_75])).
% 37.21/27.24  tff(c_56949, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=k2_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_56940])).
% 37.21/27.24  tff(c_56952, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_56949])).
% 37.21/27.24  tff(c_56840, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 37.21/27.24  tff(c_30, plain, (![C_31, A_27]: (r2_hidden(C_31, k1_zfmisc_1(A_27)) | ~r1_tarski(C_31, A_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 37.21/27.24  tff(c_57182, plain, (![B_795, A_796]: (m1_subset_1(B_795, A_796) | ~r2_hidden(B_795, A_796) | v1_xboole_0(A_796))), inference(cnfTransformation, [status(thm)], [f_95])).
% 37.21/27.24  tff(c_57188, plain, (![C_31, A_27]: (m1_subset_1(C_31, k1_zfmisc_1(A_27)) | v1_xboole_0(k1_zfmisc_1(A_27)) | ~r1_tarski(C_31, A_27))), inference(resolution, [status(thm)], [c_30, c_57182])).
% 37.21/27.24  tff(c_58553, plain, (![C_843, A_844]: (m1_subset_1(C_843, k1_zfmisc_1(A_844)) | ~r1_tarski(C_843, A_844))), inference(negUnitSimplification, [status(thm)], [c_52, c_57188])).
% 37.21/27.24  tff(c_54, plain, (![A_39, B_40]: (k3_subset_1(A_39, k3_subset_1(A_39, B_40))=B_40 | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 37.21/27.24  tff(c_58566, plain, (![A_844, C_843]: (k3_subset_1(A_844, k3_subset_1(A_844, C_843))=C_843 | ~r1_tarski(C_843, A_844))), inference(resolution, [status(thm)], [c_58553, c_54])).
% 37.21/27.24  tff(c_48, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k3_subset_1(A_34, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 37.21/27.24  tff(c_66908, plain, (![A_1036, C_1037]: (k4_xboole_0(A_1036, C_1037)=k3_subset_1(A_1036, C_1037) | ~r1_tarski(C_1037, A_1036))), inference(resolution, [status(thm)], [c_58553, c_48])).
% 37.21/27.24  tff(c_67093, plain, (k4_xboole_0('#skF_7', '#skF_6')=k3_subset_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_56840, c_66908])).
% 37.21/27.24  tff(c_59996, plain, (![A_899, B_900]: (k4_xboole_0(A_899, k4_xboole_0(A_899, B_900))=k3_subset_1(A_899, k4_xboole_0(A_899, B_900)))), inference(resolution, [status(thm)], [c_69, c_57359])).
% 37.21/27.24  tff(c_60157, plain, (![A_899, B_900]: (m1_subset_1(k3_subset_1(A_899, k4_xboole_0(A_899, B_900)), k1_zfmisc_1(A_899)))), inference(superposition, [status(thm), theory('equality')], [c_59996, c_69])).
% 37.21/27.24  tff(c_67124, plain, (m1_subset_1(k3_subset_1('#skF_7', k3_subset_1('#skF_7', '#skF_6')), k1_zfmisc_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_67093, c_60157])).
% 37.21/27.24  tff(c_75358, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_7')) | ~r1_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_58566, c_67124])).
% 37.21/27.24  tff(c_75365, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56840, c_75358])).
% 37.21/27.24  tff(c_75379, plain, (k3_subset_1('#skF_7', k3_subset_1('#skF_7', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_75365, c_54])).
% 37.21/27.24  tff(c_57297, plain, (![A_805, B_806]: (k3_subset_1(A_805, k3_subset_1(A_805, B_806))=B_806 | ~m1_subset_1(B_806, k1_zfmisc_1(A_805)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 37.21/27.24  tff(c_57313, plain, (k3_subset_1('#skF_5', k3_subset_1('#skF_5', '#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_58, c_57297])).
% 37.21/27.24  tff(c_57500, plain, (m1_subset_1(k3_subset_1('#skF_5', '#skF_7'), k1_zfmisc_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57380, c_69])).
% 37.21/27.24  tff(c_57525, plain, (k4_xboole_0('#skF_5', k3_subset_1('#skF_5', '#skF_7'))=k3_subset_1('#skF_5', k3_subset_1('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_57500, c_48])).
% 37.21/27.24  tff(c_57535, plain, (k4_xboole_0('#skF_5', k3_subset_1('#skF_5', '#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_57313, c_57525])).
% 37.21/27.24  tff(c_56888, plain, (![A_754, C_755, B_756]: (r1_xboole_0(A_754, C_755) | ~r1_tarski(A_754, k4_xboole_0(B_756, C_755)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 37.21/27.24  tff(c_56896, plain, (![B_756, C_755, B_20]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_756, C_755), B_20), C_755))), inference(resolution, [status(thm)], [c_20, c_56888])).
% 37.21/27.24  tff(c_70800, plain, (![B_1086, C_1087, B_1088]: (r1_xboole_0(k3_subset_1(k4_xboole_0(B_1086, C_1087), k4_xboole_0(k4_xboole_0(B_1086, C_1087), B_1088)), C_1087))), inference(superposition, [status(thm), theory('equality')], [c_59996, c_56896])).
% 37.21/27.24  tff(c_70924, plain, (![B_1088]: (r1_xboole_0(k3_subset_1('#skF_7', k4_xboole_0(k4_xboole_0('#skF_5', k3_subset_1('#skF_5', '#skF_7')), B_1088)), k3_subset_1('#skF_5', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_57535, c_70800])).
% 37.21/27.24  tff(c_130138, plain, (![B_1555]: (r1_xboole_0(k3_subset_1('#skF_7', k4_xboole_0('#skF_7', B_1555)), k3_subset_1('#skF_5', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_57535, c_70924])).
% 37.21/27.24  tff(c_130195, plain, (r1_xboole_0(k3_subset_1('#skF_7', k3_subset_1('#skF_7', '#skF_6')), k3_subset_1('#skF_5', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_67093, c_130138])).
% 37.21/27.24  tff(c_130239, plain, (r1_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_75379, c_130195])).
% 37.21/27.24  tff(c_130254, plain, (r1_xboole_0(k3_subset_1('#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_130239, c_2])).
% 37.21/27.24  tff(c_57002, plain, (![A_781, B_782, C_783]: (~r1_xboole_0(A_781, B_782) | ~r2_hidden(C_783, k3_xboole_0(A_781, B_782)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 37.21/27.24  tff(c_57012, plain, (![A_781, B_782]: (~r1_xboole_0(A_781, B_782) | k3_xboole_0(A_781, B_782)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_57002])).
% 37.21/27.24  tff(c_130261, plain, (k3_xboole_0(k3_subset_1('#skF_5', '#skF_7'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_130254, c_57012])).
% 37.21/27.24  tff(c_130347, plain, (k5_xboole_0(k3_subset_1('#skF_5', '#skF_7'), k1_xboole_0)=k4_xboole_0(k3_subset_1('#skF_5', '#skF_7'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_130261, c_10])).
% 37.21/27.24  tff(c_130371, plain, (k4_xboole_0(k3_subset_1('#skF_5', '#skF_7'), '#skF_6')=k3_subset_1('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56952, c_130347])).
% 37.21/27.24  tff(c_57379, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_57359])).
% 37.21/27.24  tff(c_57434, plain, (![A_811, C_812, B_813]: (r1_tarski(k4_xboole_0(A_811, C_812), k4_xboole_0(B_813, C_812)) | ~r1_tarski(A_811, B_813))), inference(cnfTransformation, [status(thm)], [f_65])).
% 37.21/27.24  tff(c_57446, plain, (![A_811]: (r1_tarski(k4_xboole_0(A_811, '#skF_6'), k3_subset_1('#skF_5', '#skF_6')) | ~r1_tarski(A_811, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57379, c_57434])).
% 37.21/27.24  tff(c_132010, plain, (r1_tarski(k3_subset_1('#skF_5', '#skF_7'), k3_subset_1('#skF_5', '#skF_6')) | ~r1_tarski(k3_subset_1('#skF_5', '#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_130371, c_57446])).
% 37.21/27.24  tff(c_132229, plain, (r1_tarski(k3_subset_1('#skF_5', '#skF_7'), k3_subset_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_57503, c_132010])).
% 37.21/27.24  tff(c_132231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56841, c_132229])).
% 37.21/27.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.21/27.24  
% 37.21/27.24  Inference rules
% 37.21/27.24  ----------------------
% 37.21/27.24  #Ref     : 0
% 37.21/27.24  #Sup     : 31793
% 37.21/27.24  #Fact    : 0
% 37.21/27.24  #Define  : 0
% 37.21/27.24  #Split   : 31
% 37.21/27.24  #Chain   : 0
% 37.21/27.24  #Close   : 0
% 37.21/27.24  
% 37.21/27.24  Ordering : KBO
% 37.21/27.24  
% 37.21/27.24  Simplification rules
% 37.21/27.24  ----------------------
% 37.21/27.24  #Subsume      : 5335
% 37.21/27.24  #Demod        : 27359
% 37.21/27.24  #Tautology    : 14465
% 37.21/27.24  #SimpNegUnit  : 890
% 37.21/27.24  #BackRed      : 136
% 37.21/27.24  
% 37.21/27.24  #Partial instantiations: 0
% 37.21/27.24  #Strategies tried      : 1
% 37.21/27.24  
% 37.21/27.24  Timing (in seconds)
% 37.21/27.24  ----------------------
% 37.39/27.24  Preprocessing        : 0.33
% 37.39/27.24  Parsing              : 0.17
% 37.39/27.24  CNF conversion       : 0.02
% 37.39/27.24  Main loop            : 26.11
% 37.39/27.24  Inferencing          : 2.92
% 37.39/27.24  Reduction            : 14.97
% 37.39/27.24  Demodulation         : 13.11
% 37.39/27.24  BG Simplification    : 0.30
% 37.39/27.24  Subsumption          : 6.49
% 37.39/27.24  Abstraction          : 0.42
% 37.39/27.24  MUC search           : 0.00
% 37.39/27.24  Cooper               : 0.00
% 37.39/27.24  Total                : 26.49
% 37.39/27.24  Index Insertion      : 0.00
% 37.39/27.24  Index Deletion       : 0.00
% 37.39/27.24  Index Matching       : 0.00
% 37.39/27.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
