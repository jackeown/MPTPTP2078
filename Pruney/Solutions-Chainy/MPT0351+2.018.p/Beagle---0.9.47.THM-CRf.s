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
% DateTime   : Thu Dec  3 09:55:39 EST 2020

% Result     : Theorem 9.42s
% Output     : CNFRefutation 9.42s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 317 expanded)
%              Number of leaves         :   48 ( 126 expanded)
%              Depth                    :   17
%              Number of atoms          :  139 ( 526 expanded)
%              Number of equality atoms :   48 ( 167 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_103,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_106,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_83,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_100,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_74,plain,(
    ! [A_56] : k2_subset_1(A_56) = A_56 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_84,plain,(
    k4_subset_1('#skF_6','#skF_7',k2_subset_1('#skF_6')) != k2_subset_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_88,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_84])).

tff(c_32,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    ! [A_58] : m1_subset_1('#skF_5'(A_58),A_58) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_68,plain,(
    ! [B_55,A_54] :
      ( r2_hidden(B_55,A_54)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_86,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_80,plain,(
    ! [A_60] : ~ v1_xboole_0(k1_zfmisc_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_418,plain,(
    ! [B_107,A_108] :
      ( r2_hidden(B_107,A_108)
      | ~ m1_subset_1(B_107,A_108)
      | v1_xboole_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_52,plain,(
    ! [C_51,A_47] :
      ( r1_tarski(C_51,A_47)
      | ~ r2_hidden(C_51,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_422,plain,(
    ! [B_107,A_47] :
      ( r1_tarski(B_107,A_47)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_47))
      | v1_xboole_0(k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_418,c_52])).

tff(c_441,plain,(
    ! [B_113,A_114] :
      ( r1_tarski(B_113,A_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_114)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_422])).

tff(c_460,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_441])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_467,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_460,c_30])).

tff(c_28,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_471,plain,(
    k5_xboole_0('#skF_7','#skF_7') = k4_xboole_0('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_28])).

tff(c_26,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_156,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,B_78) = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_160,plain,(
    ! [B_8] : k3_xboole_0(B_8,B_8) = B_8 ),
    inference(resolution,[status(thm)],[c_26,c_156])).

tff(c_352,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_361,plain,(
    ! [B_8] : k5_xboole_0(B_8,B_8) = k4_xboole_0(B_8,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_352])).

tff(c_496,plain,(
    k4_xboole_0('#skF_7','#skF_7') = k4_xboole_0('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_361])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_566,plain,(
    ! [D_129] :
      ( ~ r2_hidden(D_129,'#skF_7')
      | ~ r2_hidden(D_129,k4_xboole_0('#skF_7','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_4])).

tff(c_571,plain,(
    ! [B_55] :
      ( ~ r2_hidden(B_55,'#skF_7')
      | ~ m1_subset_1(B_55,k4_xboole_0('#skF_7','#skF_6'))
      | v1_xboole_0(k4_xboole_0('#skF_7','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_68,c_566])).

tff(c_576,plain,(
    ! [B_131] :
      ( ~ r2_hidden(B_131,'#skF_7')
      | ~ m1_subset_1(B_131,k4_xboole_0('#skF_7','#skF_6')) ) ),
    inference(splitLeft,[status(thm)],[c_571])).

tff(c_586,plain,(
    ~ r2_hidden('#skF_5'(k4_xboole_0('#skF_7','#skF_6')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_576])).

tff(c_70,plain,(
    ! [B_55,A_54] :
      ( m1_subset_1(B_55,A_54)
      | ~ v1_xboole_0(B_55)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_585,plain,(
    ! [B_55] :
      ( ~ r2_hidden(B_55,'#skF_7')
      | ~ v1_xboole_0(B_55)
      | ~ v1_xboole_0(k4_xboole_0('#skF_7','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_70,c_576])).

tff(c_614,plain,(
    ~ v1_xboole_0(k4_xboole_0('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_585])).

tff(c_483,plain,(
    ! [D_116,A_117,B_118] :
      ( r2_hidden(D_116,A_117)
      | ~ r2_hidden(D_116,k4_xboole_0(A_117,B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2510,plain,(
    ! [B_206,A_207,B_208] :
      ( r2_hidden(B_206,A_207)
      | ~ m1_subset_1(B_206,k4_xboole_0(A_207,B_208))
      | v1_xboole_0(k4_xboole_0(A_207,B_208)) ) ),
    inference(resolution,[status(thm)],[c_68,c_483])).

tff(c_2513,plain,(
    ! [B_206] :
      ( r2_hidden(B_206,'#skF_7')
      | ~ m1_subset_1(B_206,k4_xboole_0('#skF_7','#skF_6'))
      | v1_xboole_0(k4_xboole_0('#skF_7','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_2510])).

tff(c_2525,plain,(
    ! [B_206] :
      ( r2_hidden(B_206,'#skF_7')
      | ~ m1_subset_1(B_206,k4_xboole_0('#skF_7','#skF_6'))
      | v1_xboole_0(k4_xboole_0('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_2513])).

tff(c_2530,plain,(
    ! [B_209] :
      ( r2_hidden(B_209,'#skF_7')
      | ~ m1_subset_1(B_209,k4_xboole_0('#skF_7','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_614,c_2525])).

tff(c_2538,plain,(
    r2_hidden('#skF_5'(k4_xboole_0('#skF_7','#skF_6')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_2530])).

tff(c_2543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_586,c_2538])).

tff(c_2545,plain,(
    v1_xboole_0(k4_xboole_0('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_145,plain,(
    ! [B_72,A_73] :
      ( ~ v1_xboole_0(B_72)
      | B_72 = A_73
      | ~ v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_148,plain,(
    ! [A_73] :
      ( k1_xboole_0 = A_73
      | ~ v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_20,c_145])).

tff(c_2564,plain,(
    k4_xboole_0('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2545,c_148])).

tff(c_36,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2587,plain,(
    k5_xboole_0('#skF_6',k1_xboole_0) = k2_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2564,c_36])).

tff(c_2590,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2587])).

tff(c_38,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_276,plain,(
    ! [A_90,B_91] : k3_tarski(k2_tarski(A_90,B_91)) = k2_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_296,plain,(
    ! [A_94,B_95] : k3_tarski(k2_tarski(A_94,B_95)) = k2_xboole_0(B_95,A_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_276])).

tff(c_64,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_302,plain,(
    ! [B_95,A_94] : k2_xboole_0(B_95,A_94) = k2_xboole_0(A_94,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_64])).

tff(c_76,plain,(
    ! [A_57] : m1_subset_1(k2_subset_1(A_57),k1_zfmisc_1(A_57)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_87,plain,(
    ! [A_57] : m1_subset_1(A_57,k1_zfmisc_1(A_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76])).

tff(c_5293,plain,(
    ! [A_324,B_325,C_326] :
      ( k4_subset_1(A_324,B_325,C_326) = k2_xboole_0(B_325,C_326)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(A_324))
      | ~ m1_subset_1(B_325,k1_zfmisc_1(A_324)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6542,plain,(
    ! [A_397,B_398] :
      ( k4_subset_1(A_397,B_398,A_397) = k2_xboole_0(B_398,A_397)
      | ~ m1_subset_1(B_398,k1_zfmisc_1(A_397)) ) ),
    inference(resolution,[status(thm)],[c_87,c_5293])).

tff(c_6557,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = k2_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_6542])).

tff(c_6568,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2590,c_302,c_6557])).

tff(c_6570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_6568])).

tff(c_6571,plain,(
    v1_xboole_0(k4_xboole_0('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_6587,plain,(
    k4_xboole_0('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6571,c_148])).

tff(c_6605,plain,(
    k5_xboole_0('#skF_6',k1_xboole_0) = k2_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6587,c_36])).

tff(c_6608,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6605])).

tff(c_11512,plain,(
    ! [A_617,B_618,C_619] :
      ( k4_subset_1(A_617,B_618,C_619) = k2_xboole_0(B_618,C_619)
      | ~ m1_subset_1(C_619,k1_zfmisc_1(A_617))
      | ~ m1_subset_1(B_618,k1_zfmisc_1(A_617)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12634,plain,(
    ! [A_693,B_694] :
      ( k4_subset_1(A_693,B_694,A_693) = k2_xboole_0(B_694,A_693)
      | ~ m1_subset_1(B_694,k1_zfmisc_1(A_693)) ) ),
    inference(resolution,[status(thm)],[c_87,c_11512])).

tff(c_12649,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = k2_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_12634])).

tff(c_12660,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6608,c_302,c_12649])).

tff(c_12662,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_12660])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:07:06 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.42/3.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.42/3.01  
% 9.42/3.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.42/3.02  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4
% 9.42/3.02  
% 9.42/3.02  %Foreground sorts:
% 9.42/3.02  
% 9.42/3.02  
% 9.42/3.02  %Background operators:
% 9.42/3.02  
% 9.42/3.02  
% 9.42/3.02  %Foreground operators:
% 9.42/3.02  tff('#skF_5', type, '#skF_5': $i > $i).
% 9.42/3.02  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.42/3.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.42/3.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.42/3.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.42/3.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.42/3.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.42/3.02  tff('#skF_7', type, '#skF_7': $i).
% 9.42/3.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.42/3.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.42/3.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.42/3.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.42/3.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.42/3.02  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.42/3.02  tff('#skF_6', type, '#skF_6': $i).
% 9.42/3.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.42/3.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.42/3.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.42/3.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.42/3.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.42/3.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.42/3.02  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.42/3.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.42/3.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.42/3.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.42/3.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.42/3.02  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.42/3.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.42/3.02  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.42/3.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.42/3.02  
% 9.42/3.03  tff(f_98, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 9.42/3.03  tff(f_117, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 9.42/3.03  tff(f_50, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 9.42/3.03  tff(f_103, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 9.42/3.03  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 9.42/3.03  tff(f_106, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.42/3.03  tff(f_81, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.42/3.03  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.42/3.03  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.42/3.03  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.42/3.03  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.42/3.03  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.42/3.03  tff(f_58, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 9.42/3.03  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.42/3.03  tff(f_62, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.42/3.03  tff(f_83, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.42/3.03  tff(f_100, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.42/3.03  tff(f_112, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.42/3.03  tff(c_74, plain, (![A_56]: (k2_subset_1(A_56)=A_56)), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.42/3.03  tff(c_84, plain, (k4_subset_1('#skF_6', '#skF_7', k2_subset_1('#skF_6'))!=k2_subset_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.42/3.03  tff(c_88, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_84])).
% 9.42/3.03  tff(c_32, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.42/3.03  tff(c_78, plain, (![A_58]: (m1_subset_1('#skF_5'(A_58), A_58))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.42/3.03  tff(c_68, plain, (![B_55, A_54]: (r2_hidden(B_55, A_54) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.42/3.03  tff(c_86, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.42/3.03  tff(c_80, plain, (![A_60]: (~v1_xboole_0(k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.42/3.03  tff(c_418, plain, (![B_107, A_108]: (r2_hidden(B_107, A_108) | ~m1_subset_1(B_107, A_108) | v1_xboole_0(A_108))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.42/3.03  tff(c_52, plain, (![C_51, A_47]: (r1_tarski(C_51, A_47) | ~r2_hidden(C_51, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.42/3.03  tff(c_422, plain, (![B_107, A_47]: (r1_tarski(B_107, A_47) | ~m1_subset_1(B_107, k1_zfmisc_1(A_47)) | v1_xboole_0(k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_418, c_52])).
% 9.42/3.03  tff(c_441, plain, (![B_113, A_114]: (r1_tarski(B_113, A_114) | ~m1_subset_1(B_113, k1_zfmisc_1(A_114)))), inference(negUnitSimplification, [status(thm)], [c_80, c_422])).
% 9.42/3.03  tff(c_460, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_86, c_441])).
% 9.42/3.03  tff(c_30, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.42/3.03  tff(c_467, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_460, c_30])).
% 9.42/3.03  tff(c_28, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.42/3.03  tff(c_471, plain, (k5_xboole_0('#skF_7', '#skF_7')=k4_xboole_0('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_467, c_28])).
% 9.42/3.03  tff(c_26, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.42/3.03  tff(c_156, plain, (![A_77, B_78]: (k3_xboole_0(A_77, B_78)=A_77 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.42/3.03  tff(c_160, plain, (![B_8]: (k3_xboole_0(B_8, B_8)=B_8)), inference(resolution, [status(thm)], [c_26, c_156])).
% 9.42/3.03  tff(c_352, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.42/3.03  tff(c_361, plain, (![B_8]: (k5_xboole_0(B_8, B_8)=k4_xboole_0(B_8, B_8))), inference(superposition, [status(thm), theory('equality')], [c_160, c_352])).
% 9.42/3.03  tff(c_496, plain, (k4_xboole_0('#skF_7', '#skF_7')=k4_xboole_0('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_471, c_361])).
% 9.42/3.03  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.42/3.03  tff(c_566, plain, (![D_129]: (~r2_hidden(D_129, '#skF_7') | ~r2_hidden(D_129, k4_xboole_0('#skF_7', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_496, c_4])).
% 9.42/3.03  tff(c_571, plain, (![B_55]: (~r2_hidden(B_55, '#skF_7') | ~m1_subset_1(B_55, k4_xboole_0('#skF_7', '#skF_6')) | v1_xboole_0(k4_xboole_0('#skF_7', '#skF_6')))), inference(resolution, [status(thm)], [c_68, c_566])).
% 9.42/3.03  tff(c_576, plain, (![B_131]: (~r2_hidden(B_131, '#skF_7') | ~m1_subset_1(B_131, k4_xboole_0('#skF_7', '#skF_6')))), inference(splitLeft, [status(thm)], [c_571])).
% 9.42/3.03  tff(c_586, plain, (~r2_hidden('#skF_5'(k4_xboole_0('#skF_7', '#skF_6')), '#skF_7')), inference(resolution, [status(thm)], [c_78, c_576])).
% 9.42/3.03  tff(c_70, plain, (![B_55, A_54]: (m1_subset_1(B_55, A_54) | ~v1_xboole_0(B_55) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.42/3.03  tff(c_585, plain, (![B_55]: (~r2_hidden(B_55, '#skF_7') | ~v1_xboole_0(B_55) | ~v1_xboole_0(k4_xboole_0('#skF_7', '#skF_6')))), inference(resolution, [status(thm)], [c_70, c_576])).
% 9.42/3.03  tff(c_614, plain, (~v1_xboole_0(k4_xboole_0('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_585])).
% 9.42/3.03  tff(c_483, plain, (![D_116, A_117, B_118]: (r2_hidden(D_116, A_117) | ~r2_hidden(D_116, k4_xboole_0(A_117, B_118)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.42/3.03  tff(c_2510, plain, (![B_206, A_207, B_208]: (r2_hidden(B_206, A_207) | ~m1_subset_1(B_206, k4_xboole_0(A_207, B_208)) | v1_xboole_0(k4_xboole_0(A_207, B_208)))), inference(resolution, [status(thm)], [c_68, c_483])).
% 9.42/3.03  tff(c_2513, plain, (![B_206]: (r2_hidden(B_206, '#skF_7') | ~m1_subset_1(B_206, k4_xboole_0('#skF_7', '#skF_6')) | v1_xboole_0(k4_xboole_0('#skF_7', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_496, c_2510])).
% 9.42/3.03  tff(c_2525, plain, (![B_206]: (r2_hidden(B_206, '#skF_7') | ~m1_subset_1(B_206, k4_xboole_0('#skF_7', '#skF_6')) | v1_xboole_0(k4_xboole_0('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_496, c_2513])).
% 9.42/3.03  tff(c_2530, plain, (![B_209]: (r2_hidden(B_209, '#skF_7') | ~m1_subset_1(B_209, k4_xboole_0('#skF_7', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_614, c_2525])).
% 9.42/3.03  tff(c_2538, plain, (r2_hidden('#skF_5'(k4_xboole_0('#skF_7', '#skF_6')), '#skF_7')), inference(resolution, [status(thm)], [c_78, c_2530])).
% 9.42/3.03  tff(c_2543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_586, c_2538])).
% 9.42/3.03  tff(c_2545, plain, (v1_xboole_0(k4_xboole_0('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_585])).
% 9.42/3.03  tff(c_20, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.42/3.03  tff(c_145, plain, (![B_72, A_73]: (~v1_xboole_0(B_72) | B_72=A_73 | ~v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.42/3.03  tff(c_148, plain, (![A_73]: (k1_xboole_0=A_73 | ~v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_20, c_145])).
% 9.42/3.03  tff(c_2564, plain, (k4_xboole_0('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_2545, c_148])).
% 9.42/3.03  tff(c_36, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.42/3.03  tff(c_2587, plain, (k5_xboole_0('#skF_6', k1_xboole_0)=k2_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2564, c_36])).
% 9.42/3.03  tff(c_2590, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2587])).
% 9.42/3.03  tff(c_38, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.42/3.03  tff(c_276, plain, (![A_90, B_91]: (k3_tarski(k2_tarski(A_90, B_91))=k2_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.42/3.03  tff(c_296, plain, (![A_94, B_95]: (k3_tarski(k2_tarski(A_94, B_95))=k2_xboole_0(B_95, A_94))), inference(superposition, [status(thm), theory('equality')], [c_38, c_276])).
% 9.42/3.03  tff(c_64, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.42/3.03  tff(c_302, plain, (![B_95, A_94]: (k2_xboole_0(B_95, A_94)=k2_xboole_0(A_94, B_95))), inference(superposition, [status(thm), theory('equality')], [c_296, c_64])).
% 9.42/3.03  tff(c_76, plain, (![A_57]: (m1_subset_1(k2_subset_1(A_57), k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.42/3.03  tff(c_87, plain, (![A_57]: (m1_subset_1(A_57, k1_zfmisc_1(A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76])).
% 9.42/3.03  tff(c_5293, plain, (![A_324, B_325, C_326]: (k4_subset_1(A_324, B_325, C_326)=k2_xboole_0(B_325, C_326) | ~m1_subset_1(C_326, k1_zfmisc_1(A_324)) | ~m1_subset_1(B_325, k1_zfmisc_1(A_324)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.42/3.03  tff(c_6542, plain, (![A_397, B_398]: (k4_subset_1(A_397, B_398, A_397)=k2_xboole_0(B_398, A_397) | ~m1_subset_1(B_398, k1_zfmisc_1(A_397)))), inference(resolution, [status(thm)], [c_87, c_5293])).
% 9.42/3.03  tff(c_6557, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')=k2_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_86, c_6542])).
% 9.42/3.03  tff(c_6568, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2590, c_302, c_6557])).
% 9.42/3.03  tff(c_6570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_6568])).
% 9.42/3.03  tff(c_6571, plain, (v1_xboole_0(k4_xboole_0('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_571])).
% 9.42/3.03  tff(c_6587, plain, (k4_xboole_0('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_6571, c_148])).
% 9.42/3.03  tff(c_6605, plain, (k5_xboole_0('#skF_6', k1_xboole_0)=k2_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6587, c_36])).
% 9.42/3.03  tff(c_6608, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6605])).
% 9.42/3.03  tff(c_11512, plain, (![A_617, B_618, C_619]: (k4_subset_1(A_617, B_618, C_619)=k2_xboole_0(B_618, C_619) | ~m1_subset_1(C_619, k1_zfmisc_1(A_617)) | ~m1_subset_1(B_618, k1_zfmisc_1(A_617)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.42/3.03  tff(c_12634, plain, (![A_693, B_694]: (k4_subset_1(A_693, B_694, A_693)=k2_xboole_0(B_694, A_693) | ~m1_subset_1(B_694, k1_zfmisc_1(A_693)))), inference(resolution, [status(thm)], [c_87, c_11512])).
% 9.42/3.03  tff(c_12649, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')=k2_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_86, c_12634])).
% 9.42/3.03  tff(c_12660, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6608, c_302, c_12649])).
% 9.42/3.03  tff(c_12662, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_12660])).
% 9.42/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.42/3.03  
% 9.42/3.03  Inference rules
% 9.42/3.03  ----------------------
% 9.42/3.03  #Ref     : 0
% 9.42/3.03  #Sup     : 3137
% 9.42/3.03  #Fact    : 0
% 9.42/3.03  #Define  : 0
% 9.42/3.03  #Split   : 18
% 9.42/3.03  #Chain   : 0
% 9.42/3.03  #Close   : 0
% 9.42/3.03  
% 9.42/3.03  Ordering : KBO
% 9.42/3.03  
% 9.42/3.03  Simplification rules
% 9.42/3.03  ----------------------
% 9.42/3.03  #Subsume      : 997
% 9.42/3.03  #Demod        : 1863
% 9.42/3.03  #Tautology    : 1051
% 9.42/3.03  #SimpNegUnit  : 56
% 9.42/3.03  #BackRed      : 165
% 9.42/3.03  
% 9.42/3.03  #Partial instantiations: 0
% 9.42/3.03  #Strategies tried      : 1
% 9.42/3.03  
% 9.42/3.03  Timing (in seconds)
% 9.42/3.03  ----------------------
% 9.42/3.04  Preprocessing        : 0.37
% 9.42/3.04  Parsing              : 0.19
% 9.42/3.04  CNF conversion       : 0.03
% 9.42/3.04  Main loop            : 1.93
% 9.42/3.04  Inferencing          : 0.60
% 9.42/3.04  Reduction            : 0.65
% 9.42/3.04  Demodulation         : 0.46
% 9.42/3.04  BG Simplification    : 0.07
% 9.42/3.04  Subsumption          : 0.47
% 9.42/3.04  Abstraction          : 0.08
% 9.42/3.04  MUC search           : 0.00
% 9.42/3.04  Cooper               : 0.00
% 9.42/3.04  Total                : 2.35
% 9.42/3.04  Index Insertion      : 0.00
% 9.42/3.04  Index Deletion       : 0.00
% 9.42/3.04  Index Matching       : 0.00
% 9.42/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
