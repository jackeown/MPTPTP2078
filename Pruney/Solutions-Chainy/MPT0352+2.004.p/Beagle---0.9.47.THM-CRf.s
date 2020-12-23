%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:47 EST 2020

% Result     : Theorem 9.73s
% Output     : CNFRefutation 9.73s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 148 expanded)
%              Number of leaves         :   42 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  145 ( 246 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_118,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_70,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_103,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_64,plain,(
    ! [A_50] : ~ v1_xboole_0(k1_zfmisc_1(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_756,plain,(
    ! [B_130,A_131] :
      ( r2_hidden(B_130,A_131)
      | ~ m1_subset_1(B_130,A_131)
      | v1_xboole_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_40,plain,(
    ! [C_43,A_39] :
      ( r1_tarski(C_43,A_39)
      | ~ r2_hidden(C_43,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_763,plain,(
    ! [B_130,A_39] :
      ( r1_tarski(B_130,A_39)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_39))
      | v1_xboole_0(k1_zfmisc_1(A_39)) ) ),
    inference(resolution,[status(thm)],[c_756,c_40])).

tff(c_771,plain,(
    ! [B_132,A_133] :
      ( r1_tarski(B_132,A_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_133)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_763])).

tff(c_788,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_771])).

tff(c_76,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_216,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_76])).

tff(c_941,plain,(
    ! [A_149,B_150] :
      ( k4_xboole_0(A_149,B_150) = k3_subset_1(A_149,B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(A_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_958,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_941])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_tarski(A_8,k4_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1346,plain,(
    ! [A_172] :
      ( r1_xboole_0(A_172,'#skF_4')
      | ~ r1_tarski(A_172,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_958,c_10])).

tff(c_1365,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_216,c_1346])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_xboole_0(B_5,A_4)
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1425,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1365,c_6])).

tff(c_14,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_787,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_771])).

tff(c_789,plain,(
    ! [A_134,C_135,B_136] :
      ( r1_tarski(A_134,C_135)
      | ~ r1_tarski(B_136,C_135)
      | ~ r1_tarski(A_134,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_808,plain,(
    ! [A_137] :
      ( r1_tarski(A_137,'#skF_3')
      | ~ r1_tarski(A_137,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_787,c_789])).

tff(c_824,plain,(
    ! [B_16] : r1_tarski(k4_xboole_0('#skF_5',B_16),'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_808])).

tff(c_28,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_260,plain,(
    ! [B_84,A_85] :
      ( ~ r1_xboole_0(B_84,A_85)
      | ~ r1_tarski(B_84,A_85)
      | v1_xboole_0(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1589,plain,(
    ! [A_187,B_188] :
      ( ~ r1_tarski(k4_xboole_0(A_187,B_188),B_188)
      | v1_xboole_0(k4_xboole_0(A_187,B_188)) ) ),
    inference(resolution,[status(thm)],[c_28,c_260])).

tff(c_1641,plain,(
    v1_xboole_0(k4_xboole_0('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_824,c_1589])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2029,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1641,c_4])).

tff(c_20,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2056,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2029,c_20])).

tff(c_2098,plain,(
    k2_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2056])).

tff(c_52,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    ! [B_36,A_35] : k2_tarski(B_36,A_35) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_192,plain,(
    ! [A_70,B_71] : k3_tarski(k2_tarski(A_70,B_71)) = k2_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_237,plain,(
    ! [A_82,B_83] : k3_tarski(k2_tarski(A_82,B_83)) = k2_xboole_0(B_83,A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_192])).

tff(c_249,plain,(
    ! [B_45,A_44] : k2_xboole_0(B_45,A_44) = k2_xboole_0(A_44,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_237])).

tff(c_957,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_941])).

tff(c_1070,plain,(
    ! [A_151,B_152,C_153] :
      ( r1_tarski(A_151,B_152)
      | ~ r1_xboole_0(A_151,C_153)
      | ~ r1_tarski(A_151,k2_xboole_0(B_152,C_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2108,plain,(
    ! [A_198,A_199,B_200] :
      ( r1_tarski(A_198,A_199)
      | ~ r1_xboole_0(A_198,k4_xboole_0(B_200,A_199))
      | ~ r1_tarski(A_198,k2_xboole_0(A_199,B_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1070])).

tff(c_2134,plain,(
    ! [A_198] :
      ( r1_tarski(A_198,'#skF_5')
      | ~ r1_xboole_0(A_198,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_198,k2_xboole_0('#skF_5','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_2108])).

tff(c_2182,plain,(
    ! [A_198] :
      ( r1_tarski(A_198,'#skF_5')
      | ~ r1_xboole_0(A_198,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_198,k2_xboole_0('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_2134])).

tff(c_15522,plain,(
    ! [A_427] :
      ( r1_tarski(A_427,'#skF_5')
      | ~ r1_xboole_0(A_427,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_427,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2098,c_2182])).

tff(c_15556,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1425,c_15522])).

tff(c_15600,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_15556])).

tff(c_15602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_15600])).

tff(c_15604,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_16503,plain,(
    ! [A_524,B_525] :
      ( k4_xboole_0(A_524,B_525) = k3_subset_1(A_524,B_525)
      | ~ m1_subset_1(B_525,k1_zfmisc_1(A_524)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_16519,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_16503])).

tff(c_15995,plain,(
    ! [A_472,C_473,B_474] :
      ( r1_xboole_0(A_472,k4_xboole_0(C_473,B_474))
      | ~ r1_tarski(A_472,B_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16004,plain,(
    ! [C_473,B_474,A_472] :
      ( r1_xboole_0(k4_xboole_0(C_473,B_474),A_472)
      | ~ r1_tarski(A_472,B_474) ) ),
    inference(resolution,[status(thm)],[c_15995,c_6])).

tff(c_16624,plain,(
    ! [A_472] :
      ( r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),A_472)
      | ~ r1_tarski(A_472,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16519,c_16004])).

tff(c_16660,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16519,c_18])).

tff(c_16520,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_16503])).

tff(c_16726,plain,(
    ! [A_532,B_533,C_534] :
      ( r1_tarski(A_532,k4_xboole_0(B_533,C_534))
      | ~ r1_xboole_0(A_532,C_534)
      | ~ r1_tarski(A_532,B_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_17100,plain,(
    ! [A_558] :
      ( r1_tarski(A_558,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_xboole_0(A_558,'#skF_4')
      | ~ r1_tarski(A_558,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16520,c_16726])).

tff(c_15603,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_17120,plain,
    ( ~ r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4')
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_17100,c_15603])).

tff(c_17131,plain,(
    ~ r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16660,c_17120])).

tff(c_17142,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_16624,c_17131])).

tff(c_17152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15604,c_17142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.73/3.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.73/3.65  
% 9.73/3.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.73/3.66  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 9.73/3.66  
% 9.73/3.66  %Foreground sorts:
% 9.73/3.66  
% 9.73/3.66  
% 9.73/3.66  %Background operators:
% 9.73/3.66  
% 9.73/3.66  
% 9.73/3.66  %Foreground operators:
% 9.73/3.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.73/3.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.73/3.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.73/3.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.73/3.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.73/3.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.73/3.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.73/3.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.73/3.66  tff('#skF_5', type, '#skF_5': $i).
% 9.73/3.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.73/3.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.73/3.66  tff('#skF_3', type, '#skF_3': $i).
% 9.73/3.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.73/3.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.73/3.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.73/3.66  tff('#skF_4', type, '#skF_4': $i).
% 9.73/3.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.73/3.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.73/3.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.73/3.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.73/3.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.73/3.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.73/3.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.73/3.66  
% 9.73/3.67  tff(f_128, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 9.73/3.67  tff(f_118, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.73/3.67  tff(f_111, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.73/3.67  tff(f_96, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.73/3.67  tff(f_115, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.73/3.67  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 9.73/3.67  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 9.73/3.67  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.73/3.67  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.73/3.67  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.73/3.67  tff(f_73, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.73/3.67  tff(f_65, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 9.73/3.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.73/3.67  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.73/3.67  tff(f_98, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.73/3.67  tff(f_87, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.73/3.67  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 9.73/3.67  tff(f_77, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 9.73/3.67  tff(f_83, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 9.73/3.67  tff(c_70, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.73/3.67  tff(c_103, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_70])).
% 9.73/3.67  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.73/3.67  tff(c_64, plain, (![A_50]: (~v1_xboole_0(k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.73/3.67  tff(c_756, plain, (![B_130, A_131]: (r2_hidden(B_130, A_131) | ~m1_subset_1(B_130, A_131) | v1_xboole_0(A_131))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.73/3.67  tff(c_40, plain, (![C_43, A_39]: (r1_tarski(C_43, A_39) | ~r2_hidden(C_43, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.73/3.67  tff(c_763, plain, (![B_130, A_39]: (r1_tarski(B_130, A_39) | ~m1_subset_1(B_130, k1_zfmisc_1(A_39)) | v1_xboole_0(k1_zfmisc_1(A_39)))), inference(resolution, [status(thm)], [c_756, c_40])).
% 9.73/3.67  tff(c_771, plain, (![B_132, A_133]: (r1_tarski(B_132, A_133) | ~m1_subset_1(B_132, k1_zfmisc_1(A_133)))), inference(negUnitSimplification, [status(thm)], [c_64, c_763])).
% 9.73/3.67  tff(c_788, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_771])).
% 9.73/3.67  tff(c_76, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.73/3.67  tff(c_216, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_103, c_76])).
% 9.73/3.67  tff(c_941, plain, (![A_149, B_150]: (k4_xboole_0(A_149, B_150)=k3_subset_1(A_149, B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(A_149)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.73/3.67  tff(c_958, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_941])).
% 9.73/3.67  tff(c_10, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_tarski(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.73/3.67  tff(c_1346, plain, (![A_172]: (r1_xboole_0(A_172, '#skF_4') | ~r1_tarski(A_172, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_958, c_10])).
% 9.73/3.67  tff(c_1365, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_216, c_1346])).
% 9.73/3.67  tff(c_6, plain, (![B_5, A_4]: (r1_xboole_0(B_5, A_4) | ~r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.73/3.67  tff(c_1425, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_1365, c_6])).
% 9.73/3.67  tff(c_14, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.73/3.67  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.73/3.67  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.73/3.67  tff(c_787, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_771])).
% 9.73/3.67  tff(c_789, plain, (![A_134, C_135, B_136]: (r1_tarski(A_134, C_135) | ~r1_tarski(B_136, C_135) | ~r1_tarski(A_134, B_136))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.73/3.67  tff(c_808, plain, (![A_137]: (r1_tarski(A_137, '#skF_3') | ~r1_tarski(A_137, '#skF_5'))), inference(resolution, [status(thm)], [c_787, c_789])).
% 9.73/3.67  tff(c_824, plain, (![B_16]: (r1_tarski(k4_xboole_0('#skF_5', B_16), '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_808])).
% 9.73/3.67  tff(c_28, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.73/3.67  tff(c_260, plain, (![B_84, A_85]: (~r1_xboole_0(B_84, A_85) | ~r1_tarski(B_84, A_85) | v1_xboole_0(B_84))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.73/3.67  tff(c_1589, plain, (![A_187, B_188]: (~r1_tarski(k4_xboole_0(A_187, B_188), B_188) | v1_xboole_0(k4_xboole_0(A_187, B_188)))), inference(resolution, [status(thm)], [c_28, c_260])).
% 9.73/3.67  tff(c_1641, plain, (v1_xboole_0(k4_xboole_0('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_824, c_1589])).
% 9.73/3.67  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.73/3.67  tff(c_2029, plain, (k4_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1641, c_4])).
% 9.73/3.67  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.73/3.67  tff(c_2056, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2029, c_20])).
% 9.73/3.67  tff(c_2098, plain, (k2_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2056])).
% 9.73/3.67  tff(c_52, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.73/3.67  tff(c_36, plain, (![B_36, A_35]: (k2_tarski(B_36, A_35)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.73/3.67  tff(c_192, plain, (![A_70, B_71]: (k3_tarski(k2_tarski(A_70, B_71))=k2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.73/3.67  tff(c_237, plain, (![A_82, B_83]: (k3_tarski(k2_tarski(A_82, B_83))=k2_xboole_0(B_83, A_82))), inference(superposition, [status(thm), theory('equality')], [c_36, c_192])).
% 9.73/3.67  tff(c_249, plain, (![B_45, A_44]: (k2_xboole_0(B_45, A_44)=k2_xboole_0(A_44, B_45))), inference(superposition, [status(thm), theory('equality')], [c_52, c_237])).
% 9.73/3.67  tff(c_957, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_941])).
% 9.73/3.67  tff(c_1070, plain, (![A_151, B_152, C_153]: (r1_tarski(A_151, B_152) | ~r1_xboole_0(A_151, C_153) | ~r1_tarski(A_151, k2_xboole_0(B_152, C_153)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.73/3.67  tff(c_2108, plain, (![A_198, A_199, B_200]: (r1_tarski(A_198, A_199) | ~r1_xboole_0(A_198, k4_xboole_0(B_200, A_199)) | ~r1_tarski(A_198, k2_xboole_0(A_199, B_200)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1070])).
% 9.73/3.67  tff(c_2134, plain, (![A_198]: (r1_tarski(A_198, '#skF_5') | ~r1_xboole_0(A_198, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_198, k2_xboole_0('#skF_5', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_957, c_2108])).
% 9.73/3.67  tff(c_2182, plain, (![A_198]: (r1_tarski(A_198, '#skF_5') | ~r1_xboole_0(A_198, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_198, k2_xboole_0('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_2134])).
% 9.73/3.67  tff(c_15522, plain, (![A_427]: (r1_tarski(A_427, '#skF_5') | ~r1_xboole_0(A_427, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_427, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2098, c_2182])).
% 9.73/3.67  tff(c_15556, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1425, c_15522])).
% 9.73/3.67  tff(c_15600, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_788, c_15556])).
% 9.73/3.67  tff(c_15602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_15600])).
% 9.73/3.67  tff(c_15604, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 9.73/3.67  tff(c_16503, plain, (![A_524, B_525]: (k4_xboole_0(A_524, B_525)=k3_subset_1(A_524, B_525) | ~m1_subset_1(B_525, k1_zfmisc_1(A_524)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.73/3.67  tff(c_16519, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_16503])).
% 9.73/3.67  tff(c_15995, plain, (![A_472, C_473, B_474]: (r1_xboole_0(A_472, k4_xboole_0(C_473, B_474)) | ~r1_tarski(A_472, B_474))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.73/3.67  tff(c_16004, plain, (![C_473, B_474, A_472]: (r1_xboole_0(k4_xboole_0(C_473, B_474), A_472) | ~r1_tarski(A_472, B_474))), inference(resolution, [status(thm)], [c_15995, c_6])).
% 9.73/3.67  tff(c_16624, plain, (![A_472]: (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), A_472) | ~r1_tarski(A_472, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16519, c_16004])).
% 9.73/3.67  tff(c_16660, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16519, c_18])).
% 9.73/3.67  tff(c_16520, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_16503])).
% 9.73/3.67  tff(c_16726, plain, (![A_532, B_533, C_534]: (r1_tarski(A_532, k4_xboole_0(B_533, C_534)) | ~r1_xboole_0(A_532, C_534) | ~r1_tarski(A_532, B_533))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.73/3.67  tff(c_17100, plain, (![A_558]: (r1_tarski(A_558, k3_subset_1('#skF_3', '#skF_4')) | ~r1_xboole_0(A_558, '#skF_4') | ~r1_tarski(A_558, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16520, c_16726])).
% 9.73/3.67  tff(c_15603, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_70])).
% 9.73/3.67  tff(c_17120, plain, (~r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_17100, c_15603])).
% 9.73/3.67  tff(c_17131, plain, (~r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16660, c_17120])).
% 9.73/3.67  tff(c_17142, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_16624, c_17131])).
% 9.73/3.67  tff(c_17152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15604, c_17142])).
% 9.73/3.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.73/3.67  
% 9.73/3.67  Inference rules
% 9.73/3.67  ----------------------
% 9.73/3.67  #Ref     : 0
% 9.73/3.67  #Sup     : 4071
% 9.73/3.67  #Fact    : 0
% 9.73/3.67  #Define  : 0
% 9.73/3.67  #Split   : 22
% 9.73/3.67  #Chain   : 0
% 9.73/3.67  #Close   : 0
% 9.73/3.67  
% 9.73/3.67  Ordering : KBO
% 9.73/3.67  
% 9.73/3.67  Simplification rules
% 9.73/3.67  ----------------------
% 9.73/3.67  #Subsume      : 768
% 9.73/3.67  #Demod        : 3429
% 9.73/3.67  #Tautology    : 2005
% 9.73/3.67  #SimpNegUnit  : 84
% 9.73/3.67  #BackRed      : 16
% 9.73/3.67  
% 9.73/3.67  #Partial instantiations: 0
% 9.73/3.67  #Strategies tried      : 1
% 9.73/3.67  
% 9.73/3.67  Timing (in seconds)
% 9.73/3.67  ----------------------
% 9.73/3.68  Preprocessing        : 0.36
% 9.73/3.68  Parsing              : 0.19
% 9.73/3.68  CNF conversion       : 0.02
% 9.73/3.68  Main loop            : 2.55
% 9.73/3.68  Inferencing          : 0.58
% 9.73/3.68  Reduction            : 1.20
% 9.73/3.68  Demodulation         : 0.95
% 9.73/3.68  BG Simplification    : 0.06
% 9.73/3.68  Subsumption          : 0.56
% 9.73/3.68  Abstraction          : 0.08
% 9.73/3.68  MUC search           : 0.00
% 9.73/3.68  Cooper               : 0.00
% 9.73/3.68  Total                : 2.95
% 9.73/3.68  Index Insertion      : 0.00
% 9.73/3.68  Index Deletion       : 0.00
% 9.73/3.68  Index Matching       : 0.00
% 9.73/3.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
