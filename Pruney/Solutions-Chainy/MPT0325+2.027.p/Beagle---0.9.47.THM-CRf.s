%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:24 EST 2020

% Result     : Theorem 7.99s
% Output     : CNFRefutation 7.99s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 333 expanded)
%              Number of leaves         :   27 ( 121 expanded)
%              Depth                    :   17
%              Number of atoms          :  181 ( 603 expanded)
%              Number of equality atoms :   74 ( 243 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_56,plain,
    ( ~ r1_tarski('#skF_5','#skF_7')
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_85,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_99,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_30,c_91])).

tff(c_113,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_125,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_113])).

tff(c_165,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_180,plain,(
    ! [B_13] : k4_xboole_0(B_13,k1_xboole_0) = k3_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_165])).

tff(c_183,plain,(
    ! [B_13] : k4_xboole_0(B_13,k1_xboole_0) = B_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_180])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    ! [B_21] : k2_zfmisc_1(k1_xboole_0,B_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_564,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_tarski(k2_zfmisc_1(A_83,C_84),k2_zfmisc_1(B_85,C_84))
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_604,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k2_zfmisc_1(A_86,B_87),k1_xboole_0)
      | ~ r1_tarski(A_86,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_564])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_614,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(k2_zfmisc_1(A_86,B_87),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_86,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_604,c_34])).

tff(c_636,plain,(
    ! [A_88,B_89] :
      ( k2_zfmisc_1(A_88,B_89) = k1_xboole_0
      | ~ r1_tarski(A_88,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_614])).

tff(c_646,plain,(
    ! [A_14,B_89] :
      ( k2_zfmisc_1(A_14,B_89) = k1_xboole_0
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_636])).

tff(c_660,plain,(
    ! [A_90,B_91] :
      ( k2_zfmisc_1(A_90,B_91) = k1_xboole_0
      | k1_xboole_0 != A_90 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_646])).

tff(c_58,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_738,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_58])).

tff(c_1273,plain,(
    ! [A_124,C_125,B_126,D_127] : k3_xboole_0(k2_zfmisc_1(A_124,C_125),k2_zfmisc_1(B_126,D_127)) = k2_zfmisc_1(k3_xboole_0(A_124,B_126),k3_xboole_0(C_125,D_127)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_60,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_103,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_36])).

tff(c_1288,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1273,c_103])).

tff(c_52,plain,(
    ! [A_25,C_27,B_26] :
      ( r1_tarski(k2_zfmisc_1(A_25,C_27),k2_zfmisc_1(B_26,C_27))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5458,plain,(
    ! [A_257] :
      ( r1_tarski(k2_zfmisc_1(A_257,k3_xboole_0('#skF_5','#skF_7')),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_257,k3_xboole_0('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1288,c_52])).

tff(c_46,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_tarski(k2_zfmisc_1(A_22,B_23),k2_zfmisc_1(A_22,C_24))
      | r1_tarski(B_23,C_24)
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5474,plain,
    ( r1_tarski(k3_xboole_0('#skF_5','#skF_7'),'#skF_5')
    | k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4',k3_xboole_0('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_5458,c_46])).

tff(c_5540,plain,
    ( r1_tarski(k3_xboole_0('#skF_5','#skF_7'),'#skF_5')
    | ~ r1_tarski('#skF_4',k3_xboole_0('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_738,c_5474])).

tff(c_6054,plain,(
    ~ r1_tarski('#skF_4',k3_xboole_0('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5540])).

tff(c_244,plain,(
    ! [D_58,A_59,B_60] :
      ( r2_hidden(D_58,A_59)
      | ~ r2_hidden(D_58,k3_xboole_0(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6842,plain,(
    ! [A_293,B_294,B_295] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_293,B_294),B_295),A_293)
      | r1_tarski(k3_xboole_0(A_293,B_294),B_295) ) ),
    inference(resolution,[status(thm)],[c_6,c_244])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6910,plain,(
    ! [A_293,B_294] : r1_tarski(k3_xboole_0(A_293,B_294),A_293) ),
    inference(resolution,[status(thm)],[c_6842,c_4])).

tff(c_404,plain,(
    ! [C_73,A_74,B_75] :
      ( r1_tarski(k2_zfmisc_1(C_73,A_74),k2_zfmisc_1(C_73,B_75))
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_426,plain,(
    ! [C_73,A_74,B_75] :
      ( k4_xboole_0(k2_zfmisc_1(C_73,A_74),k2_zfmisc_1(C_73,B_75)) = k1_xboole_0
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_404,c_34])).

tff(c_42,plain,(
    ! [A_20] : k2_zfmisc_1(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_451,plain,(
    ! [A_77,A_78] :
      ( r1_tarski(k2_zfmisc_1(A_77,A_78),k1_xboole_0)
      | ~ r1_tarski(A_78,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_404])).

tff(c_459,plain,(
    ! [A_77,A_78] :
      ( k4_xboole_0(k2_zfmisc_1(A_77,A_78),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_78,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_451,c_34])).

tff(c_480,plain,(
    ! [A_79,A_80] :
      ( k2_zfmisc_1(A_79,A_80) = k1_xboole_0
      | ~ r1_tarski(A_80,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_459])).

tff(c_488,plain,(
    ! [A_79,A_14] :
      ( k2_zfmisc_1(A_79,A_14) = k1_xboole_0
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_480])).

tff(c_496,plain,(
    ! [A_79,A_14] :
      ( k2_zfmisc_1(A_79,A_14) = k1_xboole_0
      | k1_xboole_0 != A_14 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_488])).

tff(c_1760,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
    | k3_xboole_0('#skF_5','#skF_7') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1288,c_496])).

tff(c_1796,plain,(
    k3_xboole_0('#skF_5','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1760])).

tff(c_1012,plain,(
    ! [B_107,A_108,C_109] :
      ( ~ r1_tarski(k2_zfmisc_1(B_107,A_108),k2_zfmisc_1(C_109,A_108))
      | r1_tarski(B_107,C_109)
      | k1_xboole_0 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8956,plain,(
    ! [B_322,C_323,A_324] :
      ( r1_tarski(B_322,C_323)
      | k1_xboole_0 = A_324
      | k4_xboole_0(k2_zfmisc_1(B_322,A_324),k2_zfmisc_1(C_323,A_324)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_1012])).

tff(c_9031,plain,(
    ! [B_322] :
      ( r1_tarski(B_322,k3_xboole_0('#skF_4','#skF_6'))
      | k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0
      | k4_xboole_0(k2_zfmisc_1(B_322,k3_xboole_0('#skF_5','#skF_7')),k2_zfmisc_1('#skF_4','#skF_5')) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1288,c_8956])).

tff(c_9388,plain,(
    ! [B_328] :
      ( r1_tarski(B_328,k3_xboole_0('#skF_4','#skF_6'))
      | k4_xboole_0(k2_zfmisc_1(B_328,k3_xboole_0('#skF_5','#skF_7')),k2_zfmisc_1('#skF_4','#skF_5')) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_1796,c_9031])).

tff(c_9407,plain,
    ( r1_tarski('#skF_4',k3_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski(k3_xboole_0('#skF_5','#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_9388])).

tff(c_9475,plain,(
    r1_tarski('#skF_4',k3_xboole_0('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6910,c_9407])).

tff(c_9477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6054,c_9475])).

tff(c_9479,plain,(
    r1_tarski('#skF_4',k3_xboole_0('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5540])).

tff(c_9563,plain,(
    k3_xboole_0('#skF_4',k3_xboole_0('#skF_4','#skF_6')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9479,c_36])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12465,plain,(
    ! [D_370] :
      ( r2_hidden(D_370,k3_xboole_0('#skF_4','#skF_6'))
      | ~ r2_hidden(D_370,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9563,c_10])).

tff(c_12514,plain,(
    ! [D_371] :
      ( r2_hidden(D_371,'#skF_6')
      | ~ r2_hidden(D_371,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12465,c_10])).

tff(c_12660,plain,(
    ! [A_373] :
      ( r1_tarski(A_373,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_373,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12514,c_4])).

tff(c_12676,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_12660])).

tff(c_12683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_85,c_12676])).

tff(c_12684,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_12723,plain,(
    ! [A_379,B_380] :
      ( k3_xboole_0(A_379,B_380) = A_379
      | ~ r1_tarski(A_379,B_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12739,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_30,c_12723])).

tff(c_12691,plain,(
    ! [A_376,B_377] :
      ( k4_xboole_0(A_376,B_377) = k1_xboole_0
      | ~ r1_tarski(A_376,B_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12707,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_12691])).

tff(c_12754,plain,(
    ! [A_384,B_385] : k4_xboole_0(A_384,k4_xboole_0(A_384,B_385)) = k3_xboole_0(A_384,B_385) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12769,plain,(
    ! [B_13] : k4_xboole_0(B_13,k1_xboole_0) = k3_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_12707,c_12754])).

tff(c_12778,plain,(
    ! [B_13] : k4_xboole_0(B_13,k1_xboole_0) = B_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12739,c_12769])).

tff(c_13301,plain,(
    ! [A_425,C_426,B_427] :
      ( r1_tarski(k2_zfmisc_1(A_425,C_426),k2_zfmisc_1(B_427,C_426))
      | ~ r1_tarski(A_425,B_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_13360,plain,(
    ! [A_431,B_432] :
      ( r1_tarski(k2_zfmisc_1(A_431,B_432),k1_xboole_0)
      | ~ r1_tarski(A_431,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_13301])).

tff(c_13373,plain,(
    ! [A_431,B_432] :
      ( k4_xboole_0(k2_zfmisc_1(A_431,B_432),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_431,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_13360,c_34])).

tff(c_13392,plain,(
    ! [A_433,B_434] :
      ( k2_zfmisc_1(A_433,B_434) = k1_xboole_0
      | ~ r1_tarski(A_433,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12778,c_13373])).

tff(c_13402,plain,(
    ! [A_14,B_434] :
      ( k2_zfmisc_1(A_14,B_434) = k1_xboole_0
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_13392])).

tff(c_13416,plain,(
    ! [A_435,B_436] :
      ( k2_zfmisc_1(A_435,B_436) = k1_xboole_0
      | k1_xboole_0 != A_435 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12778,c_13402])).

tff(c_13506,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_13416,c_58])).

tff(c_12685,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_12738,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12685,c_12723])).

tff(c_14000,plain,(
    ! [A_465,C_466,B_467,D_468] : k3_xboole_0(k2_zfmisc_1(A_465,C_466),k2_zfmisc_1(B_467,D_468)) = k2_zfmisc_1(k3_xboole_0(A_465,B_467),k3_xboole_0(C_466,D_468)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12737,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_12723])).

tff(c_14021,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14000,c_12737])).

tff(c_14055,plain,(
    k2_zfmisc_1('#skF_4',k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12738,c_14021])).

tff(c_14076,plain,(
    ! [B_23] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4',B_23),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_23,k3_xboole_0('#skF_5','#skF_7'))
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14055,c_46])).

tff(c_14143,plain,(
    ! [B_469] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4',B_469),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_469,k3_xboole_0('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13506,c_14076])).

tff(c_14160,plain,
    ( r1_tarski('#skF_5',k3_xboole_0('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_14143])).

tff(c_14186,plain,(
    r1_tarski('#skF_5',k3_xboole_0('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_14160])).

tff(c_14215,plain,(
    k3_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_7')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14186,c_36])).

tff(c_14334,plain,(
    ! [D_474] :
      ( r2_hidden(D_474,k3_xboole_0('#skF_5','#skF_7'))
      | ~ r2_hidden(D_474,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14215,c_10])).

tff(c_14365,plain,(
    ! [D_475] :
      ( r2_hidden(D_475,'#skF_7')
      | ~ r2_hidden(D_475,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14334,c_10])).

tff(c_14552,plain,(
    ! [A_480] :
      ( r1_tarski(A_480,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_480,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14365,c_4])).

tff(c_14556,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_14552])).

tff(c_14560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12684,c_12684,c_14556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:17:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.99/2.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.99/2.78  
% 7.99/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.99/2.78  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.99/2.78  
% 7.99/2.78  %Foreground sorts:
% 7.99/2.78  
% 7.99/2.78  
% 7.99/2.78  %Background operators:
% 7.99/2.78  
% 7.99/2.78  
% 7.99/2.78  %Foreground operators:
% 7.99/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.99/2.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.99/2.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.99/2.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.99/2.78  tff('#skF_7', type, '#skF_7': $i).
% 7.99/2.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.99/2.78  tff('#skF_5', type, '#skF_5': $i).
% 7.99/2.78  tff('#skF_6', type, '#skF_6': $i).
% 7.99/2.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.99/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.99/2.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.99/2.78  tff('#skF_4', type, '#skF_4': $i).
% 7.99/2.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.99/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.99/2.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.99/2.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.99/2.78  
% 7.99/2.80  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 7.99/2.80  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.99/2.80  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.99/2.80  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.99/2.80  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.99/2.80  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.99/2.80  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.99/2.80  tff(f_80, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 7.99/2.80  tff(f_82, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 7.99/2.80  tff(f_74, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 7.99/2.80  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.99/2.81  tff(c_56, plain, (~r1_tarski('#skF_5', '#skF_7') | ~r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.99/2.81  tff(c_85, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_56])).
% 7.99/2.81  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.99/2.81  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.99/2.81  tff(c_91, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.99/2.81  tff(c_99, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_30, c_91])).
% 7.99/2.81  tff(c_113, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.99/2.81  tff(c_125, plain, (![B_13]: (k4_xboole_0(B_13, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_113])).
% 7.99/2.81  tff(c_165, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.99/2.81  tff(c_180, plain, (![B_13]: (k4_xboole_0(B_13, k1_xboole_0)=k3_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_125, c_165])).
% 7.99/2.81  tff(c_183, plain, (![B_13]: (k4_xboole_0(B_13, k1_xboole_0)=B_13)), inference(demodulation, [status(thm), theory('equality')], [c_99, c_180])).
% 7.99/2.81  tff(c_32, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.99/2.81  tff(c_44, plain, (![B_21]: (k2_zfmisc_1(k1_xboole_0, B_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.99/2.81  tff(c_564, plain, (![A_83, C_84, B_85]: (r1_tarski(k2_zfmisc_1(A_83, C_84), k2_zfmisc_1(B_85, C_84)) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.99/2.81  tff(c_604, plain, (![A_86, B_87]: (r1_tarski(k2_zfmisc_1(A_86, B_87), k1_xboole_0) | ~r1_tarski(A_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_564])).
% 7.99/2.81  tff(c_34, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.99/2.81  tff(c_614, plain, (![A_86, B_87]: (k4_xboole_0(k2_zfmisc_1(A_86, B_87), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_86, k1_xboole_0))), inference(resolution, [status(thm)], [c_604, c_34])).
% 7.99/2.81  tff(c_636, plain, (![A_88, B_89]: (k2_zfmisc_1(A_88, B_89)=k1_xboole_0 | ~r1_tarski(A_88, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_614])).
% 7.99/2.81  tff(c_646, plain, (![A_14, B_89]: (k2_zfmisc_1(A_14, B_89)=k1_xboole_0 | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_636])).
% 7.99/2.81  tff(c_660, plain, (![A_90, B_91]: (k2_zfmisc_1(A_90, B_91)=k1_xboole_0 | k1_xboole_0!=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_646])).
% 7.99/2.81  tff(c_58, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.99/2.81  tff(c_738, plain, (k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_660, c_58])).
% 7.99/2.81  tff(c_1273, plain, (![A_124, C_125, B_126, D_127]: (k3_xboole_0(k2_zfmisc_1(A_124, C_125), k2_zfmisc_1(B_126, D_127))=k2_zfmisc_1(k3_xboole_0(A_124, B_126), k3_xboole_0(C_125, D_127)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.99/2.81  tff(c_60, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.99/2.81  tff(c_36, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.99/2.81  tff(c_103, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_36])).
% 7.99/2.81  tff(c_1288, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1273, c_103])).
% 7.99/2.81  tff(c_52, plain, (![A_25, C_27, B_26]: (r1_tarski(k2_zfmisc_1(A_25, C_27), k2_zfmisc_1(B_26, C_27)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.99/2.81  tff(c_5458, plain, (![A_257]: (r1_tarski(k2_zfmisc_1(A_257, k3_xboole_0('#skF_5', '#skF_7')), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_257, k3_xboole_0('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1288, c_52])).
% 7.99/2.81  tff(c_46, plain, (![A_22, B_23, C_24]: (~r1_tarski(k2_zfmisc_1(A_22, B_23), k2_zfmisc_1(A_22, C_24)) | r1_tarski(B_23, C_24) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.99/2.81  tff(c_5474, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5') | k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_5458, c_46])).
% 7.99/2.81  tff(c_5540, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5') | ~r1_tarski('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_738, c_5474])).
% 7.99/2.81  tff(c_6054, plain, (~r1_tarski('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_5540])).
% 7.99/2.81  tff(c_244, plain, (![D_58, A_59, B_60]: (r2_hidden(D_58, A_59) | ~r2_hidden(D_58, k3_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.99/2.81  tff(c_6842, plain, (![A_293, B_294, B_295]: (r2_hidden('#skF_1'(k3_xboole_0(A_293, B_294), B_295), A_293) | r1_tarski(k3_xboole_0(A_293, B_294), B_295))), inference(resolution, [status(thm)], [c_6, c_244])).
% 7.99/2.81  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.99/2.81  tff(c_6910, plain, (![A_293, B_294]: (r1_tarski(k3_xboole_0(A_293, B_294), A_293))), inference(resolution, [status(thm)], [c_6842, c_4])).
% 7.99/2.81  tff(c_404, plain, (![C_73, A_74, B_75]: (r1_tarski(k2_zfmisc_1(C_73, A_74), k2_zfmisc_1(C_73, B_75)) | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.99/2.81  tff(c_426, plain, (![C_73, A_74, B_75]: (k4_xboole_0(k2_zfmisc_1(C_73, A_74), k2_zfmisc_1(C_73, B_75))=k1_xboole_0 | ~r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_404, c_34])).
% 7.99/2.81  tff(c_42, plain, (![A_20]: (k2_zfmisc_1(A_20, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.99/2.81  tff(c_451, plain, (![A_77, A_78]: (r1_tarski(k2_zfmisc_1(A_77, A_78), k1_xboole_0) | ~r1_tarski(A_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_404])).
% 7.99/2.81  tff(c_459, plain, (![A_77, A_78]: (k4_xboole_0(k2_zfmisc_1(A_77, A_78), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_78, k1_xboole_0))), inference(resolution, [status(thm)], [c_451, c_34])).
% 7.99/2.81  tff(c_480, plain, (![A_79, A_80]: (k2_zfmisc_1(A_79, A_80)=k1_xboole_0 | ~r1_tarski(A_80, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_459])).
% 7.99/2.81  tff(c_488, plain, (![A_79, A_14]: (k2_zfmisc_1(A_79, A_14)=k1_xboole_0 | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_480])).
% 7.99/2.81  tff(c_496, plain, (![A_79, A_14]: (k2_zfmisc_1(A_79, A_14)=k1_xboole_0 | k1_xboole_0!=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_488])).
% 7.99/2.81  tff(c_1760, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_xboole_0('#skF_5', '#skF_7')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1288, c_496])).
% 7.99/2.81  tff(c_1796, plain, (k3_xboole_0('#skF_5', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_1760])).
% 7.99/2.81  tff(c_1012, plain, (![B_107, A_108, C_109]: (~r1_tarski(k2_zfmisc_1(B_107, A_108), k2_zfmisc_1(C_109, A_108)) | r1_tarski(B_107, C_109) | k1_xboole_0=A_108)), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.99/2.81  tff(c_8956, plain, (![B_322, C_323, A_324]: (r1_tarski(B_322, C_323) | k1_xboole_0=A_324 | k4_xboole_0(k2_zfmisc_1(B_322, A_324), k2_zfmisc_1(C_323, A_324))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_1012])).
% 7.99/2.81  tff(c_9031, plain, (![B_322]: (r1_tarski(B_322, k3_xboole_0('#skF_4', '#skF_6')) | k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0 | k4_xboole_0(k2_zfmisc_1(B_322, k3_xboole_0('#skF_5', '#skF_7')), k2_zfmisc_1('#skF_4', '#skF_5'))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1288, c_8956])).
% 7.99/2.81  tff(c_9388, plain, (![B_328]: (r1_tarski(B_328, k3_xboole_0('#skF_4', '#skF_6')) | k4_xboole_0(k2_zfmisc_1(B_328, k3_xboole_0('#skF_5', '#skF_7')), k2_zfmisc_1('#skF_4', '#skF_5'))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1796, c_9031])).
% 7.99/2.81  tff(c_9407, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_426, c_9388])).
% 7.99/2.81  tff(c_9475, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6910, c_9407])).
% 7.99/2.81  tff(c_9477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6054, c_9475])).
% 7.99/2.81  tff(c_9479, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_5540])).
% 7.99/2.81  tff(c_9563, plain, (k3_xboole_0('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))='#skF_4'), inference(resolution, [status(thm)], [c_9479, c_36])).
% 7.99/2.81  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.99/2.81  tff(c_12465, plain, (![D_370]: (r2_hidden(D_370, k3_xboole_0('#skF_4', '#skF_6')) | ~r2_hidden(D_370, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9563, c_10])).
% 7.99/2.81  tff(c_12514, plain, (![D_371]: (r2_hidden(D_371, '#skF_6') | ~r2_hidden(D_371, '#skF_4'))), inference(resolution, [status(thm)], [c_12465, c_10])).
% 7.99/2.81  tff(c_12660, plain, (![A_373]: (r1_tarski(A_373, '#skF_6') | ~r2_hidden('#skF_1'(A_373, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_12514, c_4])).
% 7.99/2.81  tff(c_12676, plain, (r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_12660])).
% 7.99/2.81  tff(c_12683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_85, c_12676])).
% 7.99/2.81  tff(c_12684, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 7.99/2.81  tff(c_12723, plain, (![A_379, B_380]: (k3_xboole_0(A_379, B_380)=A_379 | ~r1_tarski(A_379, B_380))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.99/2.81  tff(c_12739, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_30, c_12723])).
% 7.99/2.81  tff(c_12691, plain, (![A_376, B_377]: (k4_xboole_0(A_376, B_377)=k1_xboole_0 | ~r1_tarski(A_376, B_377))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.99/2.81  tff(c_12707, plain, (![B_13]: (k4_xboole_0(B_13, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_12691])).
% 7.99/2.81  tff(c_12754, plain, (![A_384, B_385]: (k4_xboole_0(A_384, k4_xboole_0(A_384, B_385))=k3_xboole_0(A_384, B_385))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.99/2.81  tff(c_12769, plain, (![B_13]: (k4_xboole_0(B_13, k1_xboole_0)=k3_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_12707, c_12754])).
% 7.99/2.81  tff(c_12778, plain, (![B_13]: (k4_xboole_0(B_13, k1_xboole_0)=B_13)), inference(demodulation, [status(thm), theory('equality')], [c_12739, c_12769])).
% 7.99/2.81  tff(c_13301, plain, (![A_425, C_426, B_427]: (r1_tarski(k2_zfmisc_1(A_425, C_426), k2_zfmisc_1(B_427, C_426)) | ~r1_tarski(A_425, B_427))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.99/2.81  tff(c_13360, plain, (![A_431, B_432]: (r1_tarski(k2_zfmisc_1(A_431, B_432), k1_xboole_0) | ~r1_tarski(A_431, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_13301])).
% 7.99/2.81  tff(c_13373, plain, (![A_431, B_432]: (k4_xboole_0(k2_zfmisc_1(A_431, B_432), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_431, k1_xboole_0))), inference(resolution, [status(thm)], [c_13360, c_34])).
% 7.99/2.81  tff(c_13392, plain, (![A_433, B_434]: (k2_zfmisc_1(A_433, B_434)=k1_xboole_0 | ~r1_tarski(A_433, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12778, c_13373])).
% 7.99/2.81  tff(c_13402, plain, (![A_14, B_434]: (k2_zfmisc_1(A_14, B_434)=k1_xboole_0 | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_13392])).
% 7.99/2.81  tff(c_13416, plain, (![A_435, B_436]: (k2_zfmisc_1(A_435, B_436)=k1_xboole_0 | k1_xboole_0!=A_435)), inference(demodulation, [status(thm), theory('equality')], [c_12778, c_13402])).
% 7.99/2.81  tff(c_13506, plain, (k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_13416, c_58])).
% 7.99/2.81  tff(c_12685, plain, (r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 7.99/2.81  tff(c_12738, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_12685, c_12723])).
% 7.99/2.81  tff(c_14000, plain, (![A_465, C_466, B_467, D_468]: (k3_xboole_0(k2_zfmisc_1(A_465, C_466), k2_zfmisc_1(B_467, D_468))=k2_zfmisc_1(k3_xboole_0(A_465, B_467), k3_xboole_0(C_466, D_468)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.99/2.81  tff(c_12737, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_12723])).
% 7.99/2.81  tff(c_14021, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14000, c_12737])).
% 7.99/2.81  tff(c_14055, plain, (k2_zfmisc_1('#skF_4', k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12738, c_14021])).
% 7.99/2.81  tff(c_14076, plain, (![B_23]: (~r1_tarski(k2_zfmisc_1('#skF_4', B_23), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_23, k3_xboole_0('#skF_5', '#skF_7')) | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14055, c_46])).
% 7.99/2.81  tff(c_14143, plain, (![B_469]: (~r1_tarski(k2_zfmisc_1('#skF_4', B_469), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_469, k3_xboole_0('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_13506, c_14076])).
% 7.99/2.81  tff(c_14160, plain, (r1_tarski('#skF_5', k3_xboole_0('#skF_5', '#skF_7')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_14143])).
% 7.99/2.81  tff(c_14186, plain, (r1_tarski('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_14160])).
% 7.99/2.81  tff(c_14215, plain, (k3_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))='#skF_5'), inference(resolution, [status(thm)], [c_14186, c_36])).
% 7.99/2.81  tff(c_14334, plain, (![D_474]: (r2_hidden(D_474, k3_xboole_0('#skF_5', '#skF_7')) | ~r2_hidden(D_474, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14215, c_10])).
% 7.99/2.81  tff(c_14365, plain, (![D_475]: (r2_hidden(D_475, '#skF_7') | ~r2_hidden(D_475, '#skF_5'))), inference(resolution, [status(thm)], [c_14334, c_10])).
% 7.99/2.81  tff(c_14552, plain, (![A_480]: (r1_tarski(A_480, '#skF_7') | ~r2_hidden('#skF_1'(A_480, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_14365, c_4])).
% 7.99/2.81  tff(c_14556, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_14552])).
% 7.99/2.81  tff(c_14560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12684, c_12684, c_14556])).
% 7.99/2.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.99/2.81  
% 7.99/2.81  Inference rules
% 7.99/2.81  ----------------------
% 7.99/2.81  #Ref     : 5
% 7.99/2.81  #Sup     : 3700
% 7.99/2.81  #Fact    : 0
% 7.99/2.81  #Define  : 0
% 7.99/2.81  #Split   : 15
% 7.99/2.81  #Chain   : 0
% 7.99/2.81  #Close   : 0
% 7.99/2.81  
% 7.99/2.81  Ordering : KBO
% 7.99/2.81  
% 7.99/2.81  Simplification rules
% 7.99/2.81  ----------------------
% 7.99/2.81  #Subsume      : 1251
% 7.99/2.81  #Demod        : 1527
% 7.99/2.81  #Tautology    : 1548
% 7.99/2.81  #SimpNegUnit  : 103
% 7.99/2.81  #BackRed      : 8
% 7.99/2.81  
% 7.99/2.81  #Partial instantiations: 0
% 7.99/2.81  #Strategies tried      : 1
% 7.99/2.81  
% 7.99/2.81  Timing (in seconds)
% 7.99/2.81  ----------------------
% 7.99/2.81  Preprocessing        : 0.31
% 7.99/2.81  Parsing              : 0.16
% 7.99/2.81  CNF conversion       : 0.02
% 7.99/2.81  Main loop            : 1.71
% 7.99/2.81  Inferencing          : 0.47
% 7.99/2.81  Reduction            : 0.66
% 7.99/2.81  Demodulation         : 0.49
% 7.99/2.81  BG Simplification    : 0.05
% 7.99/2.81  Subsumption          : 0.42
% 7.99/2.81  Abstraction          : 0.08
% 7.99/2.81  MUC search           : 0.00
% 7.99/2.81  Cooper               : 0.00
% 7.99/2.81  Total                : 2.06
% 7.99/2.81  Index Insertion      : 0.00
% 7.99/2.81  Index Deletion       : 0.00
% 7.99/2.81  Index Matching       : 0.00
% 7.99/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
