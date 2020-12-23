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
% DateTime   : Thu Dec  3 09:49:54 EST 2020

% Result     : Theorem 28.59s
% Output     : CNFRefutation 28.59s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 297 expanded)
%              Number of leaves         :   25 ( 105 expanded)
%              Depth                    :   10
%              Number of atoms          :  214 ( 599 expanded)
%              Number of equality atoms :   43 ( 116 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),C)
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_106,plain,(
    ! [A_35,B_36] :
      ( r2_hidden(A_35,B_36)
      | ~ r1_tarski(k1_tarski(A_35),B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_125,plain,(
    ! [A_35] : r2_hidden(A_35,k1_tarski(A_35)) ),
    inference(resolution,[status(thm)],[c_26,c_106])).

tff(c_46,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_317,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_157,plain,(
    ! [A_45,B_46] : k2_xboole_0(k1_tarski(A_45),k1_tarski(B_46)) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_181,plain,(
    ! [A_45,B_46] : r1_tarski(k1_tarski(A_45),k2_tarski(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_32])).

tff(c_50,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_136,plain,(
    r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_406,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(A_70,C_71)
      | ~ r1_tarski(B_72,C_71)
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_435,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,'#skF_8')
      | ~ r1_tarski(A_73,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_136,c_406])).

tff(c_453,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_181,c_435])).

tff(c_38,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,B_25)
      | ~ r1_tarski(k1_tarski(A_24),B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_464,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_453,c_38])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_317,c_464])).

tff(c_471,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_473,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_56,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_71,plain,(
    ! [A_30,B_29] : r1_tarski(A_30,k2_xboole_0(B_29,A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_32])).

tff(c_172,plain,(
    ! [B_46,A_45] : r1_tarski(k1_tarski(B_46),k2_tarski(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_71])).

tff(c_566,plain,(
    ! [A_79,C_80,B_81] :
      ( r1_tarski(A_79,C_80)
      | ~ r1_tarski(B_81,C_80)
      | ~ r1_tarski(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_594,plain,(
    ! [A_82] :
      ( r1_tarski(A_82,'#skF_8')
      | ~ r1_tarski(A_82,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_136,c_566])).

tff(c_611,plain,(
    r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_172,c_594])).

tff(c_633,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_611,c_38])).

tff(c_639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_473,c_633])).

tff(c_640,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_40,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k1_tarski(A_24),B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_719,plain,(
    ! [A_85,C_86,B_87] :
      ( r1_tarski(A_85,C_86)
      | ~ r1_tarski(B_87,C_86)
      | ~ r1_tarski(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1554,plain,(
    ! [A_152,B_153,A_154] :
      ( r1_tarski(A_152,B_153)
      | ~ r1_tarski(A_152,k1_tarski(A_154))
      | ~ r2_hidden(A_154,B_153) ) ),
    inference(resolution,[status(thm)],[c_40,c_719])).

tff(c_36843,plain,(
    ! [A_598,B_599,A_600] :
      ( r1_tarski(k1_tarski(A_598),B_599)
      | ~ r2_hidden(A_600,B_599)
      | ~ r2_hidden(A_598,k1_tarski(A_600)) ) ),
    inference(resolution,[status(thm)],[c_40,c_1554])).

tff(c_37662,plain,(
    ! [A_602] :
      ( r1_tarski(k1_tarski(A_602),'#skF_5')
      | ~ r2_hidden(A_602,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_640,c_36843])).

tff(c_37835,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_125,c_37662])).

tff(c_641,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_472,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_643,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_44])).

tff(c_644,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_643])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_644])).

tff(c_647,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_37084,plain,(
    ! [A_601] :
      ( r1_tarski(k1_tarski(A_601),'#skF_5')
      | ~ r2_hidden(A_601,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_647,c_36843])).

tff(c_37257,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_125,c_37084])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3554,plain,(
    ! [A_289,C_290] :
      ( r2_hidden('#skF_2'(A_289,A_289,C_290),C_290)
      | k2_xboole_0(A_289,A_289) = C_290
      | r2_hidden('#skF_1'(A_289,A_289,C_290),A_289) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_20])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3623,plain,(
    ! [A_289] :
      ( r2_hidden('#skF_2'(A_289,A_289,A_289),A_289)
      | k2_xboole_0(A_289,A_289) = A_289 ) ),
    inference(resolution,[status(thm)],[c_3554,c_18])).

tff(c_1720,plain,(
    ! [A_163,B_164,C_165] :
      ( r2_hidden('#skF_1'(A_163,B_164,C_165),B_164)
      | r2_hidden('#skF_1'(A_163,B_164,C_165),A_163)
      | ~ r2_hidden('#skF_2'(A_163,B_164,C_165),A_163)
      | k2_xboole_0(A_163,B_164) = C_165 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3072,plain,(
    ! [A_254,B_255] :
      ( r2_hidden('#skF_1'(A_254,B_255,B_255),A_254)
      | ~ r2_hidden('#skF_2'(A_254,B_255,B_255),A_254)
      | k2_xboole_0(A_254,B_255) = B_255 ) ),
    inference(resolution,[status(thm)],[c_1720,c_14])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_5452,plain,(
    ! [A_362] :
      ( ~ r2_hidden('#skF_2'(A_362,A_362,A_362),A_362)
      | k2_xboole_0(A_362,A_362) = A_362 ) ),
    inference(resolution,[status(thm)],[c_3072,c_10])).

tff(c_5486,plain,(
    ! [A_289] : k2_xboole_0(A_289,A_289) = A_289 ),
    inference(resolution,[status(thm)],[c_3623,c_5452])).

tff(c_5497,plain,(
    ! [A_363] : k2_xboole_0(A_363,A_363) = A_363 ),
    inference(resolution,[status(thm)],[c_3623,c_5452])).

tff(c_827,plain,(
    ! [A_93,C_94,B_95] :
      ( r1_tarski(k2_xboole_0(A_93,C_94),k2_xboole_0(B_95,C_94))
      | ~ r1_tarski(A_93,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_857,plain,(
    ! [B_95,C_94,A_93] :
      ( k2_xboole_0(B_95,C_94) = k2_xboole_0(A_93,C_94)
      | ~ r1_tarski(k2_xboole_0(B_95,C_94),k2_xboole_0(A_93,C_94))
      | ~ r1_tarski(A_93,B_95) ) ),
    inference(resolution,[status(thm)],[c_827,c_22])).

tff(c_5625,plain,(
    ! [A_93,A_363] :
      ( k2_xboole_0(A_93,A_363) = k2_xboole_0(A_363,A_363)
      | ~ r1_tarski(A_363,k2_xboole_0(A_93,A_363))
      | ~ r1_tarski(A_93,A_363) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5497,c_857])).

tff(c_5906,plain,(
    ! [A_93,A_363] :
      ( k2_xboole_0(A_93,A_363) = A_363
      | ~ r1_tarski(A_93,A_363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_5486,c_5625])).

tff(c_37277,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_37257,c_5906])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_175,plain,(
    ! [B_46,A_45] : k2_xboole_0(k1_tarski(B_46),k1_tarski(A_45)) = k2_tarski(A_45,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_2])).

tff(c_1470,plain,(
    ! [A_146,B_147,A_148] :
      ( r1_tarski(k2_xboole_0(A_146,B_147),k2_xboole_0(B_147,A_148))
      | ~ r1_tarski(A_146,A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_827])).

tff(c_55342,plain,(
    ! [A_774,B_775,A_776] :
      ( r1_tarski(k2_tarski(A_774,B_775),k2_xboole_0(k1_tarski(A_774),A_776))
      | ~ r1_tarski(k1_tarski(B_775),A_776) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_1470])).

tff(c_55984,plain,(
    ! [B_783] :
      ( r1_tarski(k2_tarski('#skF_4',B_783),'#skF_5')
      | ~ r1_tarski(k1_tarski(B_783),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37277,c_55342])).

tff(c_36,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),k1_tarski(B_23)) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_261,plain,(
    ! [B_63,A_64] : k2_xboole_0(k1_tarski(B_63),k1_tarski(A_64)) = k2_tarski(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_2])).

tff(c_300,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_261])).

tff(c_42,plain,
    ( ~ r1_tarski(k2_tarski('#skF_3','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_769,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_3'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_641,c_300,c_42])).

tff(c_56003,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_55984,c_769])).

tff(c_56032,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37835,c_56003])).

tff(c_56034,plain,(
    ~ r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56055,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56034,c_52])).

tff(c_56305,plain,(
    ! [A_814,C_815,B_816] :
      ( r1_tarski(A_814,C_815)
      | ~ r1_tarski(B_816,C_815)
      | ~ r1_tarski(A_814,B_816) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56793,plain,(
    ! [A_864,B_865,A_866] :
      ( r1_tarski(A_864,B_865)
      | ~ r1_tarski(A_864,k1_tarski(A_866))
      | ~ r2_hidden(A_866,B_865) ) ),
    inference(resolution,[status(thm)],[c_40,c_56305])).

tff(c_79404,plain,(
    ! [A_1317,B_1318,A_1319] :
      ( r1_tarski(k1_tarski(A_1317),B_1318)
      | ~ r2_hidden(A_1319,B_1318)
      | ~ r2_hidden(A_1317,k1_tarski(A_1319)) ) ),
    inference(resolution,[status(thm)],[c_40,c_56793])).

tff(c_79624,plain,(
    ! [A_1320] :
      ( r1_tarski(k1_tarski(A_1320),'#skF_5')
      | ~ r2_hidden(A_1320,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_56055,c_79404])).

tff(c_79781,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_125,c_79624])).

tff(c_56033,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_80202,plain,(
    ! [A_1321] :
      ( r1_tarski(k1_tarski(A_1321),'#skF_5')
      | ~ r2_hidden(A_1321,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_56033,c_79404])).

tff(c_80359,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_125,c_80202])).

tff(c_56994,plain,(
    ! [A_884,B_885,C_886] :
      ( r2_hidden('#skF_1'(A_884,B_885,C_886),B_885)
      | r2_hidden('#skF_1'(A_884,B_885,C_886),A_884)
      | r2_hidden('#skF_2'(A_884,B_885,C_886),C_886)
      | k2_xboole_0(A_884,B_885) = C_886 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58071,plain,(
    ! [A_962,B_963] :
      ( r2_hidden('#skF_1'(A_962,B_963,B_963),A_962)
      | r2_hidden('#skF_2'(A_962,B_963,B_963),B_963)
      | k2_xboole_0(A_962,B_963) = B_963 ) ),
    inference(resolution,[status(thm)],[c_56994,c_18])).

tff(c_58824,plain,(
    ! [A_1004] :
      ( r2_hidden('#skF_2'(A_1004,A_1004,A_1004),A_1004)
      | k2_xboole_0(A_1004,A_1004) = A_1004 ) ),
    inference(resolution,[status(thm)],[c_58071,c_18])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58637,plain,(
    ! [B_998,C_999] :
      ( ~ r2_hidden('#skF_2'(B_998,B_998,C_999),B_998)
      | k2_xboole_0(B_998,B_998) = C_999
      | r2_hidden('#skF_1'(B_998,B_998,C_999),B_998) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_12])).

tff(c_58662,plain,(
    ! [B_998] :
      ( ~ r2_hidden('#skF_2'(B_998,B_998,B_998),B_998)
      | k2_xboole_0(B_998,B_998) = B_998 ) ),
    inference(resolution,[status(thm)],[c_58637,c_14])).

tff(c_58840,plain,(
    ! [A_1004] : k2_xboole_0(A_1004,A_1004) = A_1004 ),
    inference(resolution,[status(thm)],[c_58824,c_58662])).

tff(c_58848,plain,(
    ! [A_1005] : k2_xboole_0(A_1005,A_1005) = A_1005 ),
    inference(resolution,[status(thm)],[c_58824,c_58662])).

tff(c_56368,plain,(
    ! [A_826,C_827,B_828] :
      ( r1_tarski(k2_xboole_0(A_826,C_827),k2_xboole_0(B_828,C_827))
      | ~ r1_tarski(A_826,B_828) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56398,plain,(
    ! [B_828,C_827,A_826] :
      ( k2_xboole_0(B_828,C_827) = k2_xboole_0(A_826,C_827)
      | ~ r1_tarski(k2_xboole_0(B_828,C_827),k2_xboole_0(A_826,C_827))
      | ~ r1_tarski(A_826,B_828) ) ),
    inference(resolution,[status(thm)],[c_56368,c_22])).

tff(c_58854,plain,(
    ! [A_826,A_1005] :
      ( k2_xboole_0(A_826,A_1005) = k2_xboole_0(A_1005,A_1005)
      | ~ r1_tarski(A_1005,k2_xboole_0(A_826,A_1005))
      | ~ r1_tarski(A_826,A_1005) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58848,c_56398])).

tff(c_59148,plain,(
    ! [A_826,A_1005] :
      ( k2_xboole_0(A_826,A_1005) = A_1005
      | ~ r1_tarski(A_826,A_1005) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_58840,c_58854])).

tff(c_80379,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_80359,c_59148])).

tff(c_56075,plain,(
    ! [A_795,B_796] : k2_xboole_0(k1_tarski(A_795),k1_tarski(B_796)) = k2_tarski(A_795,B_796) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_56111,plain,(
    ! [B_796,A_795] : k2_xboole_0(k1_tarski(B_796),k1_tarski(A_795)) = k2_tarski(A_795,B_796) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_56075])).

tff(c_56709,plain,(
    ! [A_858,B_859,A_860] :
      ( r1_tarski(k2_xboole_0(A_858,B_859),k2_xboole_0(B_859,A_860))
      | ~ r1_tarski(A_858,A_860) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_56368])).

tff(c_83953,plain,(
    ! [A_1361,B_1362,A_1363] :
      ( r1_tarski(k2_tarski(A_1361,B_1362),k2_xboole_0(k1_tarski(A_1361),A_1363))
      | ~ r1_tarski(k1_tarski(B_1362),A_1363) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56111,c_56709])).

tff(c_97463,plain,(
    ! [B_1510] :
      ( r1_tarski(k2_tarski('#skF_4',B_1510),'#skF_5')
      | ~ r1_tarski(k1_tarski(B_1510),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80379,c_83953])).

tff(c_56156,plain,(
    ! [B_807,A_808] : k2_xboole_0(k1_tarski(B_807),k1_tarski(A_808)) = k2_tarski(A_808,B_807) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_56075])).

tff(c_56162,plain,(
    ! [B_807,A_808] : k2_tarski(B_807,A_808) = k2_tarski(A_808,B_807) ),
    inference(superposition,[status(thm),theory(equality)],[c_56156,c_36])).

tff(c_48,plain,
    ( ~ r1_tarski(k2_tarski('#skF_3','#skF_4'),'#skF_5')
    | r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56303,plain,
    ( ~ r1_tarski(k2_tarski('#skF_4','#skF_3'),'#skF_5')
    | r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56162,c_48])).

tff(c_56304,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_3'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56034,c_56303])).

tff(c_97490,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_97463,c_56304])).

tff(c_97521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79781,c_97490])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.59/18.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.59/18.16  
% 28.59/18.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.59/18.17  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4
% 28.59/18.17  
% 28.59/18.17  %Foreground sorts:
% 28.59/18.17  
% 28.59/18.17  
% 28.59/18.17  %Background operators:
% 28.59/18.17  
% 28.59/18.17  
% 28.59/18.17  %Foreground operators:
% 28.59/18.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 28.59/18.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.59/18.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 28.59/18.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 28.59/18.17  tff('#skF_7', type, '#skF_7': $i).
% 28.59/18.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 28.59/18.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 28.59/18.17  tff('#skF_5', type, '#skF_5': $i).
% 28.59/18.17  tff('#skF_6', type, '#skF_6': $i).
% 28.59/18.17  tff('#skF_3', type, '#skF_3': $i).
% 28.59/18.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 28.59/18.17  tff('#skF_8', type, '#skF_8': $i).
% 28.59/18.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.59/18.17  tff('#skF_4', type, '#skF_4': $i).
% 28.59/18.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.59/18.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 28.59/18.17  
% 28.59/18.19  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 28.59/18.19  tff(f_64, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 28.59/18.19  tff(f_71, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 28.59/18.19  tff(f_60, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 28.59/18.19  tff(f_54, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 28.59/18.19  tff(f_52, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 28.59/18.19  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 28.59/18.19  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 28.59/18.19  tff(f_58, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 28.59/18.19  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 28.59/18.19  tff(c_106, plain, (![A_35, B_36]: (r2_hidden(A_35, B_36) | ~r1_tarski(k1_tarski(A_35), B_36))), inference(cnfTransformation, [status(thm)], [f_64])).
% 28.59/18.19  tff(c_125, plain, (![A_35]: (r2_hidden(A_35, k1_tarski(A_35)))), inference(resolution, [status(thm)], [c_26, c_106])).
% 28.59/18.19  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 28.59/18.19  tff(c_317, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_46])).
% 28.59/18.19  tff(c_157, plain, (![A_45, B_46]: (k2_xboole_0(k1_tarski(A_45), k1_tarski(B_46))=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_60])).
% 28.59/18.19  tff(c_32, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 28.59/18.19  tff(c_181, plain, (![A_45, B_46]: (r1_tarski(k1_tarski(A_45), k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_32])).
% 28.59/18.19  tff(c_50, plain, (r2_hidden('#skF_4', '#skF_5') | r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 28.59/18.19  tff(c_136, plain, (r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_50])).
% 28.59/18.19  tff(c_406, plain, (![A_70, C_71, B_72]: (r1_tarski(A_70, C_71) | ~r1_tarski(B_72, C_71) | ~r1_tarski(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_52])).
% 28.59/18.19  tff(c_435, plain, (![A_73]: (r1_tarski(A_73, '#skF_8') | ~r1_tarski(A_73, k2_tarski('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_136, c_406])).
% 28.59/18.19  tff(c_453, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_8')), inference(resolution, [status(thm)], [c_181, c_435])).
% 28.59/18.19  tff(c_38, plain, (![A_24, B_25]: (r2_hidden(A_24, B_25) | ~r1_tarski(k1_tarski(A_24), B_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 28.59/18.19  tff(c_464, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_453, c_38])).
% 28.59/18.19  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_317, c_464])).
% 28.59/18.19  tff(c_471, plain, (~r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 28.59/18.19  tff(c_473, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_471])).
% 28.59/18.19  tff(c_56, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 28.59/18.19  tff(c_71, plain, (![A_30, B_29]: (r1_tarski(A_30, k2_xboole_0(B_29, A_30)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_32])).
% 28.59/18.19  tff(c_172, plain, (![B_46, A_45]: (r1_tarski(k1_tarski(B_46), k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_71])).
% 28.59/18.19  tff(c_566, plain, (![A_79, C_80, B_81]: (r1_tarski(A_79, C_80) | ~r1_tarski(B_81, C_80) | ~r1_tarski(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_52])).
% 28.59/18.19  tff(c_594, plain, (![A_82]: (r1_tarski(A_82, '#skF_8') | ~r1_tarski(A_82, k2_tarski('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_136, c_566])).
% 28.59/18.19  tff(c_611, plain, (r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_172, c_594])).
% 28.59/18.19  tff(c_633, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_611, c_38])).
% 28.59/18.19  tff(c_639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_473, c_633])).
% 28.59/18.19  tff(c_640, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_471])).
% 28.59/18.19  tff(c_40, plain, (![A_24, B_25]: (r1_tarski(k1_tarski(A_24), B_25) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 28.59/18.19  tff(c_719, plain, (![A_85, C_86, B_87]: (r1_tarski(A_85, C_86) | ~r1_tarski(B_87, C_86) | ~r1_tarski(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_52])).
% 28.59/18.19  tff(c_1554, plain, (![A_152, B_153, A_154]: (r1_tarski(A_152, B_153) | ~r1_tarski(A_152, k1_tarski(A_154)) | ~r2_hidden(A_154, B_153))), inference(resolution, [status(thm)], [c_40, c_719])).
% 28.59/18.19  tff(c_36843, plain, (![A_598, B_599, A_600]: (r1_tarski(k1_tarski(A_598), B_599) | ~r2_hidden(A_600, B_599) | ~r2_hidden(A_598, k1_tarski(A_600)))), inference(resolution, [status(thm)], [c_40, c_1554])).
% 28.59/18.19  tff(c_37662, plain, (![A_602]: (r1_tarski(k1_tarski(A_602), '#skF_5') | ~r2_hidden(A_602, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_640, c_36843])).
% 28.59/18.19  tff(c_37835, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_125, c_37662])).
% 28.59/18.19  tff(c_641, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_471])).
% 28.59/18.19  tff(c_472, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_46])).
% 28.59/18.19  tff(c_44, plain, (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 28.59/18.19  tff(c_643, plain, (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_472, c_44])).
% 28.59/18.19  tff(c_644, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_643])).
% 28.59/18.19  tff(c_646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_641, c_644])).
% 28.59/18.19  tff(c_647, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_643])).
% 28.59/18.19  tff(c_37084, plain, (![A_601]: (r1_tarski(k1_tarski(A_601), '#skF_5') | ~r2_hidden(A_601, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_647, c_36843])).
% 28.59/18.19  tff(c_37257, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_125, c_37084])).
% 28.59/18.19  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 28.59/18.19  tff(c_3554, plain, (![A_289, C_290]: (r2_hidden('#skF_2'(A_289, A_289, C_290), C_290) | k2_xboole_0(A_289, A_289)=C_290 | r2_hidden('#skF_1'(A_289, A_289, C_290), A_289))), inference(factorization, [status(thm), theory('equality')], [c_20])).
% 28.59/18.19  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 28.59/18.19  tff(c_3623, plain, (![A_289]: (r2_hidden('#skF_2'(A_289, A_289, A_289), A_289) | k2_xboole_0(A_289, A_289)=A_289)), inference(resolution, [status(thm)], [c_3554, c_18])).
% 28.59/18.19  tff(c_1720, plain, (![A_163, B_164, C_165]: (r2_hidden('#skF_1'(A_163, B_164, C_165), B_164) | r2_hidden('#skF_1'(A_163, B_164, C_165), A_163) | ~r2_hidden('#skF_2'(A_163, B_164, C_165), A_163) | k2_xboole_0(A_163, B_164)=C_165)), inference(cnfTransformation, [status(thm)], [f_36])).
% 28.59/18.19  tff(c_14, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 28.59/18.19  tff(c_3072, plain, (![A_254, B_255]: (r2_hidden('#skF_1'(A_254, B_255, B_255), A_254) | ~r2_hidden('#skF_2'(A_254, B_255, B_255), A_254) | k2_xboole_0(A_254, B_255)=B_255)), inference(resolution, [status(thm)], [c_1720, c_14])).
% 28.59/18.19  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 28.59/18.19  tff(c_5452, plain, (![A_362]: (~r2_hidden('#skF_2'(A_362, A_362, A_362), A_362) | k2_xboole_0(A_362, A_362)=A_362)), inference(resolution, [status(thm)], [c_3072, c_10])).
% 28.59/18.19  tff(c_5486, plain, (![A_289]: (k2_xboole_0(A_289, A_289)=A_289)), inference(resolution, [status(thm)], [c_3623, c_5452])).
% 28.59/18.19  tff(c_5497, plain, (![A_363]: (k2_xboole_0(A_363, A_363)=A_363)), inference(resolution, [status(thm)], [c_3623, c_5452])).
% 28.59/18.19  tff(c_827, plain, (![A_93, C_94, B_95]: (r1_tarski(k2_xboole_0(A_93, C_94), k2_xboole_0(B_95, C_94)) | ~r1_tarski(A_93, B_95))), inference(cnfTransformation, [status(thm)], [f_58])).
% 28.59/18.19  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 28.59/18.19  tff(c_857, plain, (![B_95, C_94, A_93]: (k2_xboole_0(B_95, C_94)=k2_xboole_0(A_93, C_94) | ~r1_tarski(k2_xboole_0(B_95, C_94), k2_xboole_0(A_93, C_94)) | ~r1_tarski(A_93, B_95))), inference(resolution, [status(thm)], [c_827, c_22])).
% 28.59/18.19  tff(c_5625, plain, (![A_93, A_363]: (k2_xboole_0(A_93, A_363)=k2_xboole_0(A_363, A_363) | ~r1_tarski(A_363, k2_xboole_0(A_93, A_363)) | ~r1_tarski(A_93, A_363))), inference(superposition, [status(thm), theory('equality')], [c_5497, c_857])).
% 28.59/18.19  tff(c_5906, plain, (![A_93, A_363]: (k2_xboole_0(A_93, A_363)=A_363 | ~r1_tarski(A_93, A_363))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_5486, c_5625])).
% 28.59/18.19  tff(c_37277, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_37257, c_5906])).
% 28.59/18.19  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 28.59/18.19  tff(c_175, plain, (![B_46, A_45]: (k2_xboole_0(k1_tarski(B_46), k1_tarski(A_45))=k2_tarski(A_45, B_46))), inference(superposition, [status(thm), theory('equality')], [c_157, c_2])).
% 28.59/18.19  tff(c_1470, plain, (![A_146, B_147, A_148]: (r1_tarski(k2_xboole_0(A_146, B_147), k2_xboole_0(B_147, A_148)) | ~r1_tarski(A_146, A_148))), inference(superposition, [status(thm), theory('equality')], [c_2, c_827])).
% 28.59/18.19  tff(c_55342, plain, (![A_774, B_775, A_776]: (r1_tarski(k2_tarski(A_774, B_775), k2_xboole_0(k1_tarski(A_774), A_776)) | ~r1_tarski(k1_tarski(B_775), A_776))), inference(superposition, [status(thm), theory('equality')], [c_175, c_1470])).
% 28.59/18.19  tff(c_55984, plain, (![B_783]: (r1_tarski(k2_tarski('#skF_4', B_783), '#skF_5') | ~r1_tarski(k1_tarski(B_783), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_37277, c_55342])).
% 28.59/18.19  tff(c_36, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), k1_tarski(B_23))=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 28.59/18.19  tff(c_261, plain, (![B_63, A_64]: (k2_xboole_0(k1_tarski(B_63), k1_tarski(A_64))=k2_tarski(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_157, c_2])).
% 28.59/18.19  tff(c_300, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(superposition, [status(thm), theory('equality')], [c_36, c_261])).
% 28.59/18.19  tff(c_42, plain, (~r1_tarski(k2_tarski('#skF_3', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 28.59/18.19  tff(c_769, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_3'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_472, c_641, c_300, c_42])).
% 28.59/18.19  tff(c_56003, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_55984, c_769])).
% 28.59/18.19  tff(c_56032, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37835, c_56003])).
% 28.59/18.19  tff(c_56034, plain, (~r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_50])).
% 28.59/18.19  tff(c_52, plain, (r2_hidden('#skF_3', '#skF_5') | r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 28.59/18.19  tff(c_56055, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56034, c_52])).
% 28.59/18.19  tff(c_56305, plain, (![A_814, C_815, B_816]: (r1_tarski(A_814, C_815) | ~r1_tarski(B_816, C_815) | ~r1_tarski(A_814, B_816))), inference(cnfTransformation, [status(thm)], [f_52])).
% 28.59/18.19  tff(c_56793, plain, (![A_864, B_865, A_866]: (r1_tarski(A_864, B_865) | ~r1_tarski(A_864, k1_tarski(A_866)) | ~r2_hidden(A_866, B_865))), inference(resolution, [status(thm)], [c_40, c_56305])).
% 28.59/18.19  tff(c_79404, plain, (![A_1317, B_1318, A_1319]: (r1_tarski(k1_tarski(A_1317), B_1318) | ~r2_hidden(A_1319, B_1318) | ~r2_hidden(A_1317, k1_tarski(A_1319)))), inference(resolution, [status(thm)], [c_40, c_56793])).
% 28.59/18.19  tff(c_79624, plain, (![A_1320]: (r1_tarski(k1_tarski(A_1320), '#skF_5') | ~r2_hidden(A_1320, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_56055, c_79404])).
% 28.59/18.19  tff(c_79781, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_125, c_79624])).
% 28.59/18.19  tff(c_56033, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 28.59/18.19  tff(c_80202, plain, (![A_1321]: (r1_tarski(k1_tarski(A_1321), '#skF_5') | ~r2_hidden(A_1321, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_56033, c_79404])).
% 28.59/18.19  tff(c_80359, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_125, c_80202])).
% 28.59/18.19  tff(c_56994, plain, (![A_884, B_885, C_886]: (r2_hidden('#skF_1'(A_884, B_885, C_886), B_885) | r2_hidden('#skF_1'(A_884, B_885, C_886), A_884) | r2_hidden('#skF_2'(A_884, B_885, C_886), C_886) | k2_xboole_0(A_884, B_885)=C_886)), inference(cnfTransformation, [status(thm)], [f_36])).
% 28.59/18.19  tff(c_58071, plain, (![A_962, B_963]: (r2_hidden('#skF_1'(A_962, B_963, B_963), A_962) | r2_hidden('#skF_2'(A_962, B_963, B_963), B_963) | k2_xboole_0(A_962, B_963)=B_963)), inference(resolution, [status(thm)], [c_56994, c_18])).
% 28.59/18.19  tff(c_58824, plain, (![A_1004]: (r2_hidden('#skF_2'(A_1004, A_1004, A_1004), A_1004) | k2_xboole_0(A_1004, A_1004)=A_1004)), inference(resolution, [status(thm)], [c_58071, c_18])).
% 28.59/18.19  tff(c_12, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 28.59/18.19  tff(c_58637, plain, (![B_998, C_999]: (~r2_hidden('#skF_2'(B_998, B_998, C_999), B_998) | k2_xboole_0(B_998, B_998)=C_999 | r2_hidden('#skF_1'(B_998, B_998, C_999), B_998))), inference(factorization, [status(thm), theory('equality')], [c_12])).
% 28.59/18.19  tff(c_58662, plain, (![B_998]: (~r2_hidden('#skF_2'(B_998, B_998, B_998), B_998) | k2_xboole_0(B_998, B_998)=B_998)), inference(resolution, [status(thm)], [c_58637, c_14])).
% 28.59/18.19  tff(c_58840, plain, (![A_1004]: (k2_xboole_0(A_1004, A_1004)=A_1004)), inference(resolution, [status(thm)], [c_58824, c_58662])).
% 28.59/18.19  tff(c_58848, plain, (![A_1005]: (k2_xboole_0(A_1005, A_1005)=A_1005)), inference(resolution, [status(thm)], [c_58824, c_58662])).
% 28.59/18.19  tff(c_56368, plain, (![A_826, C_827, B_828]: (r1_tarski(k2_xboole_0(A_826, C_827), k2_xboole_0(B_828, C_827)) | ~r1_tarski(A_826, B_828))), inference(cnfTransformation, [status(thm)], [f_58])).
% 28.59/18.19  tff(c_56398, plain, (![B_828, C_827, A_826]: (k2_xboole_0(B_828, C_827)=k2_xboole_0(A_826, C_827) | ~r1_tarski(k2_xboole_0(B_828, C_827), k2_xboole_0(A_826, C_827)) | ~r1_tarski(A_826, B_828))), inference(resolution, [status(thm)], [c_56368, c_22])).
% 28.59/18.19  tff(c_58854, plain, (![A_826, A_1005]: (k2_xboole_0(A_826, A_1005)=k2_xboole_0(A_1005, A_1005) | ~r1_tarski(A_1005, k2_xboole_0(A_826, A_1005)) | ~r1_tarski(A_826, A_1005))), inference(superposition, [status(thm), theory('equality')], [c_58848, c_56398])).
% 28.59/18.19  tff(c_59148, plain, (![A_826, A_1005]: (k2_xboole_0(A_826, A_1005)=A_1005 | ~r1_tarski(A_826, A_1005))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_58840, c_58854])).
% 28.59/18.19  tff(c_80379, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_80359, c_59148])).
% 28.59/18.19  tff(c_56075, plain, (![A_795, B_796]: (k2_xboole_0(k1_tarski(A_795), k1_tarski(B_796))=k2_tarski(A_795, B_796))), inference(cnfTransformation, [status(thm)], [f_60])).
% 28.59/18.19  tff(c_56111, plain, (![B_796, A_795]: (k2_xboole_0(k1_tarski(B_796), k1_tarski(A_795))=k2_tarski(A_795, B_796))), inference(superposition, [status(thm), theory('equality')], [c_2, c_56075])).
% 28.59/18.19  tff(c_56709, plain, (![A_858, B_859, A_860]: (r1_tarski(k2_xboole_0(A_858, B_859), k2_xboole_0(B_859, A_860)) | ~r1_tarski(A_858, A_860))), inference(superposition, [status(thm), theory('equality')], [c_2, c_56368])).
% 28.59/18.19  tff(c_83953, plain, (![A_1361, B_1362, A_1363]: (r1_tarski(k2_tarski(A_1361, B_1362), k2_xboole_0(k1_tarski(A_1361), A_1363)) | ~r1_tarski(k1_tarski(B_1362), A_1363))), inference(superposition, [status(thm), theory('equality')], [c_56111, c_56709])).
% 28.59/18.19  tff(c_97463, plain, (![B_1510]: (r1_tarski(k2_tarski('#skF_4', B_1510), '#skF_5') | ~r1_tarski(k1_tarski(B_1510), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_80379, c_83953])).
% 28.59/18.19  tff(c_56156, plain, (![B_807, A_808]: (k2_xboole_0(k1_tarski(B_807), k1_tarski(A_808))=k2_tarski(A_808, B_807))), inference(superposition, [status(thm), theory('equality')], [c_2, c_56075])).
% 28.59/18.19  tff(c_56162, plain, (![B_807, A_808]: (k2_tarski(B_807, A_808)=k2_tarski(A_808, B_807))), inference(superposition, [status(thm), theory('equality')], [c_56156, c_36])).
% 28.59/18.19  tff(c_48, plain, (~r1_tarski(k2_tarski('#skF_3', '#skF_4'), '#skF_5') | r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 28.59/18.19  tff(c_56303, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_3'), '#skF_5') | r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56162, c_48])).
% 28.59/18.19  tff(c_56304, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_3'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56034, c_56303])).
% 28.59/18.19  tff(c_97490, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_97463, c_56304])).
% 28.59/18.19  tff(c_97521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79781, c_97490])).
% 28.59/18.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.59/18.19  
% 28.59/18.19  Inference rules
% 28.59/18.19  ----------------------
% 28.59/18.19  #Ref     : 0
% 28.59/18.19  #Sup     : 24093
% 28.59/18.19  #Fact    : 74
% 28.59/18.19  #Define  : 0
% 28.59/18.19  #Split   : 22
% 28.59/18.19  #Chain   : 0
% 28.59/18.19  #Close   : 0
% 28.59/18.19  
% 28.59/18.19  Ordering : KBO
% 28.59/18.19  
% 28.59/18.19  Simplification rules
% 28.59/18.19  ----------------------
% 28.59/18.19  #Subsume      : 5111
% 28.59/18.19  #Demod        : 20114
% 28.59/18.19  #Tautology    : 8712
% 28.59/18.19  #SimpNegUnit  : 23
% 28.59/18.19  #BackRed      : 19
% 28.59/18.19  
% 28.59/18.19  #Partial instantiations: 0
% 28.59/18.19  #Strategies tried      : 1
% 28.59/18.19  
% 28.59/18.19  Timing (in seconds)
% 28.59/18.19  ----------------------
% 28.59/18.19  Preprocessing        : 0.30
% 28.59/18.19  Parsing              : 0.16
% 28.59/18.19  CNF conversion       : 0.02
% 28.59/18.19  Main loop            : 17.12
% 28.59/18.19  Inferencing          : 2.06
% 28.59/18.19  Reduction            : 8.47
% 28.59/18.19  Demodulation         : 7.58
% 28.59/18.19  BG Simplification    : 0.27
% 28.59/18.19  Subsumption          : 5.37
% 28.59/18.19  Abstraction          : 0.38
% 28.59/18.19  MUC search           : 0.00
% 28.59/18.19  Cooper               : 0.00
% 28.59/18.19  Total                : 17.47
% 28.59/18.19  Index Insertion      : 0.00
% 28.59/18.19  Index Deletion       : 0.00
% 28.59/18.19  Index Matching       : 0.00
% 28.59/18.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
