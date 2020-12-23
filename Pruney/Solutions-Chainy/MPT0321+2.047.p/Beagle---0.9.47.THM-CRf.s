%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:19 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 512 expanded)
%              Number of leaves         :   18 ( 166 expanded)
%              Depth                    :   16
%              Number of atoms          :  175 (1230 expanded)
%              Number of equality atoms :   48 ( 520 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_18,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_3'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( r2_hidden(k4_tarski(A_31,B_32),k2_zfmisc_1(C_33,D_34))
      | ~ r2_hidden(B_32,D_34)
      | ~ r2_hidden(A_31,C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_35,plain,(
    ! [A_15,C_16,B_17,D_18] :
      ( r2_hidden(A_15,C_16)
      | ~ r2_hidden(k4_tarski(A_15,B_17),k2_zfmisc_1(C_16,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38,plain,(
    ! [A_15,B_17] :
      ( r2_hidden(A_15,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_15,B_17),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_35])).

tff(c_76,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,'#skF_6')
      | ~ r2_hidden(B_32,'#skF_5')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_38])).

tff(c_98,plain,(
    ! [B_37] : ~ r2_hidden(B_37,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_112,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_112])).

tff(c_120,plain,(
    ! [A_38] :
      ( r2_hidden(A_38,'#skF_6')
      | ~ r2_hidden(A_38,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_795,plain,(
    ! [A_73] :
      ( r2_hidden('#skF_1'(A_73,'#skF_6'),'#skF_6')
      | A_73 = '#skF_6'
      | ~ r2_hidden('#skF_2'(A_73,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_120,c_4])).

tff(c_799,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_6'),'#skF_6')
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_795])).

tff(c_806,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_25,c_799])).

tff(c_80,plain,(
    ! [A_35,B_36] :
      ( r2_hidden(k4_tarski(A_35,B_36),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_36,'#skF_7')
      | ~ r2_hidden(A_35,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_58])).

tff(c_14,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_96,plain,(
    ! [B_36,A_35] :
      ( r2_hidden(B_36,'#skF_5')
      | ~ r2_hidden(B_36,'#skF_7')
      | ~ r2_hidden(A_35,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_80,c_14])).

tff(c_166,plain,(
    ! [A_41] : ~ r2_hidden(A_41,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_183,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10,c_166])).

tff(c_211,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_3'(A_45),A_45)
      | A_45 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_10])).

tff(c_163,plain,(
    ! [A_35] : ~ r2_hidden(A_35,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_119,plain,(
    ! [A_31] :
      ( r2_hidden(A_31,'#skF_6')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_164,plain,(
    ! [A_31] : ~ r2_hidden(A_31,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_119])).

tff(c_215,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_211,c_164])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_215])).

tff(c_225,plain,(
    ! [B_46] :
      ( r2_hidden(B_46,'#skF_5')
      | ~ r2_hidden(B_46,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_246,plain,
    ( r2_hidden('#skF_3'('#skF_7'),'#skF_5')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_10,c_225])).

tff(c_247,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_249,plain,(
    '#skF_7' != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_20])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_31,plain,(
    ! [B_11,D_12,A_13,C_14] :
      ( r2_hidden(B_11,D_12)
      | ~ r2_hidden(k4_tarski(A_13,B_11),k2_zfmisc_1(C_14,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [B_11,A_13] :
      ( r2_hidden(B_11,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_13,B_11),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_31])).

tff(c_77,plain,(
    ! [B_32,A_31] :
      ( r2_hidden(B_32,'#skF_7')
      | ~ r2_hidden(B_32,'#skF_5')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_34])).

tff(c_131,plain,(
    ! [A_39] : ~ r2_hidden(A_39,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_145,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_145])).

tff(c_153,plain,(
    ! [B_40] :
      ( r2_hidden(B_40,'#skF_7')
      | ~ r2_hidden(B_40,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_630,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_1'(A_67,'#skF_7'),'#skF_7')
      | A_67 = '#skF_7'
      | ~ r2_hidden('#skF_2'(A_67,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_153,c_4])).

tff(c_634,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8,c_630])).

tff(c_641,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_249,c_634])).

tff(c_224,plain,(
    ! [B_36] :
      ( r2_hidden(B_36,'#skF_5')
      | ~ r2_hidden(B_36,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_647,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_641,c_224])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_152,plain,(
    ! [B_32] :
      ( r2_hidden(B_32,'#skF_7')
      | ~ r2_hidden(B_32,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_649,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_647,c_2])).

tff(c_652,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_649])).

tff(c_656,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_152,c_652])).

tff(c_662,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_5')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_656])).

tff(c_668,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_662])).

tff(c_670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_668])).

tff(c_672,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_16,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_95,plain,(
    ! [A_35,B_36] :
      ( r2_hidden(A_35,'#skF_4')
      | ~ r2_hidden(B_36,'#skF_7')
      | ~ r2_hidden(A_35,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_80,c_16])).

tff(c_676,plain,(
    ! [B_68] : ~ r2_hidden(B_68,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_690,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_10,c_676])).

tff(c_696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_672,c_690])).

tff(c_697,plain,(
    ! [A_35] :
      ( r2_hidden(A_35,'#skF_4')
      | ~ r2_hidden(A_35,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_812,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_806,c_697])).

tff(c_814,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_812,c_2])).

tff(c_817,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_814])).

tff(c_821,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_119,c_817])).

tff(c_827,plain,
    ( ~ r2_hidden('#skF_1'('#skF_4','#skF_6'),'#skF_4')
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_821])).

tff(c_833,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_827])).

tff(c_835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_833])).

tff(c_836,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_874,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( r2_hidden(k4_tarski(A_93,B_94),k2_zfmisc_1(C_95,D_96))
      | ~ r2_hidden(B_94,D_96)
      | ~ r2_hidden(A_93,C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_837,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_842,plain,(
    k2_zfmisc_1('#skF_4','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_24])).

tff(c_848,plain,(
    ! [B_75,D_76,A_77,C_78] :
      ( r2_hidden(B_75,D_76)
      | ~ r2_hidden(k4_tarski(A_77,B_75),k2_zfmisc_1(C_78,D_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_851,plain,(
    ! [B_75,A_77] :
      ( r2_hidden(B_75,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_77,B_75),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_848])).

tff(c_888,plain,(
    ! [B_94,A_93] :
      ( r2_hidden(B_94,'#skF_7')
      | ~ r2_hidden(B_94,'#skF_5')
      | ~ r2_hidden(A_93,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_874,c_851])).

tff(c_892,plain,(
    ! [A_97] : ~ r2_hidden(A_97,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_888])).

tff(c_906,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_892])).

tff(c_912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_906])).

tff(c_927,plain,(
    ! [B_100] :
      ( r2_hidden(B_100,'#skF_7')
      | ~ r2_hidden(B_100,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_1004,plain,(
    ! [A_105] :
      ( r2_hidden('#skF_1'(A_105,'#skF_7'),'#skF_7')
      | A_105 = '#skF_7'
      | ~ r2_hidden('#skF_2'(A_105,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_927,c_4])).

tff(c_1016,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8,c_1004])).

tff(c_1023,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_836,c_836,c_1016])).

tff(c_914,plain,(
    ! [A_98,B_99] :
      ( r2_hidden(k4_tarski(A_98,B_99),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_99,'#skF_7')
      | ~ r2_hidden(A_98,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_874])).

tff(c_926,plain,(
    ! [B_99,A_98] :
      ( r2_hidden(B_99,'#skF_5')
      | ~ r2_hidden(B_99,'#skF_7')
      | ~ r2_hidden(A_98,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_914,c_14])).

tff(c_938,plain,(
    ! [A_101] : ~ r2_hidden(A_101,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_926])).

tff(c_952,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_938])).

tff(c_958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_952])).

tff(c_959,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,'#skF_5')
      | ~ r2_hidden(B_99,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_926])).

tff(c_1027,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1023,c_959])).

tff(c_913,plain,(
    ! [B_94] :
      ( r2_hidden(B_94,'#skF_7')
      | ~ r2_hidden(B_94,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_1029,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1027,c_2])).

tff(c_1032,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_836,c_1029])).

tff(c_1036,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_913,c_1032])).

tff(c_1039,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_5')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_1036])).

tff(c_1045,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_1039])).

tff(c_1047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_836,c_1045])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.45  
% 2.81/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.45  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.81/1.45  
% 2.81/1.45  %Foreground sorts:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Background operators:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Foreground operators:
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.81/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.81/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.45  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.45  
% 2.81/1.47  tff(f_57, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 2.81/1.47  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.81/1.47  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.81/1.47  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.81/1.47  tff(c_18, plain, ('#skF_7'!='#skF_5' | '#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.47  tff(c_25, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_18])).
% 2.81/1.47  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.47  tff(c_20, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.47  tff(c_10, plain, (![A_4]: (r2_hidden('#skF_3'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.81/1.47  tff(c_58, plain, (![A_31, B_32, C_33, D_34]: (r2_hidden(k4_tarski(A_31, B_32), k2_zfmisc_1(C_33, D_34)) | ~r2_hidden(B_32, D_34) | ~r2_hidden(A_31, C_33))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.47  tff(c_24, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.47  tff(c_35, plain, (![A_15, C_16, B_17, D_18]: (r2_hidden(A_15, C_16) | ~r2_hidden(k4_tarski(A_15, B_17), k2_zfmisc_1(C_16, D_18)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.47  tff(c_38, plain, (![A_15, B_17]: (r2_hidden(A_15, '#skF_6') | ~r2_hidden(k4_tarski(A_15, B_17), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_35])).
% 2.81/1.47  tff(c_76, plain, (![A_31, B_32]: (r2_hidden(A_31, '#skF_6') | ~r2_hidden(B_32, '#skF_5') | ~r2_hidden(A_31, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_38])).
% 2.81/1.47  tff(c_98, plain, (![B_37]: (~r2_hidden(B_37, '#skF_5'))), inference(splitLeft, [status(thm)], [c_76])).
% 2.81/1.47  tff(c_112, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_10, c_98])).
% 2.81/1.47  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_112])).
% 2.81/1.47  tff(c_120, plain, (![A_38]: (r2_hidden(A_38, '#skF_6') | ~r2_hidden(A_38, '#skF_4'))), inference(splitRight, [status(thm)], [c_76])).
% 2.81/1.47  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.47  tff(c_795, plain, (![A_73]: (r2_hidden('#skF_1'(A_73, '#skF_6'), '#skF_6') | A_73='#skF_6' | ~r2_hidden('#skF_2'(A_73, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_120, c_4])).
% 2.81/1.47  tff(c_799, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_6'), '#skF_6') | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_8, c_795])).
% 2.81/1.47  tff(c_806, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_25, c_25, c_799])).
% 2.81/1.47  tff(c_80, plain, (![A_35, B_36]: (r2_hidden(k4_tarski(A_35, B_36), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_36, '#skF_7') | ~r2_hidden(A_35, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_58])).
% 2.81/1.47  tff(c_14, plain, (![B_7, D_9, A_6, C_8]: (r2_hidden(B_7, D_9) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.47  tff(c_96, plain, (![B_36, A_35]: (r2_hidden(B_36, '#skF_5') | ~r2_hidden(B_36, '#skF_7') | ~r2_hidden(A_35, '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_14])).
% 2.81/1.47  tff(c_166, plain, (![A_41]: (~r2_hidden(A_41, '#skF_6'))), inference(splitLeft, [status(thm)], [c_96])).
% 2.81/1.47  tff(c_183, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_10, c_166])).
% 2.81/1.47  tff(c_211, plain, (![A_45]: (r2_hidden('#skF_3'(A_45), A_45) | A_45='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_10])).
% 2.81/1.47  tff(c_163, plain, (![A_35]: (~r2_hidden(A_35, '#skF_6'))), inference(splitLeft, [status(thm)], [c_96])).
% 2.81/1.47  tff(c_119, plain, (![A_31]: (r2_hidden(A_31, '#skF_6') | ~r2_hidden(A_31, '#skF_4'))), inference(splitRight, [status(thm)], [c_76])).
% 2.81/1.47  tff(c_164, plain, (![A_31]: (~r2_hidden(A_31, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_163, c_119])).
% 2.81/1.47  tff(c_215, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_211, c_164])).
% 2.81/1.47  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25, c_215])).
% 2.81/1.47  tff(c_225, plain, (![B_46]: (r2_hidden(B_46, '#skF_5') | ~r2_hidden(B_46, '#skF_7'))), inference(splitRight, [status(thm)], [c_96])).
% 2.81/1.47  tff(c_246, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_5') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_10, c_225])).
% 2.81/1.47  tff(c_247, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_246])).
% 2.81/1.47  tff(c_249, plain, ('#skF_7'!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_20])).
% 2.81/1.47  tff(c_22, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.47  tff(c_31, plain, (![B_11, D_12, A_13, C_14]: (r2_hidden(B_11, D_12) | ~r2_hidden(k4_tarski(A_13, B_11), k2_zfmisc_1(C_14, D_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.47  tff(c_34, plain, (![B_11, A_13]: (r2_hidden(B_11, '#skF_7') | ~r2_hidden(k4_tarski(A_13, B_11), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_31])).
% 2.81/1.47  tff(c_77, plain, (![B_32, A_31]: (r2_hidden(B_32, '#skF_7') | ~r2_hidden(B_32, '#skF_5') | ~r2_hidden(A_31, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_34])).
% 2.81/1.47  tff(c_131, plain, (![A_39]: (~r2_hidden(A_39, '#skF_4'))), inference(splitLeft, [status(thm)], [c_77])).
% 2.81/1.47  tff(c_145, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10, c_131])).
% 2.81/1.47  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_145])).
% 2.81/1.47  tff(c_153, plain, (![B_40]: (r2_hidden(B_40, '#skF_7') | ~r2_hidden(B_40, '#skF_5'))), inference(splitRight, [status(thm)], [c_77])).
% 2.81/1.47  tff(c_630, plain, (![A_67]: (r2_hidden('#skF_1'(A_67, '#skF_7'), '#skF_7') | A_67='#skF_7' | ~r2_hidden('#skF_2'(A_67, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_153, c_4])).
% 2.81/1.47  tff(c_634, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7'), '#skF_7') | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_8, c_630])).
% 2.81/1.47  tff(c_641, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_249, c_249, c_634])).
% 2.81/1.47  tff(c_224, plain, (![B_36]: (r2_hidden(B_36, '#skF_5') | ~r2_hidden(B_36, '#skF_7'))), inference(splitRight, [status(thm)], [c_96])).
% 2.81/1.47  tff(c_647, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_641, c_224])).
% 2.81/1.47  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.47  tff(c_152, plain, (![B_32]: (r2_hidden(B_32, '#skF_7') | ~r2_hidden(B_32, '#skF_5'))), inference(splitRight, [status(thm)], [c_77])).
% 2.81/1.47  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.47  tff(c_649, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_7'), '#skF_7') | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_647, c_2])).
% 2.81/1.47  tff(c_652, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_249, c_649])).
% 2.81/1.47  tff(c_656, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_152, c_652])).
% 2.81/1.47  tff(c_662, plain, (~r2_hidden('#skF_1'('#skF_5', '#skF_7'), '#skF_5') | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_6, c_656])).
% 2.81/1.47  tff(c_668, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_647, c_662])).
% 2.81/1.47  tff(c_670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_668])).
% 2.81/1.47  tff(c_672, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_246])).
% 2.81/1.47  tff(c_16, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.47  tff(c_95, plain, (![A_35, B_36]: (r2_hidden(A_35, '#skF_4') | ~r2_hidden(B_36, '#skF_7') | ~r2_hidden(A_35, '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_16])).
% 2.81/1.47  tff(c_676, plain, (![B_68]: (~r2_hidden(B_68, '#skF_7'))), inference(splitLeft, [status(thm)], [c_95])).
% 2.81/1.47  tff(c_690, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_10, c_676])).
% 2.81/1.47  tff(c_696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_672, c_690])).
% 2.81/1.47  tff(c_697, plain, (![A_35]: (r2_hidden(A_35, '#skF_4') | ~r2_hidden(A_35, '#skF_6'))), inference(splitRight, [status(thm)], [c_95])).
% 2.81/1.47  tff(c_812, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_806, c_697])).
% 2.81/1.47  tff(c_814, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_812, c_2])).
% 2.81/1.47  tff(c_817, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_25, c_814])).
% 2.81/1.47  tff(c_821, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_119, c_817])).
% 2.81/1.47  tff(c_827, plain, (~r2_hidden('#skF_1'('#skF_4', '#skF_6'), '#skF_4') | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_6, c_821])).
% 2.81/1.47  tff(c_833, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_812, c_827])).
% 2.81/1.47  tff(c_835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25, c_833])).
% 2.81/1.47  tff(c_836, plain, ('#skF_7'!='#skF_5'), inference(splitRight, [status(thm)], [c_18])).
% 2.81/1.47  tff(c_874, plain, (![A_93, B_94, C_95, D_96]: (r2_hidden(k4_tarski(A_93, B_94), k2_zfmisc_1(C_95, D_96)) | ~r2_hidden(B_94, D_96) | ~r2_hidden(A_93, C_95))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.47  tff(c_837, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_18])).
% 2.81/1.47  tff(c_842, plain, (k2_zfmisc_1('#skF_4', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_837, c_24])).
% 2.81/1.47  tff(c_848, plain, (![B_75, D_76, A_77, C_78]: (r2_hidden(B_75, D_76) | ~r2_hidden(k4_tarski(A_77, B_75), k2_zfmisc_1(C_78, D_76)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.47  tff(c_851, plain, (![B_75, A_77]: (r2_hidden(B_75, '#skF_7') | ~r2_hidden(k4_tarski(A_77, B_75), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_842, c_848])).
% 2.81/1.47  tff(c_888, plain, (![B_94, A_93]: (r2_hidden(B_94, '#skF_7') | ~r2_hidden(B_94, '#skF_5') | ~r2_hidden(A_93, '#skF_4'))), inference(resolution, [status(thm)], [c_874, c_851])).
% 2.81/1.47  tff(c_892, plain, (![A_97]: (~r2_hidden(A_97, '#skF_4'))), inference(splitLeft, [status(thm)], [c_888])).
% 2.81/1.47  tff(c_906, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10, c_892])).
% 2.81/1.47  tff(c_912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_906])).
% 2.81/1.47  tff(c_927, plain, (![B_100]: (r2_hidden(B_100, '#skF_7') | ~r2_hidden(B_100, '#skF_5'))), inference(splitRight, [status(thm)], [c_888])).
% 2.81/1.47  tff(c_1004, plain, (![A_105]: (r2_hidden('#skF_1'(A_105, '#skF_7'), '#skF_7') | A_105='#skF_7' | ~r2_hidden('#skF_2'(A_105, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_927, c_4])).
% 2.81/1.47  tff(c_1016, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7'), '#skF_7') | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_8, c_1004])).
% 2.81/1.47  tff(c_1023, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_836, c_836, c_1016])).
% 2.81/1.47  tff(c_914, plain, (![A_98, B_99]: (r2_hidden(k4_tarski(A_98, B_99), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_99, '#skF_7') | ~r2_hidden(A_98, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_842, c_874])).
% 2.81/1.47  tff(c_926, plain, (![B_99, A_98]: (r2_hidden(B_99, '#skF_5') | ~r2_hidden(B_99, '#skF_7') | ~r2_hidden(A_98, '#skF_4'))), inference(resolution, [status(thm)], [c_914, c_14])).
% 2.81/1.47  tff(c_938, plain, (![A_101]: (~r2_hidden(A_101, '#skF_4'))), inference(splitLeft, [status(thm)], [c_926])).
% 2.81/1.47  tff(c_952, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10, c_938])).
% 2.81/1.47  tff(c_958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_952])).
% 2.81/1.47  tff(c_959, plain, (![B_99]: (r2_hidden(B_99, '#skF_5') | ~r2_hidden(B_99, '#skF_7'))), inference(splitRight, [status(thm)], [c_926])).
% 2.81/1.47  tff(c_1027, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_1023, c_959])).
% 2.81/1.47  tff(c_913, plain, (![B_94]: (r2_hidden(B_94, '#skF_7') | ~r2_hidden(B_94, '#skF_5'))), inference(splitRight, [status(thm)], [c_888])).
% 2.81/1.47  tff(c_1029, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_7'), '#skF_7') | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1027, c_2])).
% 2.81/1.47  tff(c_1032, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_836, c_1029])).
% 2.81/1.47  tff(c_1036, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_913, c_1032])).
% 2.81/1.47  tff(c_1039, plain, (~r2_hidden('#skF_1'('#skF_5', '#skF_7'), '#skF_5') | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_6, c_1036])).
% 2.81/1.47  tff(c_1045, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_1039])).
% 2.81/1.47  tff(c_1047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_836, c_1045])).
% 2.81/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.47  
% 2.81/1.47  Inference rules
% 2.81/1.47  ----------------------
% 2.81/1.47  #Ref     : 0
% 2.81/1.47  #Sup     : 178
% 2.81/1.47  #Fact    : 0
% 2.81/1.47  #Define  : 0
% 2.81/1.47  #Split   : 15
% 2.81/1.47  #Chain   : 0
% 2.81/1.47  #Close   : 0
% 2.81/1.47  
% 2.81/1.47  Ordering : KBO
% 2.81/1.47  
% 2.81/1.47  Simplification rules
% 2.81/1.47  ----------------------
% 2.81/1.47  #Subsume      : 46
% 2.81/1.47  #Demod        : 42
% 2.81/1.47  #Tautology    : 57
% 2.81/1.47  #SimpNegUnit  : 47
% 2.81/1.47  #BackRed      : 29
% 2.81/1.47  
% 2.81/1.47  #Partial instantiations: 0
% 2.81/1.47  #Strategies tried      : 1
% 2.81/1.47  
% 2.81/1.47  Timing (in seconds)
% 2.81/1.47  ----------------------
% 2.81/1.48  Preprocessing        : 0.26
% 2.81/1.48  Parsing              : 0.14
% 2.81/1.48  CNF conversion       : 0.02
% 2.81/1.48  Main loop            : 0.39
% 2.81/1.48  Inferencing          : 0.16
% 2.81/1.48  Reduction            : 0.10
% 2.81/1.48  Demodulation         : 0.06
% 2.81/1.48  BG Simplification    : 0.02
% 2.81/1.48  Subsumption          : 0.08
% 2.81/1.48  Abstraction          : 0.02
% 2.81/1.48  MUC search           : 0.00
% 2.81/1.48  Cooper               : 0.00
% 2.81/1.48  Total                : 0.69
% 2.81/1.48  Index Insertion      : 0.00
% 2.81/1.48  Index Deletion       : 0.00
% 2.81/1.48  Index Matching       : 0.00
% 2.81/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
