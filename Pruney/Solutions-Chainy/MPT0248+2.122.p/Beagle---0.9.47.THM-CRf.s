%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:21 EST 2020

% Result     : Theorem 14.47s
% Output     : CNFRefutation 14.47s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 693 expanded)
%              Number of leaves         :   21 ( 222 expanded)
%              Depth                    :   15
%              Number of atoms          :  296 (1920 expanded)
%              Number of equality atoms :  164 (1388 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_36,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(c_42,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,
    ( k1_xboole_0 != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_57,plain,(
    k1_tarski('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_24,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_123,plain,(
    ! [D_41,B_42,A_43] :
      ( r2_hidden(D_41,B_42)
      | r2_hidden(D_41,A_43)
      | ~ r2_hidden(D_41,k2_xboole_0(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_138,plain,(
    ! [D_44] :
      ( r2_hidden(D_44,'#skF_7')
      | r2_hidden(D_44,'#skF_6')
      | ~ r2_hidden(D_44,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_123])).

tff(c_151,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_138])).

tff(c_152,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_424,plain,(
    ! [A_565,B_566] :
      ( '#skF_3'(A_565,B_566) = A_565
      | r2_hidden('#skF_4'(A_565,B_566),B_566)
      | k1_tarski(A_565) = B_566 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_87,plain,(
    ! [D_26,A_27,B_28] :
      ( ~ r2_hidden(D_26,A_27)
      | r2_hidden(D_26,k2_xboole_0(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_94,plain,(
    ! [D_29] :
      ( ~ r2_hidden(D_29,'#skF_6')
      | r2_hidden(D_29,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_87])).

tff(c_22,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,(
    ! [D_29] :
      ( D_29 = '#skF_5'
      | ~ r2_hidden(D_29,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_94,c_22])).

tff(c_3717,plain,(
    ! [A_2365] :
      ( '#skF_4'(A_2365,'#skF_6') = '#skF_5'
      | '#skF_3'(A_2365,'#skF_6') = A_2365
      | k1_tarski(A_2365) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_424,c_98])).

tff(c_3785,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_5'
    | '#skF_3'('#skF_5','#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3717,c_57])).

tff(c_3789,plain,(
    '#skF_3'('#skF_5','#skF_6') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3785])).

tff(c_26,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_3'(A_8,B_9),B_9)
      | '#skF_4'(A_8,B_9) != A_8
      | k1_tarski(A_8) = B_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3796,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | '#skF_4'('#skF_5','#skF_6') != '#skF_5'
    | k1_tarski('#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3789,c_26])).

tff(c_3817,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_5'
    | k1_tarski('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_3796])).

tff(c_3818,plain,(
    '#skF_4'('#skF_5','#skF_6') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_3817])).

tff(c_30,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_3'(A_8,B_9),B_9)
      | r2_hidden('#skF_4'(A_8,B_9),B_9)
      | k1_tarski(A_8) = B_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3793,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | k1_tarski('#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3789,c_30])).

tff(c_3814,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | k1_tarski('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_3793])).

tff(c_3815,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_3814])).

tff(c_3828,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3815,c_98])).

tff(c_3832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3818,c_3828])).

tff(c_3833,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3785])).

tff(c_160,plain,(
    ! [A_45,B_46] :
      ( '#skF_3'(A_45,B_46) = A_45
      | '#skF_4'(A_45,B_46) != A_45
      | k1_tarski(A_45) = B_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_318,plain,(
    ! [B_46] :
      ( B_46 != '#skF_6'
      | '#skF_3'('#skF_5',B_46) = '#skF_5'
      | '#skF_4'('#skF_5',B_46) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_57])).

tff(c_3834,plain,(
    '#skF_3'('#skF_5','#skF_6') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3785])).

tff(c_3849,plain,(
    '#skF_4'('#skF_5','#skF_6') != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_3834])).

tff(c_3858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3833,c_3849])).

tff(c_3860,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_25543,plain,(
    ! [A_18278,B_18279,C_18280] :
      ( r2_hidden('#skF_1'(A_18278,B_18279,C_18280),B_18279)
      | r2_hidden('#skF_1'(A_18278,B_18279,C_18280),A_18278)
      | r2_hidden('#skF_2'(A_18278,B_18279,C_18280),C_18280)
      | k2_xboole_0(A_18278,B_18279) = C_18280 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34460,plain,(
    ! [A_21804,B_21805] :
      ( r2_hidden('#skF_1'(A_21804,B_21805,B_21805),A_21804)
      | r2_hidden('#skF_2'(A_21804,B_21805,B_21805),B_21805)
      | k2_xboole_0(A_21804,B_21805) = B_21805 ) ),
    inference(resolution,[status(thm)],[c_25543,c_16])).

tff(c_16525,plain,(
    ! [A_11662,B_11663,C_11664] :
      ( r2_hidden('#skF_1'(A_11662,B_11663,C_11664),B_11663)
      | r2_hidden('#skF_1'(A_11662,B_11663,C_11664),A_11662)
      | ~ r2_hidden('#skF_2'(A_11662,B_11663,C_11664),B_11663)
      | k2_xboole_0(A_11662,B_11663) = C_11664 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16603,plain,(
    ! [A_11662,B_11663] :
      ( r2_hidden('#skF_1'(A_11662,B_11663,B_11663),A_11662)
      | ~ r2_hidden('#skF_2'(A_11662,B_11663,B_11663),B_11663)
      | k2_xboole_0(A_11662,B_11663) = B_11663 ) ),
    inference(resolution,[status(thm)],[c_16525,c_8])).

tff(c_34561,plain,(
    ! [A_21828,B_21829] :
      ( r2_hidden('#skF_1'(A_21828,B_21829,B_21829),A_21828)
      | k2_xboole_0(A_21828,B_21829) = B_21829 ) ),
    inference(resolution,[status(thm)],[c_34460,c_16603])).

tff(c_34846,plain,(
    ! [B_21941] :
      ( '#skF_1'('#skF_6',B_21941,B_21941) = '#skF_5'
      | k2_xboole_0('#skF_6',B_21941) = B_21941 ) ),
    inference(resolution,[status(thm)],[c_34561,c_98])).

tff(c_34914,plain,
    ( k1_xboole_0 = '#skF_6'
    | '#skF_1'('#skF_6',k1_xboole_0,k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_34846,c_20])).

tff(c_34953,plain,(
    '#skF_1'('#skF_6',k1_xboole_0,k1_xboole_0) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_34914])).

tff(c_34555,plain,(
    ! [A_21804,B_21805] :
      ( r2_hidden('#skF_1'(A_21804,B_21805,B_21805),A_21804)
      | k2_xboole_0(A_21804,B_21805) = B_21805 ) ),
    inference(resolution,[status(thm)],[c_34460,c_16603])).

tff(c_34965,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k2_xboole_0('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34953,c_34555])).

tff(c_34988,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_34965])).

tff(c_34990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3860,c_34988])).

tff(c_34991,plain,(
    k1_tarski('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_34992,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_34997,plain,(
    ! [A_7] : k2_xboole_0(A_7,'#skF_6') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34992,c_20])).

tff(c_35071,plain,(
    ! [D_22007,B_22008,A_22009] :
      ( r2_hidden(D_22007,B_22008)
      | r2_hidden(D_22007,A_22009)
      | ~ r2_hidden(D_22007,k2_xboole_0(A_22009,B_22008)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_35086,plain,(
    ! [D_22010] :
      ( r2_hidden(D_22010,'#skF_7')
      | r2_hidden(D_22010,'#skF_6')
      | ~ r2_hidden(D_22010,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_35071])).

tff(c_35095,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_35086])).

tff(c_35096,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_35095])).

tff(c_35048,plain,(
    ! [D_21997,B_21998,A_21999] :
      ( ~ r2_hidden(D_21997,B_21998)
      | r2_hidden(D_21997,k2_xboole_0(A_21999,B_21998)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_35051,plain,(
    ! [D_21997,A_7] :
      ( ~ r2_hidden(D_21997,'#skF_6')
      | r2_hidden(D_21997,A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34997,c_35048])).

tff(c_35106,plain,(
    ! [A_22011] : r2_hidden('#skF_5',A_22011) ),
    inference(resolution,[status(thm)],[c_35096,c_35051])).

tff(c_35142,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_35106,c_22])).

tff(c_35140,plain,(
    ! [A_8] : A_8 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_35106,c_22])).

tff(c_35190,plain,(
    ! [A_22431] : A_22431 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_35142,c_35140])).

tff(c_35225,plain,(
    k2_xboole_0('#skF_6','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35190,c_46])).

tff(c_35234,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34997,c_35225])).

tff(c_35236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_35234])).

tff(c_35237,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_35095])).

tff(c_35624,plain,(
    ! [A_23542,B_23543] :
      ( '#skF_3'(A_23542,B_23543) = A_23542
      | r2_hidden('#skF_4'(A_23542,B_23543),B_23543)
      | k1_tarski(A_23542) = B_23543 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_35056,plain,(
    ! [D_22002] :
      ( ~ r2_hidden(D_22002,'#skF_7')
      | r2_hidden(D_22002,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_35048])).

tff(c_35060,plain,(
    ! [D_22002] :
      ( D_22002 = '#skF_5'
      | ~ r2_hidden(D_22002,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_35056,c_22])).

tff(c_38830,plain,(
    ! [A_25203] :
      ( '#skF_4'(A_25203,'#skF_7') = '#skF_5'
      | '#skF_3'(A_25203,'#skF_7') = A_25203
      | k1_tarski(A_25203) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_35624,c_35060])).

tff(c_38904,plain,
    ( '#skF_4'('#skF_5','#skF_7') = '#skF_5'
    | '#skF_3'('#skF_5','#skF_7') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_38830,c_34991])).

tff(c_38935,plain,(
    '#skF_3'('#skF_5','#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_38904])).

tff(c_38951,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | '#skF_4'('#skF_5','#skF_7') != '#skF_5'
    | k1_tarski('#skF_5') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_38935,c_26])).

tff(c_38973,plain,
    ( '#skF_4'('#skF_5','#skF_7') != '#skF_5'
    | k1_tarski('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35237,c_38951])).

tff(c_38974,plain,(
    '#skF_4'('#skF_5','#skF_7') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_34991,c_38973])).

tff(c_38939,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_4'('#skF_5','#skF_7'),'#skF_7')
    | k1_tarski('#skF_5') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_38935,c_30])).

tff(c_38966,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_7'),'#skF_7')
    | k1_tarski('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35237,c_38939])).

tff(c_38967,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_34991,c_38966])).

tff(c_38982,plain,(
    '#skF_4'('#skF_5','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38967,c_35060])).

tff(c_38986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38974,c_38982])).

tff(c_38987,plain,(
    '#skF_4'('#skF_5','#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_38904])).

tff(c_35246,plain,(
    ! [A_22872,B_22873] :
      ( '#skF_3'(A_22872,B_22873) = A_22872
      | '#skF_4'(A_22872,B_22873) != A_22872
      | k1_tarski(A_22872) = B_22873 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_35356,plain,(
    ! [B_22873] :
      ( B_22873 != '#skF_7'
      | '#skF_3'('#skF_5',B_22873) = '#skF_5'
      | '#skF_4'('#skF_5',B_22873) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35246,c_34991])).

tff(c_38988,plain,(
    '#skF_3'('#skF_5','#skF_7') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_38904])).

tff(c_39006,plain,(
    '#skF_4'('#skF_5','#skF_7') != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_35356,c_38988])).

tff(c_39018,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38987,c_39006])).

tff(c_39019,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_39020,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_39045,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39020,c_39020,c_44])).

tff(c_39203,plain,(
    ! [A_25382] :
      ( '#skF_3'(A_25382,'#skF_7') = A_25382
      | '#skF_4'(A_25382,'#skF_7') != A_25382
      | k1_tarski(A_25382) = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_39206,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_3'('#skF_5','#skF_7') = '#skF_5'
    | '#skF_4'('#skF_5','#skF_7') != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_39203,c_39020])).

tff(c_39303,plain,
    ( '#skF_3'('#skF_5','#skF_7') = '#skF_5'
    | '#skF_4'('#skF_5','#skF_7') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_39045,c_39206])).

tff(c_39306,plain,(
    '#skF_4'('#skF_5','#skF_7') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_39303])).

tff(c_39309,plain,(
    ! [A_25868,B_25869] :
      ( '#skF_3'(A_25868,B_25869) = A_25868
      | r2_hidden('#skF_4'(A_25868,B_25869),B_25869)
      | k1_tarski(A_25868) = B_25869 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_39039,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39020,c_46])).

tff(c_39077,plain,(
    ! [D_25370,B_25371,A_25372] :
      ( ~ r2_hidden(D_25370,B_25371)
      | r2_hidden(D_25370,k2_xboole_0(A_25372,B_25371)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_39080,plain,(
    ! [D_25370] :
      ( ~ r2_hidden(D_25370,'#skF_7')
      | r2_hidden(D_25370,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39039,c_39077])).

tff(c_42794,plain,(
    ! [A_27809] :
      ( r2_hidden('#skF_4'(A_27809,'#skF_7'),'#skF_6')
      | '#skF_3'(A_27809,'#skF_7') = A_27809
      | k1_tarski(A_27809) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_39309,c_39080])).

tff(c_39046,plain,(
    ! [C_25362,A_25363] :
      ( C_25362 = A_25363
      | ~ r2_hidden(C_25362,k1_tarski(A_25363)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_39049,plain,(
    ! [C_25362] :
      ( C_25362 = '#skF_5'
      | ~ r2_hidden(C_25362,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39020,c_39046])).

tff(c_42814,plain,(
    ! [A_27832] :
      ( '#skF_4'(A_27832,'#skF_7') = '#skF_5'
      | '#skF_3'(A_27832,'#skF_7') = A_27832
      | k1_tarski(A_27832) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_42794,c_39049])).

tff(c_42829,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_4'('#skF_5','#skF_7') = '#skF_5'
    | '#skF_3'('#skF_5','#skF_7') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_42814,c_39020])).

tff(c_42883,plain,(
    '#skF_3'('#skF_5','#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_39306,c_39045,c_42829])).

tff(c_42899,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_4'('#skF_5','#skF_7'),'#skF_7')
    | k1_tarski('#skF_5') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_42883,c_30])).

tff(c_42919,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_4'('#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39020,c_42899])).

tff(c_42920,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_4'('#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_39045,c_42919])).

tff(c_42927,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_42920])).

tff(c_52099,plain,(
    ! [A_33446,B_33447,C_33448] :
      ( r2_hidden('#skF_1'(A_33446,B_33447,C_33448),B_33447)
      | r2_hidden('#skF_1'(A_33446,B_33447,C_33448),A_33446)
      | r2_hidden('#skF_2'(A_33446,B_33447,C_33448),C_33448)
      | k2_xboole_0(A_33446,B_33447) = C_33448 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_72409,plain,(
    ! [A_45260,B_45261] :
      ( r2_hidden('#skF_1'(A_45260,B_45261,B_45261),A_45260)
      | r2_hidden('#skF_2'(A_45260,B_45261,B_45261),B_45261)
      | k2_xboole_0(A_45260,B_45261) = B_45261 ) ),
    inference(resolution,[status(thm)],[c_52099,c_16])).

tff(c_53621,plain,(
    ! [A_36160,B_36161,C_36162] :
      ( r2_hidden('#skF_1'(A_36160,B_36161,C_36162),B_36161)
      | r2_hidden('#skF_1'(A_36160,B_36161,C_36162),A_36160)
      | ~ r2_hidden('#skF_2'(A_36160,B_36161,C_36162),B_36161)
      | k2_xboole_0(A_36160,B_36161) = C_36162 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_53695,plain,(
    ! [A_36160,B_36161] :
      ( r2_hidden('#skF_1'(A_36160,B_36161,B_36161),A_36160)
      | ~ r2_hidden('#skF_2'(A_36160,B_36161,B_36161),B_36161)
      | k2_xboole_0(A_36160,B_36161) = B_36161 ) ),
    inference(resolution,[status(thm)],[c_53621,c_8])).

tff(c_72501,plain,(
    ! [A_45284,B_45285] :
      ( r2_hidden('#skF_1'(A_45284,B_45285,B_45285),A_45284)
      | k2_xboole_0(A_45284,B_45285) = B_45285 ) ),
    inference(resolution,[status(thm)],[c_72409,c_53695])).

tff(c_72743,plain,(
    ! [B_45375] :
      ( r2_hidden('#skF_1'('#skF_7',B_45375,B_45375),'#skF_6')
      | k2_xboole_0('#skF_7',B_45375) = B_45375 ) ),
    inference(resolution,[status(thm)],[c_72501,c_39080])).

tff(c_72770,plain,(
    ! [B_45398] :
      ( '#skF_1'('#skF_7',B_45398,B_45398) = '#skF_5'
      | k2_xboole_0('#skF_7',B_45398) = B_45398 ) ),
    inference(resolution,[status(thm)],[c_72743,c_39049])).

tff(c_72828,plain,
    ( k1_xboole_0 = '#skF_7'
    | '#skF_1'('#skF_7',k1_xboole_0,k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_72770,c_20])).

tff(c_72853,plain,(
    '#skF_1'('#skF_7',k1_xboole_0,k1_xboole_0) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_39019,c_72828])).

tff(c_72497,plain,(
    ! [A_45260,B_45261] :
      ( r2_hidden('#skF_1'(A_45260,B_45261,B_45261),A_45260)
      | k2_xboole_0(A_45260,B_45261) = B_45261 ) ),
    inference(resolution,[status(thm)],[c_72409,c_53695])).

tff(c_72865,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k2_xboole_0('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_72853,c_72497])).

tff(c_72890,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_72865])).

tff(c_72892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39019,c_42927,c_72890])).

tff(c_72893,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_42920])).

tff(c_72933,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_72893,c_39080])).

tff(c_72936,plain,(
    '#skF_4'('#skF_5','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_72933,c_39049])).

tff(c_72940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39306,c_72936])).

tff(c_72942,plain,(
    '#skF_4'('#skF_5','#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_39303])).

tff(c_72941,plain,(
    '#skF_3'('#skF_5','#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_39303])).

tff(c_73192,plain,(
    ! [A_45854,B_45855] :
      ( ~ r2_hidden('#skF_3'(A_45854,B_45855),B_45855)
      | '#skF_4'(A_45854,B_45855) != A_45854
      | k1_tarski(A_45854) = B_45855 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_73220,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | '#skF_4'('#skF_5','#skF_7') != '#skF_5'
    | k1_tarski('#skF_5') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_72941,c_73192])).

tff(c_73252,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39020,c_72942,c_73220])).

tff(c_73253,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_39045,c_73252])).

tff(c_88960,plain,(
    ! [A_58155,B_58156,C_58157] :
      ( r2_hidden('#skF_1'(A_58155,B_58156,C_58157),B_58156)
      | r2_hidden('#skF_1'(A_58155,B_58156,C_58157),A_58155)
      | r2_hidden('#skF_2'(A_58155,B_58156,C_58157),C_58157)
      | k2_xboole_0(A_58155,B_58156) = C_58157 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_89042,plain,(
    ! [A_58155,B_58156] :
      ( r2_hidden('#skF_1'(A_58155,B_58156,B_58156),A_58155)
      | r2_hidden('#skF_2'(A_58155,B_58156,B_58156),B_58156)
      | k2_xboole_0(A_58155,B_58156) = B_58156 ) ),
    inference(resolution,[status(thm)],[c_88960,c_16])).

tff(c_89340,plain,(
    ! [A_58386,B_58387,C_58388] :
      ( r2_hidden('#skF_1'(A_58386,B_58387,C_58388),B_58387)
      | r2_hidden('#skF_1'(A_58386,B_58387,C_58388),A_58386)
      | ~ r2_hidden('#skF_2'(A_58386,B_58387,C_58388),B_58387)
      | k2_xboole_0(A_58386,B_58387) = C_58388 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98562,plain,(
    ! [A_61792,B_61793] :
      ( r2_hidden('#skF_1'(A_61792,B_61793,B_61793),A_61792)
      | ~ r2_hidden('#skF_2'(A_61792,B_61793,B_61793),B_61793)
      | k2_xboole_0(A_61792,B_61793) = B_61793 ) ),
    inference(resolution,[status(thm)],[c_89340,c_8])).

tff(c_98605,plain,(
    ! [A_61816,B_61817] :
      ( r2_hidden('#skF_1'(A_61816,B_61817,B_61817),A_61816)
      | k2_xboole_0(A_61816,B_61817) = B_61817 ) ),
    inference(resolution,[status(thm)],[c_89042,c_98562])).

tff(c_98843,plain,(
    ! [B_61907] :
      ( r2_hidden('#skF_1'('#skF_7',B_61907,B_61907),'#skF_6')
      | k2_xboole_0('#skF_7',B_61907) = B_61907 ) ),
    inference(resolution,[status(thm)],[c_98605,c_39080])).

tff(c_98870,plain,(
    ! [B_61930] :
      ( '#skF_1'('#skF_7',B_61930,B_61930) = '#skF_5'
      | k2_xboole_0('#skF_7',B_61930) = B_61930 ) ),
    inference(resolution,[status(thm)],[c_98843,c_39049])).

tff(c_98928,plain,
    ( k1_xboole_0 = '#skF_7'
    | '#skF_1'('#skF_7',k1_xboole_0,k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_98870,c_20])).

tff(c_98953,plain,(
    '#skF_1'('#skF_7',k1_xboole_0,k1_xboole_0) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_39019,c_98928])).

tff(c_98595,plain,(
    ! [A_58155,B_58156] :
      ( r2_hidden('#skF_1'(A_58155,B_58156,B_58156),A_58155)
      | k2_xboole_0(A_58155,B_58156) = B_58156 ) ),
    inference(resolution,[status(thm)],[c_89042,c_98562])).

tff(c_98965,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k2_xboole_0('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_98953,c_98595])).

tff(c_98990,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_98965])).

tff(c_98992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39019,c_73253,c_98990])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.47/5.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.47/5.87  
% 14.47/5.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.47/5.87  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 14.47/5.87  
% 14.47/5.87  %Foreground sorts:
% 14.47/5.87  
% 14.47/5.87  
% 14.47/5.87  %Background operators:
% 14.47/5.87  
% 14.47/5.87  
% 14.47/5.87  %Foreground operators:
% 14.47/5.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.47/5.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.47/5.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.47/5.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.47/5.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.47/5.87  tff('#skF_7', type, '#skF_7': $i).
% 14.47/5.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 14.47/5.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.47/5.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.47/5.87  tff('#skF_5', type, '#skF_5': $i).
% 14.47/5.87  tff('#skF_6', type, '#skF_6': $i).
% 14.47/5.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.47/5.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.47/5.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.47/5.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.47/5.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.47/5.87  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 14.47/5.87  
% 14.47/5.90  tff(f_68, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 14.47/5.90  tff(f_43, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 14.47/5.90  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 14.47/5.90  tff(f_36, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 14.47/5.90  tff(c_42, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.47/5.90  tff(c_58, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_42])).
% 14.47/5.90  tff(c_40, plain, (k1_xboole_0!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.47/5.90  tff(c_57, plain, (k1_tarski('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_40])).
% 14.47/5.90  tff(c_24, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/5.90  tff(c_46, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.47/5.90  tff(c_123, plain, (![D_41, B_42, A_43]: (r2_hidden(D_41, B_42) | r2_hidden(D_41, A_43) | ~r2_hidden(D_41, k2_xboole_0(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_138, plain, (![D_44]: (r2_hidden(D_44, '#skF_7') | r2_hidden(D_44, '#skF_6') | ~r2_hidden(D_44, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_123])).
% 14.47/5.90  tff(c_151, plain, (r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_138])).
% 14.47/5.90  tff(c_152, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_151])).
% 14.47/5.90  tff(c_424, plain, (![A_565, B_566]: ('#skF_3'(A_565, B_566)=A_565 | r2_hidden('#skF_4'(A_565, B_566), B_566) | k1_tarski(A_565)=B_566)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/5.90  tff(c_87, plain, (![D_26, A_27, B_28]: (~r2_hidden(D_26, A_27) | r2_hidden(D_26, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_94, plain, (![D_29]: (~r2_hidden(D_29, '#skF_6') | r2_hidden(D_29, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_87])).
% 14.47/5.90  tff(c_22, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/5.90  tff(c_98, plain, (![D_29]: (D_29='#skF_5' | ~r2_hidden(D_29, '#skF_6'))), inference(resolution, [status(thm)], [c_94, c_22])).
% 14.47/5.90  tff(c_3717, plain, (![A_2365]: ('#skF_4'(A_2365, '#skF_6')='#skF_5' | '#skF_3'(A_2365, '#skF_6')=A_2365 | k1_tarski(A_2365)='#skF_6')), inference(resolution, [status(thm)], [c_424, c_98])).
% 14.47/5.90  tff(c_3785, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_5' | '#skF_3'('#skF_5', '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3717, c_57])).
% 14.47/5.90  tff(c_3789, plain, ('#skF_3'('#skF_5', '#skF_6')='#skF_5'), inference(splitLeft, [status(thm)], [c_3785])).
% 14.47/5.90  tff(c_26, plain, (![A_8, B_9]: (~r2_hidden('#skF_3'(A_8, B_9), B_9) | '#skF_4'(A_8, B_9)!=A_8 | k1_tarski(A_8)=B_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/5.90  tff(c_3796, plain, (~r2_hidden('#skF_5', '#skF_6') | '#skF_4'('#skF_5', '#skF_6')!='#skF_5' | k1_tarski('#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3789, c_26])).
% 14.47/5.90  tff(c_3817, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_5' | k1_tarski('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_3796])).
% 14.47/5.90  tff(c_3818, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_57, c_3817])).
% 14.47/5.90  tff(c_30, plain, (![A_8, B_9]: (~r2_hidden('#skF_3'(A_8, B_9), B_9) | r2_hidden('#skF_4'(A_8, B_9), B_9) | k1_tarski(A_8)=B_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/5.90  tff(c_3793, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | k1_tarski('#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3789, c_30])).
% 14.47/5.90  tff(c_3814, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | k1_tarski('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_3793])).
% 14.47/5.90  tff(c_3815, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_57, c_3814])).
% 14.47/5.90  tff(c_3828, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_3815, c_98])).
% 14.47/5.90  tff(c_3832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3818, c_3828])).
% 14.47/5.90  tff(c_3833, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_3785])).
% 14.47/5.90  tff(c_160, plain, (![A_45, B_46]: ('#skF_3'(A_45, B_46)=A_45 | '#skF_4'(A_45, B_46)!=A_45 | k1_tarski(A_45)=B_46)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/5.90  tff(c_318, plain, (![B_46]: (B_46!='#skF_6' | '#skF_3'('#skF_5', B_46)='#skF_5' | '#skF_4'('#skF_5', B_46)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_160, c_57])).
% 14.47/5.90  tff(c_3834, plain, ('#skF_3'('#skF_5', '#skF_6')!='#skF_5'), inference(splitRight, [status(thm)], [c_3785])).
% 14.47/5.90  tff(c_3849, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_318, c_3834])).
% 14.47/5.90  tff(c_3858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3833, c_3849])).
% 14.47/5.90  tff(c_3860, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_151])).
% 14.47/5.90  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 14.47/5.90  tff(c_25543, plain, (![A_18278, B_18279, C_18280]: (r2_hidden('#skF_1'(A_18278, B_18279, C_18280), B_18279) | r2_hidden('#skF_1'(A_18278, B_18279, C_18280), A_18278) | r2_hidden('#skF_2'(A_18278, B_18279, C_18280), C_18280) | k2_xboole_0(A_18278, B_18279)=C_18280)), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_34460, plain, (![A_21804, B_21805]: (r2_hidden('#skF_1'(A_21804, B_21805, B_21805), A_21804) | r2_hidden('#skF_2'(A_21804, B_21805, B_21805), B_21805) | k2_xboole_0(A_21804, B_21805)=B_21805)), inference(resolution, [status(thm)], [c_25543, c_16])).
% 14.47/5.90  tff(c_16525, plain, (![A_11662, B_11663, C_11664]: (r2_hidden('#skF_1'(A_11662, B_11663, C_11664), B_11663) | r2_hidden('#skF_1'(A_11662, B_11663, C_11664), A_11662) | ~r2_hidden('#skF_2'(A_11662, B_11663, C_11664), B_11663) | k2_xboole_0(A_11662, B_11663)=C_11664)), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_16603, plain, (![A_11662, B_11663]: (r2_hidden('#skF_1'(A_11662, B_11663, B_11663), A_11662) | ~r2_hidden('#skF_2'(A_11662, B_11663, B_11663), B_11663) | k2_xboole_0(A_11662, B_11663)=B_11663)), inference(resolution, [status(thm)], [c_16525, c_8])).
% 14.47/5.90  tff(c_34561, plain, (![A_21828, B_21829]: (r2_hidden('#skF_1'(A_21828, B_21829, B_21829), A_21828) | k2_xboole_0(A_21828, B_21829)=B_21829)), inference(resolution, [status(thm)], [c_34460, c_16603])).
% 14.47/5.90  tff(c_34846, plain, (![B_21941]: ('#skF_1'('#skF_6', B_21941, B_21941)='#skF_5' | k2_xboole_0('#skF_6', B_21941)=B_21941)), inference(resolution, [status(thm)], [c_34561, c_98])).
% 14.47/5.90  tff(c_34914, plain, (k1_xboole_0='#skF_6' | '#skF_1'('#skF_6', k1_xboole_0, k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_34846, c_20])).
% 14.47/5.90  tff(c_34953, plain, ('#skF_1'('#skF_6', k1_xboole_0, k1_xboole_0)='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_58, c_34914])).
% 14.47/5.90  tff(c_34555, plain, (![A_21804, B_21805]: (r2_hidden('#skF_1'(A_21804, B_21805, B_21805), A_21804) | k2_xboole_0(A_21804, B_21805)=B_21805)), inference(resolution, [status(thm)], [c_34460, c_16603])).
% 14.47/5.90  tff(c_34965, plain, (r2_hidden('#skF_5', '#skF_6') | k2_xboole_0('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34953, c_34555])).
% 14.47/5.90  tff(c_34988, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_34965])).
% 14.47/5.90  tff(c_34990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_3860, c_34988])).
% 14.47/5.90  tff(c_34991, plain, (k1_tarski('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_42])).
% 14.47/5.90  tff(c_34992, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 14.47/5.90  tff(c_34997, plain, (![A_7]: (k2_xboole_0(A_7, '#skF_6')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_34992, c_20])).
% 14.47/5.90  tff(c_35071, plain, (![D_22007, B_22008, A_22009]: (r2_hidden(D_22007, B_22008) | r2_hidden(D_22007, A_22009) | ~r2_hidden(D_22007, k2_xboole_0(A_22009, B_22008)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_35086, plain, (![D_22010]: (r2_hidden(D_22010, '#skF_7') | r2_hidden(D_22010, '#skF_6') | ~r2_hidden(D_22010, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_35071])).
% 14.47/5.90  tff(c_35095, plain, (r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_35086])).
% 14.47/5.90  tff(c_35096, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_35095])).
% 14.47/5.90  tff(c_35048, plain, (![D_21997, B_21998, A_21999]: (~r2_hidden(D_21997, B_21998) | r2_hidden(D_21997, k2_xboole_0(A_21999, B_21998)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_35051, plain, (![D_21997, A_7]: (~r2_hidden(D_21997, '#skF_6') | r2_hidden(D_21997, A_7))), inference(superposition, [status(thm), theory('equality')], [c_34997, c_35048])).
% 14.47/5.90  tff(c_35106, plain, (![A_22011]: (r2_hidden('#skF_5', A_22011))), inference(resolution, [status(thm)], [c_35096, c_35051])).
% 14.47/5.90  tff(c_35142, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_35106, c_22])).
% 14.47/5.90  tff(c_35140, plain, (![A_8]: (A_8='#skF_5')), inference(resolution, [status(thm)], [c_35106, c_22])).
% 14.47/5.90  tff(c_35190, plain, (![A_22431]: (A_22431='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_35142, c_35140])).
% 14.47/5.90  tff(c_35225, plain, (k2_xboole_0('#skF_6', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35190, c_46])).
% 14.47/5.90  tff(c_35234, plain, (k1_tarski('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_34997, c_35225])).
% 14.47/5.90  tff(c_35236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_35234])).
% 14.47/5.90  tff(c_35237, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_35095])).
% 14.47/5.90  tff(c_35624, plain, (![A_23542, B_23543]: ('#skF_3'(A_23542, B_23543)=A_23542 | r2_hidden('#skF_4'(A_23542, B_23543), B_23543) | k1_tarski(A_23542)=B_23543)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/5.90  tff(c_35056, plain, (![D_22002]: (~r2_hidden(D_22002, '#skF_7') | r2_hidden(D_22002, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_35048])).
% 14.47/5.90  tff(c_35060, plain, (![D_22002]: (D_22002='#skF_5' | ~r2_hidden(D_22002, '#skF_7'))), inference(resolution, [status(thm)], [c_35056, c_22])).
% 14.47/5.90  tff(c_38830, plain, (![A_25203]: ('#skF_4'(A_25203, '#skF_7')='#skF_5' | '#skF_3'(A_25203, '#skF_7')=A_25203 | k1_tarski(A_25203)='#skF_7')), inference(resolution, [status(thm)], [c_35624, c_35060])).
% 14.47/5.90  tff(c_38904, plain, ('#skF_4'('#skF_5', '#skF_7')='#skF_5' | '#skF_3'('#skF_5', '#skF_7')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_38830, c_34991])).
% 14.47/5.90  tff(c_38935, plain, ('#skF_3'('#skF_5', '#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_38904])).
% 14.47/5.90  tff(c_38951, plain, (~r2_hidden('#skF_5', '#skF_7') | '#skF_4'('#skF_5', '#skF_7')!='#skF_5' | k1_tarski('#skF_5')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_38935, c_26])).
% 14.47/5.90  tff(c_38973, plain, ('#skF_4'('#skF_5', '#skF_7')!='#skF_5' | k1_tarski('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_35237, c_38951])).
% 14.47/5.90  tff(c_38974, plain, ('#skF_4'('#skF_5', '#skF_7')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_34991, c_38973])).
% 14.47/5.90  tff(c_38939, plain, (~r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_4'('#skF_5', '#skF_7'), '#skF_7') | k1_tarski('#skF_5')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_38935, c_30])).
% 14.47/5.90  tff(c_38966, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_7'), '#skF_7') | k1_tarski('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_35237, c_38939])).
% 14.47/5.90  tff(c_38967, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_34991, c_38966])).
% 14.47/5.90  tff(c_38982, plain, ('#skF_4'('#skF_5', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_38967, c_35060])).
% 14.47/5.90  tff(c_38986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38974, c_38982])).
% 14.47/5.90  tff(c_38987, plain, ('#skF_4'('#skF_5', '#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_38904])).
% 14.47/5.90  tff(c_35246, plain, (![A_22872, B_22873]: ('#skF_3'(A_22872, B_22873)=A_22872 | '#skF_4'(A_22872, B_22873)!=A_22872 | k1_tarski(A_22872)=B_22873)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/5.90  tff(c_35356, plain, (![B_22873]: (B_22873!='#skF_7' | '#skF_3'('#skF_5', B_22873)='#skF_5' | '#skF_4'('#skF_5', B_22873)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35246, c_34991])).
% 14.47/5.90  tff(c_38988, plain, ('#skF_3'('#skF_5', '#skF_7')!='#skF_5'), inference(splitRight, [status(thm)], [c_38904])).
% 14.47/5.90  tff(c_39006, plain, ('#skF_4'('#skF_5', '#skF_7')!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_35356, c_38988])).
% 14.47/5.90  tff(c_39018, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38987, c_39006])).
% 14.47/5.90  tff(c_39019, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_40])).
% 14.47/5.90  tff(c_39020, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_40])).
% 14.47/5.90  tff(c_44, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.47/5.90  tff(c_39045, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_39020, c_39020, c_44])).
% 14.47/5.90  tff(c_39203, plain, (![A_25382]: ('#skF_3'(A_25382, '#skF_7')=A_25382 | '#skF_4'(A_25382, '#skF_7')!=A_25382 | k1_tarski(A_25382)='#skF_7')), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/5.90  tff(c_39206, plain, ('#skF_7'='#skF_6' | '#skF_3'('#skF_5', '#skF_7')='#skF_5' | '#skF_4'('#skF_5', '#skF_7')!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_39203, c_39020])).
% 14.47/5.90  tff(c_39303, plain, ('#skF_3'('#skF_5', '#skF_7')='#skF_5' | '#skF_4'('#skF_5', '#skF_7')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_39045, c_39206])).
% 14.47/5.90  tff(c_39306, plain, ('#skF_4'('#skF_5', '#skF_7')!='#skF_5'), inference(splitLeft, [status(thm)], [c_39303])).
% 14.47/5.90  tff(c_39309, plain, (![A_25868, B_25869]: ('#skF_3'(A_25868, B_25869)=A_25868 | r2_hidden('#skF_4'(A_25868, B_25869), B_25869) | k1_tarski(A_25868)=B_25869)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/5.90  tff(c_39039, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_39020, c_46])).
% 14.47/5.90  tff(c_39077, plain, (![D_25370, B_25371, A_25372]: (~r2_hidden(D_25370, B_25371) | r2_hidden(D_25370, k2_xboole_0(A_25372, B_25371)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_39080, plain, (![D_25370]: (~r2_hidden(D_25370, '#skF_7') | r2_hidden(D_25370, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_39039, c_39077])).
% 14.47/5.90  tff(c_42794, plain, (![A_27809]: (r2_hidden('#skF_4'(A_27809, '#skF_7'), '#skF_6') | '#skF_3'(A_27809, '#skF_7')=A_27809 | k1_tarski(A_27809)='#skF_7')), inference(resolution, [status(thm)], [c_39309, c_39080])).
% 14.47/5.90  tff(c_39046, plain, (![C_25362, A_25363]: (C_25362=A_25363 | ~r2_hidden(C_25362, k1_tarski(A_25363)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/5.90  tff(c_39049, plain, (![C_25362]: (C_25362='#skF_5' | ~r2_hidden(C_25362, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_39020, c_39046])).
% 14.47/5.90  tff(c_42814, plain, (![A_27832]: ('#skF_4'(A_27832, '#skF_7')='#skF_5' | '#skF_3'(A_27832, '#skF_7')=A_27832 | k1_tarski(A_27832)='#skF_7')), inference(resolution, [status(thm)], [c_42794, c_39049])).
% 14.47/5.90  tff(c_42829, plain, ('#skF_7'='#skF_6' | '#skF_4'('#skF_5', '#skF_7')='#skF_5' | '#skF_3'('#skF_5', '#skF_7')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_42814, c_39020])).
% 14.47/5.90  tff(c_42883, plain, ('#skF_3'('#skF_5', '#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_39306, c_39045, c_42829])).
% 14.47/5.90  tff(c_42899, plain, (~r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_4'('#skF_5', '#skF_7'), '#skF_7') | k1_tarski('#skF_5')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_42883, c_30])).
% 14.47/5.90  tff(c_42919, plain, (~r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_4'('#skF_5', '#skF_7'), '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_39020, c_42899])).
% 14.47/5.90  tff(c_42920, plain, (~r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_4'('#skF_5', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_39045, c_42919])).
% 14.47/5.90  tff(c_42927, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_42920])).
% 14.47/5.90  tff(c_52099, plain, (![A_33446, B_33447, C_33448]: (r2_hidden('#skF_1'(A_33446, B_33447, C_33448), B_33447) | r2_hidden('#skF_1'(A_33446, B_33447, C_33448), A_33446) | r2_hidden('#skF_2'(A_33446, B_33447, C_33448), C_33448) | k2_xboole_0(A_33446, B_33447)=C_33448)), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_72409, plain, (![A_45260, B_45261]: (r2_hidden('#skF_1'(A_45260, B_45261, B_45261), A_45260) | r2_hidden('#skF_2'(A_45260, B_45261, B_45261), B_45261) | k2_xboole_0(A_45260, B_45261)=B_45261)), inference(resolution, [status(thm)], [c_52099, c_16])).
% 14.47/5.90  tff(c_53621, plain, (![A_36160, B_36161, C_36162]: (r2_hidden('#skF_1'(A_36160, B_36161, C_36162), B_36161) | r2_hidden('#skF_1'(A_36160, B_36161, C_36162), A_36160) | ~r2_hidden('#skF_2'(A_36160, B_36161, C_36162), B_36161) | k2_xboole_0(A_36160, B_36161)=C_36162)), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_53695, plain, (![A_36160, B_36161]: (r2_hidden('#skF_1'(A_36160, B_36161, B_36161), A_36160) | ~r2_hidden('#skF_2'(A_36160, B_36161, B_36161), B_36161) | k2_xboole_0(A_36160, B_36161)=B_36161)), inference(resolution, [status(thm)], [c_53621, c_8])).
% 14.47/5.90  tff(c_72501, plain, (![A_45284, B_45285]: (r2_hidden('#skF_1'(A_45284, B_45285, B_45285), A_45284) | k2_xboole_0(A_45284, B_45285)=B_45285)), inference(resolution, [status(thm)], [c_72409, c_53695])).
% 14.47/5.90  tff(c_72743, plain, (![B_45375]: (r2_hidden('#skF_1'('#skF_7', B_45375, B_45375), '#skF_6') | k2_xboole_0('#skF_7', B_45375)=B_45375)), inference(resolution, [status(thm)], [c_72501, c_39080])).
% 14.47/5.90  tff(c_72770, plain, (![B_45398]: ('#skF_1'('#skF_7', B_45398, B_45398)='#skF_5' | k2_xboole_0('#skF_7', B_45398)=B_45398)), inference(resolution, [status(thm)], [c_72743, c_39049])).
% 14.47/5.90  tff(c_72828, plain, (k1_xboole_0='#skF_7' | '#skF_1'('#skF_7', k1_xboole_0, k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_72770, c_20])).
% 14.47/5.90  tff(c_72853, plain, ('#skF_1'('#skF_7', k1_xboole_0, k1_xboole_0)='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_39019, c_72828])).
% 14.47/5.90  tff(c_72497, plain, (![A_45260, B_45261]: (r2_hidden('#skF_1'(A_45260, B_45261, B_45261), A_45260) | k2_xboole_0(A_45260, B_45261)=B_45261)), inference(resolution, [status(thm)], [c_72409, c_53695])).
% 14.47/5.90  tff(c_72865, plain, (r2_hidden('#skF_5', '#skF_7') | k2_xboole_0('#skF_7', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_72853, c_72497])).
% 14.47/5.90  tff(c_72890, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_72865])).
% 14.47/5.90  tff(c_72892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39019, c_42927, c_72890])).
% 14.47/5.90  tff(c_72893, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_42920])).
% 14.47/5.90  tff(c_72933, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_72893, c_39080])).
% 14.47/5.90  tff(c_72936, plain, ('#skF_4'('#skF_5', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_72933, c_39049])).
% 14.47/5.90  tff(c_72940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39306, c_72936])).
% 14.47/5.90  tff(c_72942, plain, ('#skF_4'('#skF_5', '#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_39303])).
% 14.47/5.90  tff(c_72941, plain, ('#skF_3'('#skF_5', '#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_39303])).
% 14.47/5.90  tff(c_73192, plain, (![A_45854, B_45855]: (~r2_hidden('#skF_3'(A_45854, B_45855), B_45855) | '#skF_4'(A_45854, B_45855)!=A_45854 | k1_tarski(A_45854)=B_45855)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.47/5.90  tff(c_73220, plain, (~r2_hidden('#skF_5', '#skF_7') | '#skF_4'('#skF_5', '#skF_7')!='#skF_5' | k1_tarski('#skF_5')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_72941, c_73192])).
% 14.47/5.90  tff(c_73252, plain, (~r2_hidden('#skF_5', '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_39020, c_72942, c_73220])).
% 14.47/5.90  tff(c_73253, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_39045, c_73252])).
% 14.47/5.90  tff(c_88960, plain, (![A_58155, B_58156, C_58157]: (r2_hidden('#skF_1'(A_58155, B_58156, C_58157), B_58156) | r2_hidden('#skF_1'(A_58155, B_58156, C_58157), A_58155) | r2_hidden('#skF_2'(A_58155, B_58156, C_58157), C_58157) | k2_xboole_0(A_58155, B_58156)=C_58157)), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_89042, plain, (![A_58155, B_58156]: (r2_hidden('#skF_1'(A_58155, B_58156, B_58156), A_58155) | r2_hidden('#skF_2'(A_58155, B_58156, B_58156), B_58156) | k2_xboole_0(A_58155, B_58156)=B_58156)), inference(resolution, [status(thm)], [c_88960, c_16])).
% 14.47/5.90  tff(c_89340, plain, (![A_58386, B_58387, C_58388]: (r2_hidden('#skF_1'(A_58386, B_58387, C_58388), B_58387) | r2_hidden('#skF_1'(A_58386, B_58387, C_58388), A_58386) | ~r2_hidden('#skF_2'(A_58386, B_58387, C_58388), B_58387) | k2_xboole_0(A_58386, B_58387)=C_58388)), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.47/5.90  tff(c_98562, plain, (![A_61792, B_61793]: (r2_hidden('#skF_1'(A_61792, B_61793, B_61793), A_61792) | ~r2_hidden('#skF_2'(A_61792, B_61793, B_61793), B_61793) | k2_xboole_0(A_61792, B_61793)=B_61793)), inference(resolution, [status(thm)], [c_89340, c_8])).
% 14.47/5.90  tff(c_98605, plain, (![A_61816, B_61817]: (r2_hidden('#skF_1'(A_61816, B_61817, B_61817), A_61816) | k2_xboole_0(A_61816, B_61817)=B_61817)), inference(resolution, [status(thm)], [c_89042, c_98562])).
% 14.47/5.90  tff(c_98843, plain, (![B_61907]: (r2_hidden('#skF_1'('#skF_7', B_61907, B_61907), '#skF_6') | k2_xboole_0('#skF_7', B_61907)=B_61907)), inference(resolution, [status(thm)], [c_98605, c_39080])).
% 14.47/5.90  tff(c_98870, plain, (![B_61930]: ('#skF_1'('#skF_7', B_61930, B_61930)='#skF_5' | k2_xboole_0('#skF_7', B_61930)=B_61930)), inference(resolution, [status(thm)], [c_98843, c_39049])).
% 14.47/5.90  tff(c_98928, plain, (k1_xboole_0='#skF_7' | '#skF_1'('#skF_7', k1_xboole_0, k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_98870, c_20])).
% 14.47/5.90  tff(c_98953, plain, ('#skF_1'('#skF_7', k1_xboole_0, k1_xboole_0)='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_39019, c_98928])).
% 14.47/5.90  tff(c_98595, plain, (![A_58155, B_58156]: (r2_hidden('#skF_1'(A_58155, B_58156, B_58156), A_58155) | k2_xboole_0(A_58155, B_58156)=B_58156)), inference(resolution, [status(thm)], [c_89042, c_98562])).
% 14.47/5.90  tff(c_98965, plain, (r2_hidden('#skF_5', '#skF_7') | k2_xboole_0('#skF_7', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_98953, c_98595])).
% 14.47/5.90  tff(c_98990, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_98965])).
% 14.47/5.90  tff(c_98992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39019, c_73253, c_98990])).
% 14.47/5.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.47/5.90  
% 14.47/5.90  Inference rules
% 14.47/5.90  ----------------------
% 14.47/5.90  #Ref     : 0
% 14.47/5.90  #Sup     : 12787
% 14.47/5.90  #Fact    : 68
% 14.47/5.90  #Define  : 0
% 14.47/5.90  #Split   : 34
% 14.47/5.90  #Chain   : 0
% 14.47/5.90  #Close   : 0
% 14.47/5.90  
% 14.47/5.90  Ordering : KBO
% 14.47/5.90  
% 14.47/5.90  Simplification rules
% 14.47/5.90  ----------------------
% 14.47/5.90  #Subsume      : 5795
% 14.47/5.90  #Demod        : 3291
% 14.47/5.90  #Tautology    : 1515
% 14.47/5.90  #SimpNegUnit  : 506
% 14.47/5.90  #BackRed      : 12
% 14.47/5.90  
% 14.47/5.90  #Partial instantiations: 35809
% 14.47/5.90  #Strategies tried      : 1
% 14.47/5.90  
% 14.47/5.90  Timing (in seconds)
% 14.47/5.90  ----------------------
% 14.47/5.90  Preprocessing        : 0.31
% 14.47/5.90  Parsing              : 0.16
% 14.47/5.90  CNF conversion       : 0.02
% 14.47/5.90  Main loop            : 4.78
% 14.47/5.90  Inferencing          : 1.92
% 14.47/5.90  Reduction            : 1.22
% 14.47/5.90  Demodulation         : 0.81
% 14.47/5.90  BG Simplification    : 0.19
% 14.47/5.90  Subsumption          : 1.13
% 14.47/5.90  Abstraction          : 0.33
% 14.47/5.90  MUC search           : 0.00
% 14.47/5.91  Cooper               : 0.00
% 14.47/5.91  Total                : 5.15
% 14.47/5.91  Index Insertion      : 0.00
% 14.47/5.91  Index Deletion       : 0.00
% 14.47/5.91  Index Matching       : 0.00
% 14.47/5.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
