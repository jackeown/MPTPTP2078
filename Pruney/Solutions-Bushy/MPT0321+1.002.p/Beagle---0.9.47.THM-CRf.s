%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0321+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:06 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 370 expanded)
%              Number of leaves         :   23 ( 124 expanded)
%              Depth                    :   16
%              Number of atoms          :  169 ( 855 expanded)
%              Number of equality atoms :   46 ( 368 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_25,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(c_24,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r2_hidden('#skF_2'(A_5,B_6),A_5)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_103,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( r2_hidden(k4_tarski(A_38,B_39),k2_zfmisc_1(C_40,D_41))
      | ~ r2_hidden(B_39,D_41)
      | ~ r2_hidden(A_38,C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_57,plain,(
    ! [A_20,C_21,B_22,D_23] :
      ( r2_hidden(A_20,C_21)
      | ~ r2_hidden(k4_tarski(A_20,B_22),k2_zfmisc_1(C_21,D_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_20,B_22] :
      ( r2_hidden(A_20,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_20,B_22),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_57])).

tff(c_124,plain,(
    ! [A_38,B_39] :
      ( r2_hidden(A_38,'#skF_6')
      | ~ r2_hidden(B_39,'#skF_5')
      | ~ r2_hidden(A_38,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_103,c_60])).

tff(c_195,plain,(
    ! [B_52] : ~ r2_hidden(B_52,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_217,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_195])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_217])).

tff(c_227,plain,(
    ! [A_53] :
      ( r2_hidden(A_53,'#skF_6')
      | ~ r2_hidden(A_53,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_536,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_1'(A_68,'#skF_6'),'#skF_6')
      | A_68 = '#skF_6'
      | ~ r2_hidden('#skF_2'(A_68,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_227,c_14])).

tff(c_548,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_6'),'#skF_6')
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_536])).

tff(c_558,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_548])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_47,plain,(
    ! [B_15,D_16,A_17,C_18] :
      ( r2_hidden(B_15,D_16)
      | ~ r2_hidden(k4_tarski(A_17,B_15),k2_zfmisc_1(C_18,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [B_15,A_17] :
      ( r2_hidden(B_15,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_17,B_15),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_47])).

tff(c_125,plain,(
    ! [B_39,A_38] :
      ( r2_hidden(B_39,'#skF_7')
      | ~ r2_hidden(B_39,'#skF_5')
      | ~ r2_hidden(A_38,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_103,c_50])).

tff(c_143,plain,(
    ! [A_46] : ~ r2_hidden(A_46,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_165,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_143])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_165])).

tff(c_175,plain,(
    ! [B_47] :
      ( r2_hidden(B_47,'#skF_7')
      | ~ r2_hidden(B_47,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_20,plain,(
    ! [B_9,A_8] :
      ( ~ v1_xboole_0(B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_188,plain,(
    ! [B_47] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(B_47,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_175,c_20])).

tff(c_192,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_243,plain,(
    ! [A_54,B_55] :
      ( r2_hidden(k4_tarski(A_54,B_55),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_55,'#skF_7')
      | ~ r2_hidden(A_54,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_103])).

tff(c_10,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_261,plain,(
    ! [A_54,B_55] :
      ( r2_hidden(A_54,'#skF_4')
      | ~ r2_hidden(B_55,'#skF_7')
      | ~ r2_hidden(A_54,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_243,c_10])).

tff(c_267,plain,(
    ! [B_56] : ~ r2_hidden(B_56,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_294,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_22,c_267])).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_25])).

tff(c_4,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_305,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_31])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_305])).

tff(c_309,plain,(
    ! [A_54] :
      ( r2_hidden(A_54,'#skF_4')
      | ~ r2_hidden(A_54,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_586,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_558,c_309])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r2_hidden('#skF_2'(A_5,B_6),A_5)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_226,plain,(
    ! [A_38] :
      ( r2_hidden(A_38,'#skF_6')
      | ~ r2_hidden(A_38,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),A_5)
      | ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_604,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_586,c_12])).

tff(c_610,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_604])).

tff(c_615,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_226,c_610])).

tff(c_624,plain,
    ( ~ r2_hidden('#skF_1'('#skF_4','#skF_6'),'#skF_4')
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16,c_615])).

tff(c_632,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_624])).

tff(c_634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_632])).

tff(c_636,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_42,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_3'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_46,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(resolution,[status(thm)],[c_42,c_20])).

tff(c_643,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_636,c_46])).

tff(c_647,plain,(
    '#skF_7' != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_26])).

tff(c_76,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_1'(A_34,B_35),B_35)
      | r2_hidden('#skF_2'(A_34,B_35),A_34)
      | B_35 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [A_34,B_35] :
      ( ~ v1_xboole_0(A_34)
      | r2_hidden('#skF_1'(A_34,B_35),B_35)
      | B_35 = A_34 ) ),
    inference(resolution,[status(thm)],[c_76,c_20])).

tff(c_681,plain,(
    ! [B_71] : ~ r2_hidden(B_71,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_710,plain,(
    ! [A_73] :
      ( ~ v1_xboole_0(A_73)
      | A_73 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_91,c_681])).

tff(c_713,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_636,c_710])).

tff(c_717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_647,c_713])).

tff(c_718,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_790,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( r2_hidden(k4_tarski(A_98,B_99),k2_zfmisc_1(C_100,D_101))
      | ~ r2_hidden(B_99,D_101)
      | ~ r2_hidden(A_98,C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_719,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_730,plain,(
    k2_zfmisc_1('#skF_4','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_30])).

tff(c_745,plain,(
    ! [B_82,D_83,A_84,C_85] :
      ( r2_hidden(B_82,D_83)
      | ~ r2_hidden(k4_tarski(A_84,B_82),k2_zfmisc_1(C_85,D_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_748,plain,(
    ! [B_82,A_84] :
      ( r2_hidden(B_82,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_84,B_82),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_745])).

tff(c_807,plain,(
    ! [B_99,A_98] :
      ( r2_hidden(B_99,'#skF_7')
      | ~ r2_hidden(B_99,'#skF_5')
      | ~ r2_hidden(A_98,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_790,c_748])).

tff(c_825,plain,(
    ! [A_106] : ~ r2_hidden(A_106,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_807])).

tff(c_847,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_825])).

tff(c_855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_847])).

tff(c_857,plain,(
    ! [B_107] :
      ( r2_hidden(B_107,'#skF_7')
      | ~ r2_hidden(B_107,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_807])).

tff(c_1041,plain,(
    ! [A_120] :
      ( r2_hidden('#skF_1'(A_120,'#skF_7'),'#skF_7')
      | A_120 = '#skF_7'
      | ~ r2_hidden('#skF_2'(A_120,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_857,c_14])).

tff(c_1057,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_18,c_1041])).

tff(c_1069,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_718,c_718,c_1057])).

tff(c_876,plain,(
    ! [A_112,B_113] :
      ( r2_hidden(k4_tarski(A_112,B_113),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_113,'#skF_7')
      | ~ r2_hidden(A_112,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_790])).

tff(c_8,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_890,plain,(
    ! [B_113,A_112] :
      ( r2_hidden(B_113,'#skF_5')
      | ~ r2_hidden(B_113,'#skF_7')
      | ~ r2_hidden(A_112,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_876,c_8])).

tff(c_894,plain,(
    ! [A_114] : ~ r2_hidden(A_114,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_890])).

tff(c_916,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_894])).

tff(c_924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_916])).

tff(c_925,plain,(
    ! [B_113] :
      ( r2_hidden(B_113,'#skF_5')
      | ~ r2_hidden(B_113,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_890])).

tff(c_1078,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1069,c_925])).

tff(c_856,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,'#skF_7')
      | ~ r2_hidden(B_99,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_807])).

tff(c_1081,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1078,c_12])).

tff(c_1087,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_718,c_1081])).

tff(c_1092,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_856,c_1087])).

tff(c_1112,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_5')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16,c_1092])).

tff(c_1120,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1078,c_1112])).

tff(c_1122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_718,c_1120])).

%------------------------------------------------------------------------------
