%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:19 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 466 expanded)
%              Number of leaves         :   28 ( 163 expanded)
%              Depth                    :   14
%              Number of atoms          :  203 (1042 expanded)
%              Number of equality atoms :   49 ( 315 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_68,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_58,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_66,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_174,plain,(
    ! [A_51,B_52] :
      ( ~ r2_hidden('#skF_1'(A_51,B_52),B_52)
      | r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_179,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_174])).

tff(c_542,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( r2_hidden(k4_tarski(A_123,B_124),k2_zfmisc_1(C_125,D_126))
      | ~ r2_hidden(B_124,D_126)
      | ~ r2_hidden(A_123,C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_64,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_234,plain,(
    ! [B_75,D_76,A_77,C_78] :
      ( r2_hidden(B_75,D_76)
      | ~ r2_hidden(k4_tarski(A_77,B_75),k2_zfmisc_1(C_78,D_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_237,plain,(
    ! [B_75,A_77] :
      ( r2_hidden(B_75,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_77,B_75),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_234])).

tff(c_568,plain,(
    ! [B_124,A_123] :
      ( r2_hidden(B_124,'#skF_8')
      | ~ r2_hidden(B_124,'#skF_10')
      | ~ r2_hidden(A_123,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_542,c_237])).

tff(c_574,plain,(
    ! [A_127] : ~ r2_hidden(A_127,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_568])).

tff(c_640,plain,(
    ! [B_131] : r1_tarski('#skF_9',B_131) ),
    inference(resolution,[status(thm)],[c_6,c_574])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( r2_xboole_0(A_12,B_13)
      | B_13 = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_6'(A_17,B_18),B_18)
      | ~ r2_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_133,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_6'(A_42,B_43),B_43)
      | ~ r2_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_119,plain,(
    ! [D_37,B_38,A_39] :
      ( ~ r2_hidden(D_37,B_38)
      | ~ r2_hidden(D_37,k4_xboole_0(A_39,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_126,plain,(
    ! [D_37,A_20] :
      ( ~ r2_hidden(D_37,k1_xboole_0)
      | ~ r2_hidden(D_37,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_119])).

tff(c_181,plain,(
    ! [A_54,A_55] :
      ( ~ r2_hidden('#skF_6'(A_54,k1_xboole_0),A_55)
      | ~ r2_xboole_0(A_54,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_133,c_126])).

tff(c_187,plain,(
    ! [A_56] : ~ r2_xboole_0(A_56,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_181])).

tff(c_192,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_187])).

tff(c_657,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_640,c_192])).

tff(c_56,plain,(
    ! [B_26] : k2_zfmisc_1(k1_xboole_0,B_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_670,plain,(
    ! [B_26] : k2_zfmisc_1('#skF_9',B_26) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_657,c_56])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_104,plain,(
    ! [B_35,A_36] :
      ( k1_xboole_0 = B_35
      | k1_xboole_0 = A_36
      | k2_zfmisc_1(A_36,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_107,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_104])).

tff(c_114,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_60,c_107])).

tff(c_668,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_114])).

tff(c_748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_668])).

tff(c_750,plain,(
    ! [B_136] :
      ( r2_hidden(B_136,'#skF_8')
      | ~ r2_hidden(B_136,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_568])).

tff(c_822,plain,(
    ! [B_140] :
      ( r2_hidden('#skF_1'('#skF_10',B_140),'#skF_8')
      | r1_tarski('#skF_10',B_140) ) ),
    inference(resolution,[status(thm)],[c_6,c_750])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_830,plain,(
    r1_tarski('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_822,c_4])).

tff(c_797,plain,(
    ! [A_138,B_139] :
      ( r2_hidden(k4_tarski(A_138,B_139),k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(B_139,'#skF_8')
      | ~ r2_hidden(A_138,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_542])).

tff(c_48,plain,(
    ! [B_22,D_24,A_21,C_23] :
      ( r2_hidden(B_22,D_24)
      | ~ r2_hidden(k4_tarski(A_21,B_22),k2_zfmisc_1(C_23,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_813,plain,(
    ! [B_139,A_138] :
      ( r2_hidden(B_139,'#skF_10')
      | ~ r2_hidden(B_139,'#skF_8')
      | ~ r2_hidden(A_138,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_797,c_48])).

tff(c_1241,plain,(
    ! [A_161] : ~ r2_hidden(A_161,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_813])).

tff(c_1337,plain,(
    ! [B_164] : r1_tarski('#skF_7',B_164) ),
    inference(resolution,[status(thm)],[c_6,c_1241])).

tff(c_1349,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1337,c_192])).

tff(c_1357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1349])).

tff(c_1389,plain,(
    ! [B_169] :
      ( r2_hidden(B_169,'#skF_10')
      | ~ r2_hidden(B_169,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_813])).

tff(c_40,plain,(
    ! [A_17,B_18] :
      ( ~ r2_hidden('#skF_6'(A_17,B_18),A_17)
      | ~ r2_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1693,plain,(
    ! [B_182] :
      ( ~ r2_xboole_0('#skF_10',B_182)
      | ~ r2_hidden('#skF_6'('#skF_10',B_182),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1389,c_40])).

tff(c_1708,plain,(
    ~ r2_xboole_0('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_1693])).

tff(c_1711,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r1_tarski('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_1708])).

tff(c_1714,plain,(
    '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_1711])).

tff(c_788,plain,(
    ! [A_137] :
      ( r2_hidden('#skF_6'(A_137,'#skF_10'),'#skF_8')
      | ~ r2_xboole_0(A_137,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_42,c_750])).

tff(c_796,plain,(
    ~ r2_xboole_0('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_788,c_40])).

tff(c_820,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_26,c_796])).

tff(c_821,plain,(
    ~ r1_tarski('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_820])).

tff(c_1721,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_821])).

tff(c_1733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_1721])).

tff(c_1734,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_820])).

tff(c_221,plain,(
    ! [A_64,C_65,B_66,D_67] :
      ( r2_hidden(A_64,C_65)
      | ~ r2_hidden(k4_tarski(A_64,B_66),k2_zfmisc_1(C_65,D_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_224,plain,(
    ! [A_64,B_66] :
      ( r2_hidden(A_64,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_64,B_66),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_221])).

tff(c_570,plain,(
    ! [A_123,B_124] :
      ( r2_hidden(A_123,'#skF_7')
      | ~ r2_hidden(B_124,'#skF_10')
      | ~ r2_hidden(A_123,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_542,c_224])).

tff(c_1808,plain,(
    ! [A_123,B_124] :
      ( r2_hidden(A_123,'#skF_7')
      | ~ r2_hidden(B_124,'#skF_8')
      | ~ r2_hidden(A_123,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1734,c_570])).

tff(c_1810,plain,(
    ! [B_186] : ~ r2_hidden(B_186,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1808])).

tff(c_1872,plain,(
    ! [B_191] : r1_tarski('#skF_8',B_191) ),
    inference(resolution,[status(thm)],[c_6,c_1810])).

tff(c_1884,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1872,c_192])).

tff(c_1892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1884])).

tff(c_1894,plain,(
    ! [A_192] :
      ( r2_hidden(A_192,'#skF_7')
      | ~ r2_hidden(A_192,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_1808])).

tff(c_1917,plain,(
    ! [A_193] :
      ( r1_tarski(A_193,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_193,'#skF_7'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1894,c_4])).

tff(c_1932,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_1917])).

tff(c_50,plain,(
    ! [A_21,C_23,B_22,D_24] :
      ( r2_hidden(A_21,C_23)
      | ~ r2_hidden(k4_tarski(A_21,B_22),k2_zfmisc_1(C_23,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_815,plain,(
    ! [A_138,B_139] :
      ( r2_hidden(A_138,'#skF_9')
      | ~ r2_hidden(B_139,'#skF_8')
      | ~ r2_hidden(A_138,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_797,c_50])).

tff(c_1934,plain,(
    ! [B_194] : ~ r2_hidden(B_194,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_815])).

tff(c_1985,plain,(
    ! [B_196] : r1_tarski('#skF_8',B_196) ),
    inference(resolution,[status(thm)],[c_6,c_1934])).

tff(c_1997,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1985,c_192])).

tff(c_2005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1997])).

tff(c_2037,plain,(
    ! [A_201] :
      ( r2_hidden(A_201,'#skF_9')
      | ~ r2_hidden(A_201,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_815])).

tff(c_2096,plain,(
    ! [A_205] :
      ( r2_hidden('#skF_6'(A_205,'#skF_7'),'#skF_9')
      | ~ r2_xboole_0(A_205,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_2037])).

tff(c_2104,plain,(
    ~ r2_xboole_0('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_2096,c_40])).

tff(c_2107,plain,
    ( '#skF_7' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_2104])).

tff(c_2110,plain,(
    '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1932,c_2107])).

tff(c_2112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2110])).

tff(c_2113,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2114,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2115,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2114,c_62])).

tff(c_2598,plain,(
    ! [A_301,B_302,C_303,D_304] :
      ( r2_hidden(k4_tarski(A_301,B_302),k2_zfmisc_1(C_303,D_304))
      | ~ r2_hidden(B_302,D_304)
      | ~ r2_hidden(A_301,C_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2152,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k2_zfmisc_1('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2114,c_64])).

tff(c_2276,plain,(
    ! [B_242,D_243,A_244,C_245] :
      ( r2_hidden(B_242,D_243)
      | ~ r2_hidden(k4_tarski(A_244,B_242),k2_zfmisc_1(C_245,D_243)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2279,plain,(
    ! [B_242,A_244] :
      ( r2_hidden(B_242,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_244,B_242),k2_zfmisc_1('#skF_9','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2152,c_2276])).

tff(c_2621,plain,(
    ! [B_302,A_301] :
      ( r2_hidden(B_302,'#skF_10')
      | ~ r2_hidden(B_302,'#skF_8')
      | ~ r2_hidden(A_301,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2598,c_2279])).

tff(c_2625,plain,(
    ! [A_305] : ~ r2_hidden(A_305,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2621])).

tff(c_2669,plain,(
    ! [B_307] : r1_tarski('#skF_9',B_307) ),
    inference(resolution,[status(thm)],[c_6,c_2625])).

tff(c_2175,plain,(
    ! [D_217,B_218,A_219] :
      ( ~ r2_hidden(D_217,B_218)
      | ~ r2_hidden(D_217,k4_xboole_0(A_219,B_218)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2189,plain,(
    ! [D_220,A_221] :
      ( ~ r2_hidden(D_220,k1_xboole_0)
      | ~ r2_hidden(D_220,A_221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2175])).

tff(c_2236,plain,(
    ! [A_232,A_233] :
      ( ~ r2_hidden('#skF_6'(A_232,k1_xboole_0),A_233)
      | ~ r2_xboole_0(A_232,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42,c_2189])).

tff(c_2242,plain,(
    ! [A_234] : ~ r2_xboole_0(A_234,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_2236])).

tff(c_2247,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_2242])).

tff(c_2685,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2669,c_2247])).

tff(c_2694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2115,c_2685])).

tff(c_2696,plain,(
    ! [B_308] :
      ( r2_hidden(B_308,'#skF_10')
      | ~ r2_hidden(B_308,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_2621])).

tff(c_2789,plain,(
    ! [A_315] :
      ( r1_tarski(A_315,'#skF_10')
      | ~ r2_hidden('#skF_1'(A_315,'#skF_10'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2696,c_4])).

tff(c_2799,plain,(
    r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_6,c_2789])).

tff(c_2800,plain,(
    ! [A_316,B_317] :
      ( r2_hidden(k4_tarski(A_316,B_317),k2_zfmisc_1('#skF_9','#skF_8'))
      | ~ r2_hidden(B_317,'#skF_10')
      | ~ r2_hidden(A_316,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2152,c_2598])).

tff(c_2814,plain,(
    ! [B_317,A_316] :
      ( r2_hidden(B_317,'#skF_8')
      | ~ r2_hidden(B_317,'#skF_10')
      | ~ r2_hidden(A_316,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2800,c_48])).

tff(c_2851,plain,(
    ! [A_323] : ~ r2_hidden(A_323,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2814])).

tff(c_2902,plain,(
    ! [B_325] : r1_tarski('#skF_9',B_325) ),
    inference(resolution,[status(thm)],[c_6,c_2851])).

tff(c_2921,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2902,c_2247])).

tff(c_2931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2115,c_2921])).

tff(c_2976,plain,(
    ! [B_329] :
      ( r2_hidden(B_329,'#skF_8')
      | ~ r2_hidden(B_329,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_2814])).

tff(c_3030,plain,(
    ! [A_330] :
      ( r2_hidden('#skF_6'(A_330,'#skF_10'),'#skF_8')
      | ~ r2_xboole_0(A_330,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_42,c_2976])).

tff(c_3043,plain,(
    ~ r2_xboole_0('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_3030,c_40])).

tff(c_3046,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_26,c_3043])).

tff(c_3049,plain,(
    '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2799,c_3046])).

tff(c_3051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2113,c_3049])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.78  
% 4.23/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.79  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 4.23/1.79  
% 4.23/1.79  %Foreground sorts:
% 4.23/1.79  
% 4.23/1.79  
% 4.23/1.79  %Background operators:
% 4.23/1.79  
% 4.23/1.79  
% 4.23/1.79  %Foreground operators:
% 4.23/1.79  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.23/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.23/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.23/1.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.23/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.23/1.79  tff('#skF_7', type, '#skF_7': $i).
% 4.23/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.23/1.79  tff('#skF_10', type, '#skF_10': $i).
% 4.23/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.23/1.79  tff('#skF_9', type, '#skF_9': $i).
% 4.23/1.79  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.23/1.79  tff('#skF_8', type, '#skF_8': $i).
% 4.23/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.23/1.79  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.23/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.23/1.79  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.23/1.79  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.23/1.79  
% 4.27/1.81  tff(f_91, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 4.27/1.81  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.27/1.81  tff(f_74, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.27/1.81  tff(f_49, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 4.27/1.81  tff(f_66, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 4.27/1.81  tff(f_68, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.27/1.81  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.27/1.81  tff(f_80, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.27/1.81  tff(c_58, plain, ('#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.27/1.81  tff(c_66, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_58])).
% 4.27/1.81  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.27/1.81  tff(c_60, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.27/1.81  tff(c_174, plain, (![A_51, B_52]: (~r2_hidden('#skF_1'(A_51, B_52), B_52) | r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.27/1.81  tff(c_179, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_174])).
% 4.27/1.81  tff(c_542, plain, (![A_123, B_124, C_125, D_126]: (r2_hidden(k4_tarski(A_123, B_124), k2_zfmisc_1(C_125, D_126)) | ~r2_hidden(B_124, D_126) | ~r2_hidden(A_123, C_125))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.27/1.81  tff(c_64, plain, (k2_zfmisc_1('#skF_7', '#skF_8')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.27/1.81  tff(c_234, plain, (![B_75, D_76, A_77, C_78]: (r2_hidden(B_75, D_76) | ~r2_hidden(k4_tarski(A_77, B_75), k2_zfmisc_1(C_78, D_76)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.27/1.81  tff(c_237, plain, (![B_75, A_77]: (r2_hidden(B_75, '#skF_8') | ~r2_hidden(k4_tarski(A_77, B_75), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_234])).
% 4.27/1.81  tff(c_568, plain, (![B_124, A_123]: (r2_hidden(B_124, '#skF_8') | ~r2_hidden(B_124, '#skF_10') | ~r2_hidden(A_123, '#skF_9'))), inference(resolution, [status(thm)], [c_542, c_237])).
% 4.27/1.81  tff(c_574, plain, (![A_127]: (~r2_hidden(A_127, '#skF_9'))), inference(splitLeft, [status(thm)], [c_568])).
% 4.27/1.81  tff(c_640, plain, (![B_131]: (r1_tarski('#skF_9', B_131))), inference(resolution, [status(thm)], [c_6, c_574])).
% 4.27/1.81  tff(c_26, plain, (![A_12, B_13]: (r2_xboole_0(A_12, B_13) | B_13=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.27/1.81  tff(c_42, plain, (![A_17, B_18]: (r2_hidden('#skF_6'(A_17, B_18), B_18) | ~r2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.27/1.81  tff(c_133, plain, (![A_42, B_43]: (r2_hidden('#skF_6'(A_42, B_43), B_43) | ~r2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.27/1.81  tff(c_44, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.27/1.81  tff(c_119, plain, (![D_37, B_38, A_39]: (~r2_hidden(D_37, B_38) | ~r2_hidden(D_37, k4_xboole_0(A_39, B_38)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.27/1.81  tff(c_126, plain, (![D_37, A_20]: (~r2_hidden(D_37, k1_xboole_0) | ~r2_hidden(D_37, A_20))), inference(superposition, [status(thm), theory('equality')], [c_44, c_119])).
% 4.27/1.81  tff(c_181, plain, (![A_54, A_55]: (~r2_hidden('#skF_6'(A_54, k1_xboole_0), A_55) | ~r2_xboole_0(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_133, c_126])).
% 4.27/1.81  tff(c_187, plain, (![A_56]: (~r2_xboole_0(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_181])).
% 4.27/1.81  tff(c_192, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_187])).
% 4.27/1.81  tff(c_657, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_640, c_192])).
% 4.27/1.81  tff(c_56, plain, (![B_26]: (k2_zfmisc_1(k1_xboole_0, B_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.27/1.81  tff(c_670, plain, (![B_26]: (k2_zfmisc_1('#skF_9', B_26)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_657, c_657, c_56])).
% 4.27/1.81  tff(c_62, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.27/1.81  tff(c_104, plain, (![B_35, A_36]: (k1_xboole_0=B_35 | k1_xboole_0=A_36 | k2_zfmisc_1(A_36, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.27/1.81  tff(c_107, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_64, c_104])).
% 4.27/1.81  tff(c_114, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_60, c_107])).
% 4.27/1.81  tff(c_668, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_657, c_114])).
% 4.27/1.81  tff(c_748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_670, c_668])).
% 4.27/1.81  tff(c_750, plain, (![B_136]: (r2_hidden(B_136, '#skF_8') | ~r2_hidden(B_136, '#skF_10'))), inference(splitRight, [status(thm)], [c_568])).
% 4.27/1.81  tff(c_822, plain, (![B_140]: (r2_hidden('#skF_1'('#skF_10', B_140), '#skF_8') | r1_tarski('#skF_10', B_140))), inference(resolution, [status(thm)], [c_6, c_750])).
% 4.27/1.81  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.27/1.81  tff(c_830, plain, (r1_tarski('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_822, c_4])).
% 4.27/1.81  tff(c_797, plain, (![A_138, B_139]: (r2_hidden(k4_tarski(A_138, B_139), k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden(B_139, '#skF_8') | ~r2_hidden(A_138, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_542])).
% 4.27/1.81  tff(c_48, plain, (![B_22, D_24, A_21, C_23]: (r2_hidden(B_22, D_24) | ~r2_hidden(k4_tarski(A_21, B_22), k2_zfmisc_1(C_23, D_24)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.27/1.81  tff(c_813, plain, (![B_139, A_138]: (r2_hidden(B_139, '#skF_10') | ~r2_hidden(B_139, '#skF_8') | ~r2_hidden(A_138, '#skF_7'))), inference(resolution, [status(thm)], [c_797, c_48])).
% 4.27/1.81  tff(c_1241, plain, (![A_161]: (~r2_hidden(A_161, '#skF_7'))), inference(splitLeft, [status(thm)], [c_813])).
% 4.27/1.81  tff(c_1337, plain, (![B_164]: (r1_tarski('#skF_7', B_164))), inference(resolution, [status(thm)], [c_6, c_1241])).
% 4.27/1.81  tff(c_1349, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1337, c_192])).
% 4.27/1.81  tff(c_1357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1349])).
% 4.27/1.81  tff(c_1389, plain, (![B_169]: (r2_hidden(B_169, '#skF_10') | ~r2_hidden(B_169, '#skF_8'))), inference(splitRight, [status(thm)], [c_813])).
% 4.27/1.81  tff(c_40, plain, (![A_17, B_18]: (~r2_hidden('#skF_6'(A_17, B_18), A_17) | ~r2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.27/1.81  tff(c_1693, plain, (![B_182]: (~r2_xboole_0('#skF_10', B_182) | ~r2_hidden('#skF_6'('#skF_10', B_182), '#skF_8'))), inference(resolution, [status(thm)], [c_1389, c_40])).
% 4.27/1.81  tff(c_1708, plain, (~r2_xboole_0('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_42, c_1693])).
% 4.27/1.81  tff(c_1711, plain, ('#skF_10'='#skF_8' | ~r1_tarski('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_26, c_1708])).
% 4.27/1.81  tff(c_1714, plain, ('#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_830, c_1711])).
% 4.27/1.81  tff(c_788, plain, (![A_137]: (r2_hidden('#skF_6'(A_137, '#skF_10'), '#skF_8') | ~r2_xboole_0(A_137, '#skF_10'))), inference(resolution, [status(thm)], [c_42, c_750])).
% 4.27/1.81  tff(c_796, plain, (~r2_xboole_0('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_788, c_40])).
% 4.27/1.81  tff(c_820, plain, ('#skF_10'='#skF_8' | ~r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_26, c_796])).
% 4.27/1.81  tff(c_821, plain, (~r1_tarski('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_820])).
% 4.27/1.81  tff(c_1721, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_821])).
% 4.27/1.81  tff(c_1733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_1721])).
% 4.27/1.81  tff(c_1734, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_820])).
% 4.27/1.81  tff(c_221, plain, (![A_64, C_65, B_66, D_67]: (r2_hidden(A_64, C_65) | ~r2_hidden(k4_tarski(A_64, B_66), k2_zfmisc_1(C_65, D_67)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.27/1.81  tff(c_224, plain, (![A_64, B_66]: (r2_hidden(A_64, '#skF_7') | ~r2_hidden(k4_tarski(A_64, B_66), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_221])).
% 4.27/1.81  tff(c_570, plain, (![A_123, B_124]: (r2_hidden(A_123, '#skF_7') | ~r2_hidden(B_124, '#skF_10') | ~r2_hidden(A_123, '#skF_9'))), inference(resolution, [status(thm)], [c_542, c_224])).
% 4.27/1.81  tff(c_1808, plain, (![A_123, B_124]: (r2_hidden(A_123, '#skF_7') | ~r2_hidden(B_124, '#skF_8') | ~r2_hidden(A_123, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1734, c_570])).
% 4.27/1.81  tff(c_1810, plain, (![B_186]: (~r2_hidden(B_186, '#skF_8'))), inference(splitLeft, [status(thm)], [c_1808])).
% 4.27/1.81  tff(c_1872, plain, (![B_191]: (r1_tarski('#skF_8', B_191))), inference(resolution, [status(thm)], [c_6, c_1810])).
% 4.27/1.81  tff(c_1884, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1872, c_192])).
% 4.27/1.81  tff(c_1892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1884])).
% 4.27/1.81  tff(c_1894, plain, (![A_192]: (r2_hidden(A_192, '#skF_7') | ~r2_hidden(A_192, '#skF_9'))), inference(splitRight, [status(thm)], [c_1808])).
% 4.27/1.81  tff(c_1917, plain, (![A_193]: (r1_tarski(A_193, '#skF_7') | ~r2_hidden('#skF_1'(A_193, '#skF_7'), '#skF_9'))), inference(resolution, [status(thm)], [c_1894, c_4])).
% 4.27/1.81  tff(c_1932, plain, (r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_1917])).
% 4.27/1.81  tff(c_50, plain, (![A_21, C_23, B_22, D_24]: (r2_hidden(A_21, C_23) | ~r2_hidden(k4_tarski(A_21, B_22), k2_zfmisc_1(C_23, D_24)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.27/1.81  tff(c_815, plain, (![A_138, B_139]: (r2_hidden(A_138, '#skF_9') | ~r2_hidden(B_139, '#skF_8') | ~r2_hidden(A_138, '#skF_7'))), inference(resolution, [status(thm)], [c_797, c_50])).
% 4.27/1.81  tff(c_1934, plain, (![B_194]: (~r2_hidden(B_194, '#skF_8'))), inference(splitLeft, [status(thm)], [c_815])).
% 4.27/1.81  tff(c_1985, plain, (![B_196]: (r1_tarski('#skF_8', B_196))), inference(resolution, [status(thm)], [c_6, c_1934])).
% 4.27/1.81  tff(c_1997, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1985, c_192])).
% 4.27/1.81  tff(c_2005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1997])).
% 4.27/1.81  tff(c_2037, plain, (![A_201]: (r2_hidden(A_201, '#skF_9') | ~r2_hidden(A_201, '#skF_7'))), inference(splitRight, [status(thm)], [c_815])).
% 4.27/1.81  tff(c_2096, plain, (![A_205]: (r2_hidden('#skF_6'(A_205, '#skF_7'), '#skF_9') | ~r2_xboole_0(A_205, '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_2037])).
% 4.27/1.81  tff(c_2104, plain, (~r2_xboole_0('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_2096, c_40])).
% 4.27/1.81  tff(c_2107, plain, ('#skF_7'='#skF_9' | ~r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_26, c_2104])).
% 4.27/1.81  tff(c_2110, plain, ('#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1932, c_2107])).
% 4.27/1.81  tff(c_2112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_2110])).
% 4.27/1.81  tff(c_2113, plain, ('#skF_10'!='#skF_8'), inference(splitRight, [status(thm)], [c_58])).
% 4.27/1.81  tff(c_2114, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_58])).
% 4.27/1.81  tff(c_2115, plain, (k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2114, c_62])).
% 4.27/1.81  tff(c_2598, plain, (![A_301, B_302, C_303, D_304]: (r2_hidden(k4_tarski(A_301, B_302), k2_zfmisc_1(C_303, D_304)) | ~r2_hidden(B_302, D_304) | ~r2_hidden(A_301, C_303))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.27/1.81  tff(c_2152, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k2_zfmisc_1('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2114, c_64])).
% 4.27/1.81  tff(c_2276, plain, (![B_242, D_243, A_244, C_245]: (r2_hidden(B_242, D_243) | ~r2_hidden(k4_tarski(A_244, B_242), k2_zfmisc_1(C_245, D_243)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.27/1.81  tff(c_2279, plain, (![B_242, A_244]: (r2_hidden(B_242, '#skF_10') | ~r2_hidden(k4_tarski(A_244, B_242), k2_zfmisc_1('#skF_9', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2152, c_2276])).
% 4.27/1.81  tff(c_2621, plain, (![B_302, A_301]: (r2_hidden(B_302, '#skF_10') | ~r2_hidden(B_302, '#skF_8') | ~r2_hidden(A_301, '#skF_9'))), inference(resolution, [status(thm)], [c_2598, c_2279])).
% 4.27/1.81  tff(c_2625, plain, (![A_305]: (~r2_hidden(A_305, '#skF_9'))), inference(splitLeft, [status(thm)], [c_2621])).
% 4.27/1.81  tff(c_2669, plain, (![B_307]: (r1_tarski('#skF_9', B_307))), inference(resolution, [status(thm)], [c_6, c_2625])).
% 4.27/1.81  tff(c_2175, plain, (![D_217, B_218, A_219]: (~r2_hidden(D_217, B_218) | ~r2_hidden(D_217, k4_xboole_0(A_219, B_218)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.27/1.81  tff(c_2189, plain, (![D_220, A_221]: (~r2_hidden(D_220, k1_xboole_0) | ~r2_hidden(D_220, A_221))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2175])).
% 4.27/1.81  tff(c_2236, plain, (![A_232, A_233]: (~r2_hidden('#skF_6'(A_232, k1_xboole_0), A_233) | ~r2_xboole_0(A_232, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_2189])).
% 4.27/1.81  tff(c_2242, plain, (![A_234]: (~r2_xboole_0(A_234, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_2236])).
% 4.27/1.81  tff(c_2247, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_2242])).
% 4.27/1.81  tff(c_2685, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_2669, c_2247])).
% 4.27/1.81  tff(c_2694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2115, c_2685])).
% 4.27/1.81  tff(c_2696, plain, (![B_308]: (r2_hidden(B_308, '#skF_10') | ~r2_hidden(B_308, '#skF_8'))), inference(splitRight, [status(thm)], [c_2621])).
% 4.27/1.81  tff(c_2789, plain, (![A_315]: (r1_tarski(A_315, '#skF_10') | ~r2_hidden('#skF_1'(A_315, '#skF_10'), '#skF_8'))), inference(resolution, [status(thm)], [c_2696, c_4])).
% 4.27/1.81  tff(c_2799, plain, (r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_6, c_2789])).
% 4.27/1.81  tff(c_2800, plain, (![A_316, B_317]: (r2_hidden(k4_tarski(A_316, B_317), k2_zfmisc_1('#skF_9', '#skF_8')) | ~r2_hidden(B_317, '#skF_10') | ~r2_hidden(A_316, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2152, c_2598])).
% 4.27/1.81  tff(c_2814, plain, (![B_317, A_316]: (r2_hidden(B_317, '#skF_8') | ~r2_hidden(B_317, '#skF_10') | ~r2_hidden(A_316, '#skF_9'))), inference(resolution, [status(thm)], [c_2800, c_48])).
% 4.27/1.81  tff(c_2851, plain, (![A_323]: (~r2_hidden(A_323, '#skF_9'))), inference(splitLeft, [status(thm)], [c_2814])).
% 4.27/1.81  tff(c_2902, plain, (![B_325]: (r1_tarski('#skF_9', B_325))), inference(resolution, [status(thm)], [c_6, c_2851])).
% 4.27/1.81  tff(c_2921, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_2902, c_2247])).
% 4.27/1.81  tff(c_2931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2115, c_2921])).
% 4.27/1.81  tff(c_2976, plain, (![B_329]: (r2_hidden(B_329, '#skF_8') | ~r2_hidden(B_329, '#skF_10'))), inference(splitRight, [status(thm)], [c_2814])).
% 4.27/1.81  tff(c_3030, plain, (![A_330]: (r2_hidden('#skF_6'(A_330, '#skF_10'), '#skF_8') | ~r2_xboole_0(A_330, '#skF_10'))), inference(resolution, [status(thm)], [c_42, c_2976])).
% 4.27/1.81  tff(c_3043, plain, (~r2_xboole_0('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_3030, c_40])).
% 4.27/1.81  tff(c_3046, plain, ('#skF_10'='#skF_8' | ~r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_26, c_3043])).
% 4.27/1.81  tff(c_3049, plain, ('#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2799, c_3046])).
% 4.27/1.81  tff(c_3051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2113, c_3049])).
% 4.27/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.81  
% 4.27/1.81  Inference rules
% 4.27/1.81  ----------------------
% 4.27/1.81  #Ref     : 0
% 4.27/1.81  #Sup     : 592
% 4.27/1.81  #Fact    : 0
% 4.27/1.81  #Define  : 0
% 4.27/1.81  #Split   : 12
% 4.27/1.81  #Chain   : 0
% 4.27/1.81  #Close   : 0
% 4.27/1.81  
% 4.27/1.81  Ordering : KBO
% 4.27/1.81  
% 4.27/1.81  Simplification rules
% 4.27/1.81  ----------------------
% 4.27/1.81  #Subsume      : 106
% 4.27/1.81  #Demod        : 199
% 4.27/1.81  #Tautology    : 149
% 4.27/1.81  #SimpNegUnit  : 36
% 4.27/1.81  #BackRed      : 108
% 4.27/1.81  
% 4.27/1.81  #Partial instantiations: 0
% 4.27/1.81  #Strategies tried      : 1
% 4.27/1.81  
% 4.27/1.81  Timing (in seconds)
% 4.27/1.81  ----------------------
% 4.27/1.81  Preprocessing        : 0.33
% 4.27/1.81  Parsing              : 0.17
% 4.27/1.81  CNF conversion       : 0.03
% 4.27/1.81  Main loop            : 0.66
% 4.27/1.81  Inferencing          : 0.25
% 4.27/1.81  Reduction            : 0.18
% 4.27/1.81  Demodulation         : 0.11
% 4.27/1.81  BG Simplification    : 0.03
% 4.27/1.81  Subsumption          : 0.14
% 4.27/1.81  Abstraction          : 0.03
% 4.27/1.81  MUC search           : 0.00
% 4.27/1.81  Cooper               : 0.00
% 4.27/1.81  Total                : 1.04
% 4.27/1.81  Index Insertion      : 0.00
% 4.27/1.81  Index Deletion       : 0.00
% 4.27/1.81  Index Matching       : 0.00
% 4.27/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
