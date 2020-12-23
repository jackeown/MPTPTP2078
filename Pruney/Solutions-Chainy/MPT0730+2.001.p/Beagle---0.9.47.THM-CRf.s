%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:59 EST 2020

% Result     : Theorem 13.86s
% Output     : CNFRefutation 13.86s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 210 expanded)
%              Number of leaves         :   32 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :  172 ( 378 expanded)
%              Number of equality atoms :   36 (  98 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_87,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_85,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,k1_ordinal1(B))
      <=> ( r2_hidden(A,B)
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_92,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_83,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(A,B)
        & r2_hidden(C,k2_xboole_0(A,B))
        & ~ ( r2_hidden(C,A)
            & ~ r2_hidden(C,B) )
        & ~ ( r2_hidden(C,B)
            & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

tff(c_56,plain,(
    ! [A_35] : r2_hidden(A_35,k1_ordinal1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_21387,plain,(
    ! [A_1658] : k2_xboole_0(A_1658,k1_tarski(A_1658)) = k1_ordinal1(A_1658) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_21393,plain,(
    ! [A_1658] : r1_tarski(A_1658,k1_ordinal1(A_1658)) ),
    inference(superposition,[status(thm),theory(equality)],[c_21387,c_22])).

tff(c_21203,plain,(
    ! [A_1625] : k2_xboole_0(A_1625,k1_tarski(A_1625)) = k1_ordinal1(A_1625) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_21209,plain,(
    ! [A_1625] : r1_tarski(A_1625,k1_ordinal1(A_1625)) ),
    inference(superposition,[status(thm),theory(equality)],[c_21203,c_22])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_4',k1_ordinal1('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_96,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_4',k1_ordinal1('#skF_5'))
    | '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_85,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_104,plain,(
    ! [A_50] : k2_xboole_0(A_50,k1_tarski(A_50)) = k1_ordinal1(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_110,plain,(
    ! [A_50] : r1_tarski(A_50,k1_ordinal1(A_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_22])).

tff(c_70,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_218,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_30,plain,(
    ! [C_19] : r2_hidden(C_19,k1_tarski(C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_86,plain,(
    ! [B_44,A_45] :
      ( ~ r1_tarski(B_44,A_45)
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_94,plain,(
    ! [C_19] : ~ r1_tarski(k1_tarski(C_19),C_19) ),
    inference(resolution,[status(thm)],[c_30,c_86])).

tff(c_170,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1036,plain,(
    ! [A_167,B_168] :
      ( '#skF_1'(k1_tarski(A_167),B_168) = A_167
      | r1_tarski(k1_tarski(A_167),B_168) ) ),
    inference(resolution,[status(thm)],[c_170,c_28])).

tff(c_1054,plain,(
    ! [B_169] : '#skF_1'(k1_tarski(B_169),B_169) = B_169 ),
    inference(resolution,[status(thm)],[c_1036,c_94])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1066,plain,(
    ! [B_169] :
      ( ~ r2_hidden(B_169,B_169)
      | r1_tarski(k1_tarski(B_169),B_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1054,c_4])).

tff(c_1074,plain,(
    ! [B_169] : ~ r2_hidden(B_169,B_169) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1066])).

tff(c_52,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,k1_tarski(B_33)) = A_32
      | r2_hidden(B_33,A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_54,plain,(
    ! [A_34] : k2_xboole_0(A_34,k1_tarski(A_34)) = k1_ordinal1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_906,plain,(
    ! [C_159,A_160,B_161] :
      ( r2_hidden(C_159,A_160)
      | r2_hidden(C_159,B_161)
      | ~ r2_hidden(C_159,k2_xboole_0(A_160,B_161))
      | ~ r1_xboole_0(A_160,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1864,plain,(
    ! [C_252,A_253] :
      ( r2_hidden(C_252,A_253)
      | r2_hidden(C_252,k1_tarski(A_253))
      | ~ r2_hidden(C_252,k1_ordinal1(A_253))
      | ~ r1_xboole_0(A_253,k1_tarski(A_253)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_906])).

tff(c_5106,plain,(
    ! [C_534,A_535] :
      ( r2_hidden(C_534,A_535)
      | r2_hidden(C_534,k1_tarski(A_535))
      | ~ r2_hidden(C_534,k1_ordinal1(A_535))
      | k4_xboole_0(A_535,k1_tarski(A_535)) != A_535 ) ),
    inference(resolution,[status(thm)],[c_26,c_1864])).

tff(c_5109,plain,(
    ! [C_534,B_33] :
      ( r2_hidden(C_534,B_33)
      | r2_hidden(C_534,k1_tarski(B_33))
      | ~ r2_hidden(C_534,k1_ordinal1(B_33))
      | r2_hidden(B_33,B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_5106])).

tff(c_7863,plain,(
    ! [C_721,B_722] :
      ( r2_hidden(C_721,B_722)
      | r2_hidden(C_721,k1_tarski(B_722))
      | ~ r2_hidden(C_721,k1_ordinal1(B_722)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1074,c_5109])).

tff(c_7973,plain,(
    ! [C_724,B_725] :
      ( C_724 = B_725
      | r2_hidden(C_724,B_725)
      | ~ r2_hidden(C_724,k1_ordinal1(B_725)) ) ),
    inference(resolution,[status(thm)],[c_7863,c_28])).

tff(c_8192,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_218,c_7973])).

tff(c_8323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_85,c_8192])).

tff(c_8324,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_8326,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8324])).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_4',k1_ordinal1('#skF_5'))
    | r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_216,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_8327,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8326,c_216])).

tff(c_8330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_8327])).

tff(c_8331,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_8324])).

tff(c_8346,plain,(
    ! [C_729,B_730,A_731] :
      ( r2_hidden(C_729,B_730)
      | ~ r2_hidden(C_729,A_731)
      | ~ r1_tarski(A_731,B_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8359,plain,(
    ! [B_732] :
      ( r2_hidden('#skF_4',B_732)
      | ~ r1_tarski('#skF_5',B_732) ) ),
    inference(resolution,[status(thm)],[c_8331,c_8346])).

tff(c_8364,plain,(
    ~ r1_tarski('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_8359,c_216])).

tff(c_8376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_8364])).

tff(c_8377,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_9245,plain,(
    ! [A_823,B_824] :
      ( '#skF_1'(k1_tarski(A_823),B_824) = A_823
      | r1_tarski(k1_tarski(A_823),B_824) ) ),
    inference(resolution,[status(thm)],[c_170,c_28])).

tff(c_9263,plain,(
    ! [B_825] : '#skF_1'(k1_tarski(B_825),B_825) = B_825 ),
    inference(resolution,[status(thm)],[c_9245,c_94])).

tff(c_9275,plain,(
    ! [B_825] :
      ( ~ r2_hidden(B_825,B_825)
      | r1_tarski(k1_tarski(B_825),B_825) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9263,c_4])).

tff(c_9283,plain,(
    ! [B_825] : ~ r2_hidden(B_825,B_825) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_9275])).

tff(c_9021,plain,(
    ! [C_805,A_806,B_807] :
      ( r2_hidden(C_805,A_806)
      | r2_hidden(C_805,B_807)
      | ~ r2_hidden(C_805,k2_xboole_0(A_806,B_807))
      | ~ r1_xboole_0(A_806,B_807) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9927,plain,(
    ! [C_889,A_890] :
      ( r2_hidden(C_889,A_890)
      | r2_hidden(C_889,k1_tarski(A_890))
      | ~ r2_hidden(C_889,k1_ordinal1(A_890))
      | ~ r1_xboole_0(A_890,k1_tarski(A_890)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_9021])).

tff(c_13302,plain,(
    ! [C_1145,A_1146] :
      ( r2_hidden(C_1145,A_1146)
      | r2_hidden(C_1145,k1_tarski(A_1146))
      | ~ r2_hidden(C_1145,k1_ordinal1(A_1146))
      | k4_xboole_0(A_1146,k1_tarski(A_1146)) != A_1146 ) ),
    inference(resolution,[status(thm)],[c_26,c_9927])).

tff(c_13305,plain,(
    ! [C_1145,B_33] :
      ( r2_hidden(C_1145,B_33)
      | r2_hidden(C_1145,k1_tarski(B_33))
      | ~ r2_hidden(C_1145,k1_ordinal1(B_33))
      | r2_hidden(B_33,B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_13302])).

tff(c_20234,plain,(
    ! [C_1617,B_1618] :
      ( r2_hidden(C_1617,B_1618)
      | r2_hidden(C_1617,k1_tarski(B_1618))
      | ~ r2_hidden(C_1617,k1_ordinal1(B_1618)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9283,c_13305])).

tff(c_20641,plain,(
    ! [C_1620,B_1621] :
      ( C_1620 = B_1621
      | r2_hidden(C_1620,B_1621)
      | ~ r2_hidden(C_1620,k1_ordinal1(B_1621)) ) ),
    inference(resolution,[status(thm)],[c_20234,c_28])).

tff(c_20989,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_8377,c_20641])).

tff(c_21189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_85,c_20989])).

tff(c_21191,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_66,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_21295,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21191,c_66])).

tff(c_21296,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_21295])).

tff(c_21333,plain,(
    ! [C_1652,B_1653,A_1654] :
      ( r2_hidden(C_1652,B_1653)
      | ~ r2_hidden(C_1652,A_1654)
      | ~ r1_tarski(A_1654,B_1653) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_21349,plain,(
    ! [B_1655] :
      ( r2_hidden('#skF_4',B_1655)
      | ~ r1_tarski('#skF_5',B_1655) ) ),
    inference(resolution,[status(thm)],[c_21296,c_21333])).

tff(c_21190,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_21358,plain,(
    ~ r1_tarski('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_21349,c_21190])).

tff(c_21367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21209,c_21358])).

tff(c_21368,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_21295])).

tff(c_21371,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21368,c_21190])).

tff(c_21374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_21371])).

tff(c_21376,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_4','#skF_5')
    | '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_21422,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21376,c_62])).

tff(c_21423,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_21422])).

tff(c_21531,plain,(
    ! [C_1689,B_1690,A_1691] :
      ( r2_hidden(C_1689,B_1690)
      | ~ r2_hidden(C_1689,A_1691)
      | ~ r1_tarski(A_1691,B_1690) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_21544,plain,(
    ! [B_1692] :
      ( r2_hidden('#skF_4',B_1692)
      | ~ r1_tarski('#skF_5',B_1692) ) ),
    inference(resolution,[status(thm)],[c_21423,c_21531])).

tff(c_21375,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_21556,plain,(
    ~ r1_tarski('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_21544,c_21375])).

tff(c_21563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21393,c_21556])).

tff(c_21564,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_21422])).

tff(c_21566,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21564,c_21375])).

tff(c_21569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_21566])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:09:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.86/7.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.86/7.09  
% 13.86/7.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.86/7.09  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 13.86/7.09  
% 13.86/7.09  %Foreground sorts:
% 13.86/7.09  
% 13.86/7.09  
% 13.86/7.09  %Background operators:
% 13.86/7.09  
% 13.86/7.09  
% 13.86/7.09  %Foreground operators:
% 13.86/7.09  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 13.86/7.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.86/7.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.86/7.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.86/7.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.86/7.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.86/7.09  tff('#skF_7', type, '#skF_7': $i).
% 13.86/7.09  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.86/7.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.86/7.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.86/7.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.86/7.09  tff('#skF_5', type, '#skF_5': $i).
% 13.86/7.09  tff('#skF_6', type, '#skF_6': $i).
% 13.86/7.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.86/7.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.86/7.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.86/7.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.86/7.09  tff('#skF_4', type, '#skF_4': $i).
% 13.86/7.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.86/7.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.86/7.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.86/7.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.86/7.09  
% 13.86/7.11  tff(f_87, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 13.86/7.11  tff(f_85, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 13.86/7.11  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.86/7.11  tff(f_99, negated_conjecture, ~(![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 13.86/7.11  tff(f_68, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 13.86/7.11  tff(f_92, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 13.86/7.11  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.86/7.11  tff(f_83, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 13.86/7.11  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 13.86/7.11  tff(f_49, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 13.86/7.11  tff(c_56, plain, (![A_35]: (r2_hidden(A_35, k1_ordinal1(A_35)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.86/7.11  tff(c_21387, plain, (![A_1658]: (k2_xboole_0(A_1658, k1_tarski(A_1658))=k1_ordinal1(A_1658))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.86/7.11  tff(c_22, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.86/7.11  tff(c_21393, plain, (![A_1658]: (r1_tarski(A_1658, k1_ordinal1(A_1658)))), inference(superposition, [status(thm), theory('equality')], [c_21387, c_22])).
% 13.86/7.11  tff(c_21203, plain, (![A_1625]: (k2_xboole_0(A_1625, k1_tarski(A_1625))=k1_ordinal1(A_1625))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.86/7.11  tff(c_21209, plain, (![A_1625]: (r1_tarski(A_1625, k1_ordinal1(A_1625)))), inference(superposition, [status(thm), theory('equality')], [c_21203, c_22])).
% 13.86/7.11  tff(c_64, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_5')) | ~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.86/7.11  tff(c_96, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_64])).
% 13.86/7.11  tff(c_60, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_5')) | '#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.86/7.11  tff(c_85, plain, ('#skF_7'!='#skF_6'), inference(splitLeft, [status(thm)], [c_60])).
% 13.86/7.11  tff(c_104, plain, (![A_50]: (k2_xboole_0(A_50, k1_tarski(A_50))=k1_ordinal1(A_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.86/7.11  tff(c_110, plain, (![A_50]: (r1_tarski(A_50, k1_ordinal1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_22])).
% 13.86/7.11  tff(c_70, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.86/7.11  tff(c_218, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitLeft, [status(thm)], [c_70])).
% 13.86/7.11  tff(c_30, plain, (![C_19]: (r2_hidden(C_19, k1_tarski(C_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.86/7.11  tff(c_86, plain, (![B_44, A_45]: (~r1_tarski(B_44, A_45) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.86/7.11  tff(c_94, plain, (![C_19]: (~r1_tarski(k1_tarski(C_19), C_19))), inference(resolution, [status(thm)], [c_30, c_86])).
% 13.86/7.11  tff(c_170, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.86/7.11  tff(c_28, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.86/7.11  tff(c_1036, plain, (![A_167, B_168]: ('#skF_1'(k1_tarski(A_167), B_168)=A_167 | r1_tarski(k1_tarski(A_167), B_168))), inference(resolution, [status(thm)], [c_170, c_28])).
% 13.86/7.11  tff(c_1054, plain, (![B_169]: ('#skF_1'(k1_tarski(B_169), B_169)=B_169)), inference(resolution, [status(thm)], [c_1036, c_94])).
% 13.86/7.11  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.86/7.11  tff(c_1066, plain, (![B_169]: (~r2_hidden(B_169, B_169) | r1_tarski(k1_tarski(B_169), B_169))), inference(superposition, [status(thm), theory('equality')], [c_1054, c_4])).
% 13.86/7.11  tff(c_1074, plain, (![B_169]: (~r2_hidden(B_169, B_169))), inference(negUnitSimplification, [status(thm)], [c_94, c_1066])).
% 13.86/7.11  tff(c_52, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k1_tarski(B_33))=A_32 | r2_hidden(B_33, A_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.86/7.11  tff(c_26, plain, (![A_13, B_14]: (r1_xboole_0(A_13, B_14) | k4_xboole_0(A_13, B_14)!=A_13)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.86/7.11  tff(c_54, plain, (![A_34]: (k2_xboole_0(A_34, k1_tarski(A_34))=k1_ordinal1(A_34))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.86/7.11  tff(c_906, plain, (![C_159, A_160, B_161]: (r2_hidden(C_159, A_160) | r2_hidden(C_159, B_161) | ~r2_hidden(C_159, k2_xboole_0(A_160, B_161)) | ~r1_xboole_0(A_160, B_161))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.86/7.11  tff(c_1864, plain, (![C_252, A_253]: (r2_hidden(C_252, A_253) | r2_hidden(C_252, k1_tarski(A_253)) | ~r2_hidden(C_252, k1_ordinal1(A_253)) | ~r1_xboole_0(A_253, k1_tarski(A_253)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_906])).
% 13.86/7.11  tff(c_5106, plain, (![C_534, A_535]: (r2_hidden(C_534, A_535) | r2_hidden(C_534, k1_tarski(A_535)) | ~r2_hidden(C_534, k1_ordinal1(A_535)) | k4_xboole_0(A_535, k1_tarski(A_535))!=A_535)), inference(resolution, [status(thm)], [c_26, c_1864])).
% 13.86/7.11  tff(c_5109, plain, (![C_534, B_33]: (r2_hidden(C_534, B_33) | r2_hidden(C_534, k1_tarski(B_33)) | ~r2_hidden(C_534, k1_ordinal1(B_33)) | r2_hidden(B_33, B_33))), inference(superposition, [status(thm), theory('equality')], [c_52, c_5106])).
% 13.86/7.11  tff(c_7863, plain, (![C_721, B_722]: (r2_hidden(C_721, B_722) | r2_hidden(C_721, k1_tarski(B_722)) | ~r2_hidden(C_721, k1_ordinal1(B_722)))), inference(negUnitSimplification, [status(thm)], [c_1074, c_5109])).
% 13.86/7.11  tff(c_7973, plain, (![C_724, B_725]: (C_724=B_725 | r2_hidden(C_724, B_725) | ~r2_hidden(C_724, k1_ordinal1(B_725)))), inference(resolution, [status(thm)], [c_7863, c_28])).
% 13.86/7.11  tff(c_8192, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_218, c_7973])).
% 13.86/7.11  tff(c_8323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_85, c_8192])).
% 13.86/7.11  tff(c_8324, plain, (r2_hidden('#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_70])).
% 13.86/7.11  tff(c_8326, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_8324])).
% 13.86/7.11  tff(c_68, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_5')) | r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.86/7.11  tff(c_216, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_5'))), inference(splitLeft, [status(thm)], [c_68])).
% 13.86/7.11  tff(c_8327, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8326, c_216])).
% 13.86/7.11  tff(c_8330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_8327])).
% 13.86/7.11  tff(c_8331, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_8324])).
% 13.86/7.11  tff(c_8346, plain, (![C_729, B_730, A_731]: (r2_hidden(C_729, B_730) | ~r2_hidden(C_729, A_731) | ~r1_tarski(A_731, B_730))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.86/7.11  tff(c_8359, plain, (![B_732]: (r2_hidden('#skF_4', B_732) | ~r1_tarski('#skF_5', B_732))), inference(resolution, [status(thm)], [c_8331, c_8346])).
% 13.86/7.11  tff(c_8364, plain, (~r1_tarski('#skF_5', k1_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_8359, c_216])).
% 13.86/7.11  tff(c_8376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_8364])).
% 13.86/7.11  tff(c_8377, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitRight, [status(thm)], [c_68])).
% 13.86/7.11  tff(c_9245, plain, (![A_823, B_824]: ('#skF_1'(k1_tarski(A_823), B_824)=A_823 | r1_tarski(k1_tarski(A_823), B_824))), inference(resolution, [status(thm)], [c_170, c_28])).
% 13.86/7.11  tff(c_9263, plain, (![B_825]: ('#skF_1'(k1_tarski(B_825), B_825)=B_825)), inference(resolution, [status(thm)], [c_9245, c_94])).
% 13.86/7.11  tff(c_9275, plain, (![B_825]: (~r2_hidden(B_825, B_825) | r1_tarski(k1_tarski(B_825), B_825))), inference(superposition, [status(thm), theory('equality')], [c_9263, c_4])).
% 13.86/7.11  tff(c_9283, plain, (![B_825]: (~r2_hidden(B_825, B_825))), inference(negUnitSimplification, [status(thm)], [c_94, c_9275])).
% 13.86/7.11  tff(c_9021, plain, (![C_805, A_806, B_807]: (r2_hidden(C_805, A_806) | r2_hidden(C_805, B_807) | ~r2_hidden(C_805, k2_xboole_0(A_806, B_807)) | ~r1_xboole_0(A_806, B_807))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.86/7.11  tff(c_9927, plain, (![C_889, A_890]: (r2_hidden(C_889, A_890) | r2_hidden(C_889, k1_tarski(A_890)) | ~r2_hidden(C_889, k1_ordinal1(A_890)) | ~r1_xboole_0(A_890, k1_tarski(A_890)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_9021])).
% 13.86/7.11  tff(c_13302, plain, (![C_1145, A_1146]: (r2_hidden(C_1145, A_1146) | r2_hidden(C_1145, k1_tarski(A_1146)) | ~r2_hidden(C_1145, k1_ordinal1(A_1146)) | k4_xboole_0(A_1146, k1_tarski(A_1146))!=A_1146)), inference(resolution, [status(thm)], [c_26, c_9927])).
% 13.86/7.11  tff(c_13305, plain, (![C_1145, B_33]: (r2_hidden(C_1145, B_33) | r2_hidden(C_1145, k1_tarski(B_33)) | ~r2_hidden(C_1145, k1_ordinal1(B_33)) | r2_hidden(B_33, B_33))), inference(superposition, [status(thm), theory('equality')], [c_52, c_13302])).
% 13.86/7.11  tff(c_20234, plain, (![C_1617, B_1618]: (r2_hidden(C_1617, B_1618) | r2_hidden(C_1617, k1_tarski(B_1618)) | ~r2_hidden(C_1617, k1_ordinal1(B_1618)))), inference(negUnitSimplification, [status(thm)], [c_9283, c_13305])).
% 13.86/7.11  tff(c_20641, plain, (![C_1620, B_1621]: (C_1620=B_1621 | r2_hidden(C_1620, B_1621) | ~r2_hidden(C_1620, k1_ordinal1(B_1621)))), inference(resolution, [status(thm)], [c_20234, c_28])).
% 13.86/7.11  tff(c_20989, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_8377, c_20641])).
% 13.86/7.11  tff(c_21189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_85, c_20989])).
% 13.86/7.11  tff(c_21191, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 13.86/7.11  tff(c_66, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.86/7.11  tff(c_21295, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21191, c_66])).
% 13.86/7.11  tff(c_21296, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_21295])).
% 13.86/7.11  tff(c_21333, plain, (![C_1652, B_1653, A_1654]: (r2_hidden(C_1652, B_1653) | ~r2_hidden(C_1652, A_1654) | ~r1_tarski(A_1654, B_1653))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.86/7.11  tff(c_21349, plain, (![B_1655]: (r2_hidden('#skF_4', B_1655) | ~r1_tarski('#skF_5', B_1655))), inference(resolution, [status(thm)], [c_21296, c_21333])).
% 13.86/7.11  tff(c_21190, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_5'))), inference(splitRight, [status(thm)], [c_64])).
% 13.86/7.11  tff(c_21358, plain, (~r1_tarski('#skF_5', k1_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_21349, c_21190])).
% 13.86/7.11  tff(c_21367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21209, c_21358])).
% 13.86/7.11  tff(c_21368, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_21295])).
% 13.86/7.11  tff(c_21371, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21368, c_21190])).
% 13.86/7.11  tff(c_21374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_21371])).
% 13.86/7.11  tff(c_21376, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_60])).
% 13.86/7.11  tff(c_62, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_4', '#skF_5') | '#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.86/7.11  tff(c_21422, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21376, c_62])).
% 13.86/7.11  tff(c_21423, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_21422])).
% 13.86/7.11  tff(c_21531, plain, (![C_1689, B_1690, A_1691]: (r2_hidden(C_1689, B_1690) | ~r2_hidden(C_1689, A_1691) | ~r1_tarski(A_1691, B_1690))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.86/7.11  tff(c_21544, plain, (![B_1692]: (r2_hidden('#skF_4', B_1692) | ~r1_tarski('#skF_5', B_1692))), inference(resolution, [status(thm)], [c_21423, c_21531])).
% 13.86/7.11  tff(c_21375, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_5'))), inference(splitRight, [status(thm)], [c_60])).
% 13.86/7.11  tff(c_21556, plain, (~r1_tarski('#skF_5', k1_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_21544, c_21375])).
% 13.86/7.11  tff(c_21563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21393, c_21556])).
% 13.86/7.11  tff(c_21564, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_21422])).
% 13.86/7.11  tff(c_21566, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21564, c_21375])).
% 13.86/7.11  tff(c_21569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_21566])).
% 13.86/7.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.86/7.11  
% 13.86/7.11  Inference rules
% 13.86/7.11  ----------------------
% 13.86/7.11  #Ref     : 0
% 13.86/7.11  #Sup     : 4665
% 13.86/7.11  #Fact    : 18
% 13.86/7.11  #Define  : 0
% 13.86/7.11  #Split   : 8
% 13.86/7.11  #Chain   : 0
% 13.86/7.11  #Close   : 0
% 13.86/7.11  
% 13.86/7.11  Ordering : KBO
% 13.86/7.11  
% 13.86/7.11  Simplification rules
% 13.86/7.11  ----------------------
% 13.86/7.11  #Subsume      : 1106
% 13.86/7.11  #Demod        : 1751
% 13.86/7.11  #Tautology    : 1116
% 13.86/7.11  #SimpNegUnit  : 32
% 13.86/7.11  #BackRed      : 3
% 13.86/7.11  
% 13.86/7.11  #Partial instantiations: 0
% 13.86/7.11  #Strategies tried      : 1
% 13.86/7.11  
% 13.86/7.11  Timing (in seconds)
% 13.86/7.11  ----------------------
% 13.86/7.11  Preprocessing        : 0.32
% 13.86/7.11  Parsing              : 0.17
% 13.86/7.11  CNF conversion       : 0.02
% 13.86/7.11  Main loop            : 6.01
% 13.86/7.11  Inferencing          : 1.21
% 13.86/7.11  Reduction            : 2.60
% 13.86/7.11  Demodulation         : 1.86
% 13.86/7.11  BG Simplification    : 0.08
% 13.86/7.11  Subsumption          : 1.77
% 13.86/7.11  Abstraction          : 0.12
% 13.86/7.11  MUC search           : 0.00
% 13.86/7.11  Cooper               : 0.00
% 13.86/7.11  Total                : 6.37
% 13.86/7.11  Index Insertion      : 0.00
% 13.86/7.11  Index Deletion       : 0.00
% 13.86/7.11  Index Matching       : 0.00
% 13.86/7.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
