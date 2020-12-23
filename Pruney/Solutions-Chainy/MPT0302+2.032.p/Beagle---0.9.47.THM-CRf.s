%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:50 EST 2020

% Result     : Theorem 4.97s
% Output     : CNFRefutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 839 expanded)
%              Number of leaves         :   17 ( 266 expanded)
%              Depth                    :   17
%              Number of atoms          :  162 (2226 expanded)
%              Number of equality atoms :   53 ( 645 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_28,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_210,plain,(
    ! [A_52,B_53,C_54] :
      ( r2_hidden('#skF_1'(A_52,B_53,C_54),B_53)
      | r2_hidden('#skF_2'(A_52,B_53,C_54),C_54)
      | k3_xboole_0(A_52,B_53) = C_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_93,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( r2_hidden(k4_tarski(A_39,B_40),k2_zfmisc_1(C_41,D_42))
      | ~ r2_hidden(B_40,D_42)
      | ~ r2_hidden(A_39,C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    ! [B_20,D_21,A_22,C_23] :
      ( r2_hidden(B_20,D_21)
      | ~ r2_hidden(k4_tarski(A_22,B_20),k2_zfmisc_1(C_23,D_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_55,plain,(
    ! [B_20,A_22] :
      ( r2_hidden(B_20,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_22,B_20),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_52])).

tff(c_112,plain,(
    ! [B_40,A_39] :
      ( r2_hidden(B_40,'#skF_4')
      | ~ r2_hidden(B_40,'#skF_5')
      | ~ r2_hidden(A_39,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_93,c_55])).

tff(c_168,plain,(
    ! [A_50] : ~ r2_hidden(A_50,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_180,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_168])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_180])).

tff(c_187,plain,(
    ! [B_40] :
      ( r2_hidden(B_40,'#skF_4')
      | ~ r2_hidden(B_40,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_464,plain,(
    ! [A_98,C_99] :
      ( r2_hidden('#skF_1'(A_98,'#skF_5',C_99),'#skF_4')
      | r2_hidden('#skF_2'(A_98,'#skF_5',C_99),C_99)
      | k3_xboole_0(A_98,'#skF_5') = C_99 ) ),
    inference(resolution,[status(thm)],[c_210,c_187])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_487,plain,(
    ! [A_98] :
      ( r2_hidden('#skF_2'(A_98,'#skF_5','#skF_4'),'#skF_4')
      | k3_xboole_0(A_98,'#skF_5') = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_464,c_14])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_56,plain,(
    ! [A_24,C_25,B_26,D_27] :
      ( r2_hidden(A_24,C_25)
      | ~ r2_hidden(k4_tarski(A_24,B_26),k2_zfmisc_1(C_25,D_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_59,plain,(
    ! [A_24,B_26] :
      ( r2_hidden(A_24,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_24,B_26),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_56])).

tff(c_111,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(A_39,'#skF_5')
      | ~ r2_hidden(B_40,'#skF_5')
      | ~ r2_hidden(A_39,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_93,c_59])).

tff(c_123,plain,(
    ! [B_46] : ~ r2_hidden(B_46,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_135,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_123])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_135])).

tff(c_142,plain,(
    ! [A_39] :
      ( r2_hidden(A_39,'#skF_5')
      | ~ r2_hidden(A_39,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_143,plain,(
    ! [A_47] :
      ( r2_hidden(A_47,'#skF_5')
      | ~ r2_hidden(A_47,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_399,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_2'(A_89,B_90,'#skF_5'),'#skF_5')
      | k3_xboole_0(A_89,B_90) = '#skF_5'
      | ~ r2_hidden('#skF_1'(A_89,B_90,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_143,c_14])).

tff(c_413,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_4',B_2,'#skF_5'),'#skF_5')
      | k3_xboole_0('#skF_4',B_2) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_18,c_399])).

tff(c_243,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56,B_56),B_56)
      | k3_xboole_0(A_55,B_56) = B_56 ) ),
    inference(resolution,[status(thm)],[c_210,c_14])).

tff(c_256,plain,(
    ! [A_55] :
      ( r2_hidden('#skF_2'(A_55,'#skF_5','#skF_5'),'#skF_4')
      | k3_xboole_0(A_55,'#skF_5') = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_243,c_187])).

tff(c_420,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden('#skF_1'(A_92,B_93,C_94),B_93)
      | ~ r2_hidden('#skF_2'(A_92,B_93,C_94),B_93)
      | ~ r2_hidden('#skF_2'(A_92,B_93,C_94),A_92)
      | k3_xboole_0(A_92,B_93) = C_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_441,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_5','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_5'),'#skF_5')
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_256,c_420])).

tff(c_641,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_441])).

tff(c_654,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_413,c_641])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_496,plain,(
    ! [C_101,B_102] :
      ( ~ r2_hidden('#skF_2'(C_101,B_102,C_101),B_102)
      | r2_hidden('#skF_1'(C_101,B_102,C_101),B_102)
      | k3_xboole_0(C_101,B_102) = C_101 ) ),
    inference(resolution,[status(thm)],[c_16,c_420])).

tff(c_518,plain,(
    ! [C_101] :
      ( r2_hidden('#skF_1'(C_101,'#skF_5',C_101),'#skF_4')
      | ~ r2_hidden('#skF_2'(C_101,'#skF_5',C_101),'#skF_5')
      | k3_xboole_0(C_101,'#skF_5') = C_101 ) ),
    inference(resolution,[status(thm)],[c_496,c_187])).

tff(c_715,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r2_hidden('#skF_1'(A_112,B_113,C_114),C_114)
      | ~ r2_hidden('#skF_2'(A_112,B_113,C_114),B_113)
      | ~ r2_hidden('#skF_2'(A_112,B_113,C_114),A_112)
      | k3_xboole_0(A_112,B_113) = C_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_727,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_5')
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_518,c_715])).

tff(c_753,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_727])).

tff(c_754,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_753])).

tff(c_916,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_754])).

tff(c_921,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_916])).

tff(c_931,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_487,c_921])).

tff(c_933,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_654])).

tff(c_935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_933])).

tff(c_936,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_754])).

tff(c_1003,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_487,c_936])).

tff(c_1005,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1003,c_654])).

tff(c_1007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1005])).

tff(c_1009,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_1016,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1009,c_187])).

tff(c_1008,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_5'
    | r2_hidden('#skF_1'('#skF_4','#skF_5','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_1022,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1008])).

tff(c_1649,plain,(
    ! [A_143,B_144,C_145] :
      ( ~ r2_hidden('#skF_1'(A_143,B_144,C_145),C_145)
      | ~ r2_hidden('#skF_2'(A_143,B_144,C_145),B_144)
      | ~ r2_hidden('#skF_2'(A_143,B_144,C_145),A_143)
      | k3_xboole_0(A_143,B_144) = C_145 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1653,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_5'),'#skF_4')
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1022,c_1649])).

tff(c_1692,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_1009,c_1653])).

tff(c_1696,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_5')
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_518,c_1649])).

tff(c_2119,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_1696])).

tff(c_2120,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2119])).

tff(c_2121,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2120])).

tff(c_2125,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_2121])).

tff(c_2135,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_487,c_2125])).

tff(c_2197,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2135,c_1692])).

tff(c_2199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2197])).

tff(c_2200,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2120])).

tff(c_2211,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_487,c_2200])).

tff(c_2213,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2211,c_1692])).

tff(c_2215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2213])).

tff(c_2216,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1008])).

tff(c_2336,plain,(
    ! [A_167,B_168,C_169] :
      ( ~ r2_hidden('#skF_1'(A_167,B_168,C_169),C_169)
      | ~ r2_hidden('#skF_2'(A_167,B_168,C_169),B_168)
      | ~ r2_hidden('#skF_2'(A_167,B_168,C_169),A_167)
      | k3_xboole_0(A_167,B_168) = C_169 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2351,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_5')
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_518,c_2336])).

tff(c_2378,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2216,c_2351])).

tff(c_2379,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2378])).

tff(c_2532,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2379])).

tff(c_2536,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_2532])).

tff(c_2546,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_487,c_2536])).

tff(c_2548,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2546,c_2216])).

tff(c_2550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2548])).

tff(c_2551,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2379])).

tff(c_2562,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_487,c_2551])).

tff(c_2564,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_2216])).

tff(c_2566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.97/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.97/1.94  
% 4.97/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.97/1.95  %$ r2_hidden > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 4.97/1.95  
% 4.97/1.95  %Foreground sorts:
% 4.97/1.95  
% 4.97/1.95  
% 4.97/1.95  %Background operators:
% 4.97/1.95  
% 4.97/1.95  
% 4.97/1.95  %Foreground operators:
% 4.97/1.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.97/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.97/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.97/1.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.97/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.97/1.95  tff('#skF_5', type, '#skF_5': $i).
% 4.97/1.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.97/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.97/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.97/1.95  tff('#skF_4', type, '#skF_4': $i).
% 4.97/1.95  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.97/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.97/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.97/1.95  
% 4.97/1.97  tff(f_57, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 4.97/1.97  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.97/1.97  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.97/1.97  tff(f_48, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.97/1.97  tff(c_28, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.97/1.97  tff(c_210, plain, (![A_52, B_53, C_54]: (r2_hidden('#skF_1'(A_52, B_53, C_54), B_53) | r2_hidden('#skF_2'(A_52, B_53, C_54), C_54) | k3_xboole_0(A_52, B_53)=C_54)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.97/1.97  tff(c_32, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.97/1.97  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.97/1.97  tff(c_93, plain, (![A_39, B_40, C_41, D_42]: (r2_hidden(k4_tarski(A_39, B_40), k2_zfmisc_1(C_41, D_42)) | ~r2_hidden(B_40, D_42) | ~r2_hidden(A_39, C_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.97/1.97  tff(c_34, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.97/1.97  tff(c_52, plain, (![B_20, D_21, A_22, C_23]: (r2_hidden(B_20, D_21) | ~r2_hidden(k4_tarski(A_22, B_20), k2_zfmisc_1(C_23, D_21)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.97/1.97  tff(c_55, plain, (![B_20, A_22]: (r2_hidden(B_20, '#skF_4') | ~r2_hidden(k4_tarski(A_22, B_20), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_52])).
% 4.97/1.97  tff(c_112, plain, (![B_40, A_39]: (r2_hidden(B_40, '#skF_4') | ~r2_hidden(B_40, '#skF_5') | ~r2_hidden(A_39, '#skF_4'))), inference(resolution, [status(thm)], [c_93, c_55])).
% 4.97/1.97  tff(c_168, plain, (![A_50]: (~r2_hidden(A_50, '#skF_4'))), inference(splitLeft, [status(thm)], [c_112])).
% 4.97/1.97  tff(c_180, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_20, c_168])).
% 4.97/1.97  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_180])).
% 4.97/1.97  tff(c_187, plain, (![B_40]: (r2_hidden(B_40, '#skF_4') | ~r2_hidden(B_40, '#skF_5'))), inference(splitRight, [status(thm)], [c_112])).
% 4.97/1.97  tff(c_464, plain, (![A_98, C_99]: (r2_hidden('#skF_1'(A_98, '#skF_5', C_99), '#skF_4') | r2_hidden('#skF_2'(A_98, '#skF_5', C_99), C_99) | k3_xboole_0(A_98, '#skF_5')=C_99)), inference(resolution, [status(thm)], [c_210, c_187])).
% 4.97/1.97  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.97/1.97  tff(c_487, plain, (![A_98]: (r2_hidden('#skF_2'(A_98, '#skF_5', '#skF_4'), '#skF_4') | k3_xboole_0(A_98, '#skF_5')='#skF_4')), inference(resolution, [status(thm)], [c_464, c_14])).
% 4.97/1.97  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.97/1.97  tff(c_56, plain, (![A_24, C_25, B_26, D_27]: (r2_hidden(A_24, C_25) | ~r2_hidden(k4_tarski(A_24, B_26), k2_zfmisc_1(C_25, D_27)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.97/1.97  tff(c_59, plain, (![A_24, B_26]: (r2_hidden(A_24, '#skF_5') | ~r2_hidden(k4_tarski(A_24, B_26), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_56])).
% 4.97/1.97  tff(c_111, plain, (![A_39, B_40]: (r2_hidden(A_39, '#skF_5') | ~r2_hidden(B_40, '#skF_5') | ~r2_hidden(A_39, '#skF_4'))), inference(resolution, [status(thm)], [c_93, c_59])).
% 4.97/1.97  tff(c_123, plain, (![B_46]: (~r2_hidden(B_46, '#skF_5'))), inference(splitLeft, [status(thm)], [c_111])).
% 4.97/1.97  tff(c_135, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_20, c_123])).
% 4.97/1.97  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_135])).
% 4.97/1.97  tff(c_142, plain, (![A_39]: (r2_hidden(A_39, '#skF_5') | ~r2_hidden(A_39, '#skF_4'))), inference(splitRight, [status(thm)], [c_111])).
% 4.97/1.97  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.97/1.97  tff(c_143, plain, (![A_47]: (r2_hidden(A_47, '#skF_5') | ~r2_hidden(A_47, '#skF_4'))), inference(splitRight, [status(thm)], [c_111])).
% 4.97/1.97  tff(c_399, plain, (![A_89, B_90]: (r2_hidden('#skF_2'(A_89, B_90, '#skF_5'), '#skF_5') | k3_xboole_0(A_89, B_90)='#skF_5' | ~r2_hidden('#skF_1'(A_89, B_90, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_143, c_14])).
% 4.97/1.97  tff(c_413, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_4', B_2, '#skF_5'), '#skF_5') | k3_xboole_0('#skF_4', B_2)='#skF_5')), inference(resolution, [status(thm)], [c_18, c_399])).
% 4.97/1.97  tff(c_243, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56, B_56), B_56) | k3_xboole_0(A_55, B_56)=B_56)), inference(resolution, [status(thm)], [c_210, c_14])).
% 4.97/1.97  tff(c_256, plain, (![A_55]: (r2_hidden('#skF_2'(A_55, '#skF_5', '#skF_5'), '#skF_4') | k3_xboole_0(A_55, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_243, c_187])).
% 4.97/1.97  tff(c_420, plain, (![A_92, B_93, C_94]: (r2_hidden('#skF_1'(A_92, B_93, C_94), B_93) | ~r2_hidden('#skF_2'(A_92, B_93, C_94), B_93) | ~r2_hidden('#skF_2'(A_92, B_93, C_94), A_92) | k3_xboole_0(A_92, B_93)=C_94)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.97/1.97  tff(c_441, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_5'), '#skF_5') | k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_256, c_420])).
% 4.97/1.97  tff(c_641, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_441])).
% 4.97/1.97  tff(c_654, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_413, c_641])).
% 4.97/1.97  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.97/1.97  tff(c_496, plain, (![C_101, B_102]: (~r2_hidden('#skF_2'(C_101, B_102, C_101), B_102) | r2_hidden('#skF_1'(C_101, B_102, C_101), B_102) | k3_xboole_0(C_101, B_102)=C_101)), inference(resolution, [status(thm)], [c_16, c_420])).
% 4.97/1.97  tff(c_518, plain, (![C_101]: (r2_hidden('#skF_1'(C_101, '#skF_5', C_101), '#skF_4') | ~r2_hidden('#skF_2'(C_101, '#skF_5', C_101), '#skF_5') | k3_xboole_0(C_101, '#skF_5')=C_101)), inference(resolution, [status(thm)], [c_496, c_187])).
% 4.97/1.97  tff(c_715, plain, (![A_112, B_113, C_114]: (~r2_hidden('#skF_1'(A_112, B_113, C_114), C_114) | ~r2_hidden('#skF_2'(A_112, B_113, C_114), B_113) | ~r2_hidden('#skF_2'(A_112, B_113, C_114), A_112) | k3_xboole_0(A_112, B_113)=C_114)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.97/1.97  tff(c_727, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_5') | k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_518, c_715])).
% 4.97/1.97  tff(c_753, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_654, c_727])).
% 4.97/1.97  tff(c_754, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_28, c_753])).
% 4.97/1.97  tff(c_916, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_754])).
% 4.97/1.97  tff(c_921, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_142, c_916])).
% 4.97/1.97  tff(c_931, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_487, c_921])).
% 4.97/1.97  tff(c_933, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_931, c_654])).
% 4.97/1.97  tff(c_935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_933])).
% 4.97/1.97  tff(c_936, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_754])).
% 4.97/1.97  tff(c_1003, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_487, c_936])).
% 4.97/1.97  tff(c_1005, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1003, c_654])).
% 4.97/1.97  tff(c_1007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1005])).
% 4.97/1.97  tff(c_1009, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_441])).
% 4.97/1.97  tff(c_1016, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1009, c_187])).
% 4.97/1.97  tff(c_1008, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5' | r2_hidden('#skF_1'('#skF_4', '#skF_5', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_441])).
% 4.97/1.97  tff(c_1022, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1008])).
% 4.97/1.97  tff(c_1649, plain, (![A_143, B_144, C_145]: (~r2_hidden('#skF_1'(A_143, B_144, C_145), C_145) | ~r2_hidden('#skF_2'(A_143, B_144, C_145), B_144) | ~r2_hidden('#skF_2'(A_143, B_144, C_145), A_143) | k3_xboole_0(A_143, B_144)=C_145)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.97/1.97  tff(c_1653, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_5'), '#skF_4') | k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_1022, c_1649])).
% 4.97/1.97  tff(c_1692, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_1009, c_1653])).
% 4.97/1.97  tff(c_1696, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_5') | k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_518, c_1649])).
% 4.97/1.97  tff(c_2119, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1692, c_1696])).
% 4.97/1.97  tff(c_2120, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_28, c_2119])).
% 4.97/1.97  tff(c_2121, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_2120])).
% 4.97/1.97  tff(c_2125, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_142, c_2121])).
% 4.97/1.97  tff(c_2135, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_487, c_2125])).
% 4.97/1.97  tff(c_2197, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2135, c_1692])).
% 4.97/1.97  tff(c_2199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2197])).
% 4.97/1.97  tff(c_2200, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_2120])).
% 4.97/1.97  tff(c_2211, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_487, c_2200])).
% 4.97/1.97  tff(c_2213, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2211, c_1692])).
% 4.97/1.97  tff(c_2215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2213])).
% 4.97/1.97  tff(c_2216, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_1008])).
% 4.97/1.97  tff(c_2336, plain, (![A_167, B_168, C_169]: (~r2_hidden('#skF_1'(A_167, B_168, C_169), C_169) | ~r2_hidden('#skF_2'(A_167, B_168, C_169), B_168) | ~r2_hidden('#skF_2'(A_167, B_168, C_169), A_167) | k3_xboole_0(A_167, B_168)=C_169)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.97/1.97  tff(c_2351, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_5') | k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_518, c_2336])).
% 4.97/1.97  tff(c_2378, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2216, c_2351])).
% 4.97/1.97  tff(c_2379, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_28, c_2378])).
% 4.97/1.97  tff(c_2532, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_2379])).
% 4.97/1.97  tff(c_2536, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_142, c_2532])).
% 4.97/1.97  tff(c_2546, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_487, c_2536])).
% 4.97/1.97  tff(c_2548, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2546, c_2216])).
% 4.97/1.97  tff(c_2550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2548])).
% 4.97/1.97  tff(c_2551, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_2379])).
% 4.97/1.97  tff(c_2562, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_487, c_2551])).
% 4.97/1.97  tff(c_2564, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_2216])).
% 4.97/1.97  tff(c_2566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2564])).
% 4.97/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.97/1.97  
% 4.97/1.97  Inference rules
% 4.97/1.97  ----------------------
% 4.97/1.97  #Ref     : 0
% 4.97/1.97  #Sup     : 523
% 4.97/1.97  #Fact    : 0
% 4.97/1.97  #Define  : 0
% 4.97/1.97  #Split   : 10
% 4.97/1.97  #Chain   : 0
% 4.97/1.97  #Close   : 0
% 4.97/1.97  
% 4.97/1.97  Ordering : KBO
% 4.97/1.97  
% 4.97/1.97  Simplification rules
% 4.97/1.97  ----------------------
% 4.97/1.97  #Subsume      : 213
% 4.97/1.97  #Demod        : 284
% 4.97/1.97  #Tautology    : 105
% 4.97/1.97  #SimpNegUnit  : 44
% 4.97/1.97  #BackRed      : 10
% 4.97/1.97  
% 4.97/1.97  #Partial instantiations: 0
% 4.97/1.97  #Strategies tried      : 1
% 4.97/1.97  
% 4.97/1.97  Timing (in seconds)
% 4.97/1.97  ----------------------
% 4.97/1.97  Preprocessing        : 0.29
% 4.97/1.97  Parsing              : 0.15
% 4.97/1.97  CNF conversion       : 0.02
% 4.97/1.97  Main loop            : 0.90
% 4.97/1.97  Inferencing          : 0.35
% 5.23/1.99  Reduction            : 0.25
% 5.23/1.99  Demodulation         : 0.16
% 5.23/1.99  BG Simplification    : 0.03
% 5.23/1.99  Subsumption          : 0.21
% 5.23/1.99  Abstraction          : 0.04
% 5.23/1.99  MUC search           : 0.00
% 5.23/1.99  Cooper               : 0.00
% 5.23/1.99  Total                : 1.24
% 5.23/1.99  Index Insertion      : 0.00
% 5.23/1.99  Index Deletion       : 0.00
% 5.23/1.99  Index Matching       : 0.00
% 5.23/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
