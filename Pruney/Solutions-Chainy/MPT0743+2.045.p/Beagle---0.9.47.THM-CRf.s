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
% DateTime   : Thu Dec  3 10:06:14 EST 2020

% Result     : Theorem 24.80s
% Output     : CNFRefutation 24.80s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 457 expanded)
%              Number of leaves         :   20 ( 156 expanded)
%              Depth                    :   19
%              Number of atoms          :  253 (1140 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_62,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_30,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1507,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_1'(A_140,B_141),A_140)
      | r1_tarski(A_140,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1515,plain,(
    ! [A_140] : r1_tarski(A_140,A_140) ),
    inference(resolution,[status(thm)],[c_1507,c_4])).

tff(c_1601,plain,(
    ! [A_158,B_159] :
      ( r1_ordinal1(A_158,B_159)
      | ~ r1_tarski(A_158,B_159)
      | ~ v3_ordinal1(B_159)
      | ~ v3_ordinal1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1605,plain,(
    ! [A_140] :
      ( r1_ordinal1(A_140,A_140)
      | ~ v3_ordinal1(A_140) ) ),
    inference(resolution,[status(thm)],[c_1515,c_1601])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_ordinal1(B_7,A_6)
      | r1_ordinal1(A_6,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ r1_ordinal1(A_9,B_10)
      | ~ v3_ordinal1(B_10)
      | ~ v3_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1624,plain,(
    ! [A_166,B_167] :
      ( r1_tarski(A_166,B_167)
      | ~ r1_ordinal1(A_166,B_167)
      | ~ v3_ordinal1(B_167)
      | ~ v3_ordinal1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_57,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_24,plain,(
    ! [A_14] :
      ( v3_ordinal1(k1_ordinal1(A_14))
      | ~ v3_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_38])).

tff(c_162,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ r1_ordinal1(A_51,B_52)
      | ~ v3_ordinal1(B_52)
      | ~ v3_ordinal1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_59,plain,(
    ! [A_24,B_25] :
      ( ~ r2_hidden(A_24,B_25)
      | r2_hidden(A_24,k1_ordinal1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_63,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(k1_ordinal1(B_25),A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_59,c_26])).

tff(c_1253,plain,(
    ! [B_121,B_122] :
      ( ~ r2_hidden(B_121,B_122)
      | ~ r1_ordinal1(k1_ordinal1(B_122),B_121)
      | ~ v3_ordinal1(B_121)
      | ~ v3_ordinal1(k1_ordinal1(B_122)) ) ),
    inference(resolution,[status(thm)],[c_162,c_63])).

tff(c_1272,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_1253])).

tff(c_1279,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1272])).

tff(c_1280,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1279])).

tff(c_1283,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1280])).

tff(c_1287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1283])).

tff(c_1289,plain,(
    v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1279])).

tff(c_20,plain,(
    ! [B_13] : r2_hidden(B_13,k1_ordinal1(B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_120,plain,(
    ! [C_38,B_39,A_40] :
      ( r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [B_13,B_39] :
      ( r2_hidden(B_13,B_39)
      | ~ r1_tarski(k1_ordinal1(B_13),B_39) ) ),
    inference(resolution,[status(thm)],[c_20,c_120])).

tff(c_1456,plain,(
    ! [B_132,B_133] :
      ( r2_hidden(B_132,B_133)
      | ~ r1_ordinal1(k1_ordinal1(B_132),B_133)
      | ~ v3_ordinal1(B_133)
      | ~ v3_ordinal1(k1_ordinal1(B_132)) ) ),
    inference(resolution,[status(thm)],[c_162,c_129])).

tff(c_1475,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_1456])).

tff(c_1484,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1289,c_28,c_1475])).

tff(c_1486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1484])).

tff(c_1488,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1556,plain,(
    ! [C_148,B_149,A_150] :
      ( r2_hidden(C_148,B_149)
      | ~ r2_hidden(C_148,A_150)
      | ~ r1_tarski(A_150,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1569,plain,(
    ! [B_151] :
      ( r2_hidden('#skF_2',B_151)
      | ~ r1_tarski('#skF_3',B_151) ) ),
    inference(resolution,[status(thm)],[c_1488,c_1556])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1579,plain,(
    ! [B_2,B_151] :
      ( r2_hidden('#skF_2',B_2)
      | ~ r1_tarski(B_151,B_2)
      | ~ r1_tarski('#skF_3',B_151) ) ),
    inference(resolution,[status(thm)],[c_1569,c_2])).

tff(c_1931,plain,(
    ! [B_187,A_188] :
      ( r2_hidden('#skF_2',B_187)
      | ~ r1_tarski('#skF_3',A_188)
      | ~ r1_ordinal1(A_188,B_187)
      | ~ v3_ordinal1(B_187)
      | ~ v3_ordinal1(A_188) ) ),
    inference(resolution,[status(thm)],[c_1624,c_1579])).

tff(c_1937,plain,(
    ! [B_187,B_10] :
      ( r2_hidden('#skF_2',B_187)
      | ~ r1_ordinal1(B_10,B_187)
      | ~ v3_ordinal1(B_187)
      | ~ r1_ordinal1('#skF_3',B_10)
      | ~ v3_ordinal1(B_10)
      | ~ v3_ordinal1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_1931])).

tff(c_19251,plain,(
    ! [B_662,B_663] :
      ( r2_hidden('#skF_2',B_662)
      | ~ r1_ordinal1(B_663,B_662)
      | ~ v3_ordinal1(B_662)
      | ~ r1_ordinal1('#skF_3',B_663)
      | ~ v3_ordinal1(B_663) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1937])).

tff(c_30866,plain,(
    ! [A_765,B_766] :
      ( r2_hidden('#skF_2',A_765)
      | ~ r1_ordinal1('#skF_3',B_766)
      | r1_ordinal1(A_765,B_766)
      | ~ v3_ordinal1(B_766)
      | ~ v3_ordinal1(A_765) ) ),
    inference(resolution,[status(thm)],[c_8,c_19251])).

tff(c_30920,plain,(
    ! [A_765] :
      ( r2_hidden('#skF_2',A_765)
      | r1_ordinal1(A_765,'#skF_3')
      | ~ v3_ordinal1(A_765)
      | ~ v3_ordinal1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1605,c_30866])).

tff(c_30975,plain,(
    ! [A_767] :
      ( r2_hidden('#skF_2',A_767)
      | r1_ordinal1(A_767,'#skF_3')
      | ~ v3_ordinal1(A_767) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30920])).

tff(c_42,plain,(
    ! [B_20,A_21] :
      ( ~ r1_tarski(B_20,A_21)
      | ~ r2_hidden(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    ! [B_13] : ~ r1_tarski(k1_ordinal1(B_13),B_13) ),
    inference(resolution,[status(thm)],[c_20,c_42])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1523,plain,(
    ! [B_143,A_144] :
      ( B_143 = A_144
      | r2_hidden(A_144,B_143)
      | ~ r2_hidden(A_144,k1_ordinal1(B_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2267,plain,(
    ! [B_213,B_214] :
      ( '#skF_1'(k1_ordinal1(B_213),B_214) = B_213
      | r2_hidden('#skF_1'(k1_ordinal1(B_213),B_214),B_213)
      | r1_tarski(k1_ordinal1(B_213),B_214) ) ),
    inference(resolution,[status(thm)],[c_6,c_1523])).

tff(c_2281,plain,(
    ! [B_213] :
      ( '#skF_1'(k1_ordinal1(B_213),B_213) = B_213
      | r1_tarski(k1_ordinal1(B_213),B_213) ) ),
    inference(resolution,[status(thm)],[c_2267,c_4])).

tff(c_2293,plain,(
    ! [B_215] : '#skF_1'(k1_ordinal1(B_215),B_215) = B_215 ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_2281])).

tff(c_2315,plain,(
    ! [B_215] :
      ( ~ r2_hidden(B_215,B_215)
      | r1_tarski(k1_ordinal1(B_215),B_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2293,c_4])).

tff(c_2327,plain,(
    ! [B_215] : ~ r2_hidden(B_215,B_215) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2315])).

tff(c_30987,plain,
    ( r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30975,c_2327])).

tff(c_31003,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30987])).

tff(c_1487,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1706,plain,(
    ! [B_170,A_171] :
      ( r1_ordinal1(B_170,A_171)
      | r1_ordinal1(A_171,B_170)
      | ~ v3_ordinal1(B_170)
      | ~ v3_ordinal1(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1713,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1706,c_1487])).

tff(c_1726,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1713])).

tff(c_1733,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1726])).

tff(c_1736,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1733])).

tff(c_1740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1736])).

tff(c_1742,plain,(
    v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1726])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden(A_12,B_13)
      | r2_hidden(A_12,k1_ordinal1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1501,plain,(
    ! [A_138,B_139] :
      ( ~ r2_hidden('#skF_1'(A_138,B_139),B_139)
      | r1_tarski(A_138,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1765,plain,(
    ! [A_175,B_176] :
      ( r1_tarski(A_175,k1_ordinal1(B_176))
      | ~ r2_hidden('#skF_1'(A_175,k1_ordinal1(B_176)),B_176) ) ),
    inference(resolution,[status(thm)],[c_22,c_1501])).

tff(c_1776,plain,(
    ! [A_177] : r1_tarski(A_177,k1_ordinal1(A_177)) ),
    inference(resolution,[status(thm)],[c_6,c_1765])).

tff(c_1581,plain,(
    ! [B_151] :
      ( ~ r1_tarski(B_151,'#skF_2')
      | ~ r1_tarski('#skF_3',B_151) ) ),
    inference(resolution,[status(thm)],[c_1569,c_26])).

tff(c_1643,plain,(
    ! [A_166] :
      ( ~ r1_tarski('#skF_3',A_166)
      | ~ r1_ordinal1(A_166,'#skF_2')
      | ~ v3_ordinal1('#skF_2')
      | ~ v3_ordinal1(A_166) ) ),
    inference(resolution,[status(thm)],[c_1624,c_1581])).

tff(c_1664,plain,(
    ! [A_166] :
      ( ~ r1_tarski('#skF_3',A_166)
      | ~ r1_ordinal1(A_166,'#skF_2')
      | ~ v3_ordinal1(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1643])).

tff(c_1798,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1776,c_1664])).

tff(c_1836,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1798])).

tff(c_1839,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1836])).

tff(c_1843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1839])).

tff(c_1845,plain,(
    v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1798])).

tff(c_1844,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1798])).

tff(c_1848,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_1844])).

tff(c_1854,plain,(
    r1_ordinal1('#skF_2',k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1845,c_1848])).

tff(c_2015,plain,(
    ! [A_196,B_197,B_198] :
      ( r2_hidden('#skF_1'(A_196,B_197),B_198)
      | ~ r1_tarski(A_196,B_198)
      | r1_tarski(A_196,B_197) ) ),
    inference(resolution,[status(thm)],[c_6,c_1556])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | r2_hidden(A_12,B_13)
      | ~ r2_hidden(A_12,k1_ordinal1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4046,plain,(
    ! [B_306,A_307,B_308] :
      ( B_306 = '#skF_1'(A_307,B_308)
      | r2_hidden('#skF_1'(A_307,B_308),B_306)
      | ~ r1_tarski(A_307,k1_ordinal1(B_306))
      | r1_tarski(A_307,B_308) ) ),
    inference(resolution,[status(thm)],[c_2015,c_18])).

tff(c_4566,plain,(
    ! [A_330,B_331] :
      ( '#skF_1'(A_330,B_331) = B_331
      | ~ r1_tarski(A_330,k1_ordinal1(B_331))
      | r1_tarski(A_330,B_331) ) ),
    inference(resolution,[status(thm)],[c_4046,c_4])).

tff(c_51694,plain,(
    ! [A_974,B_975] :
      ( '#skF_1'(A_974,B_975) = B_975
      | r1_tarski(A_974,B_975)
      | ~ r1_ordinal1(A_974,k1_ordinal1(B_975))
      | ~ v3_ordinal1(k1_ordinal1(B_975))
      | ~ v3_ordinal1(A_974) ) ),
    inference(resolution,[status(thm)],[c_14,c_4566])).

tff(c_51781,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | r1_tarski('#skF_2','#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1854,c_51694])).

tff(c_51869,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1845,c_51781])).

tff(c_51976,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_51869])).

tff(c_4197,plain,(
    ! [B_313,B_314,B_315] :
      ( r2_hidden('#skF_1'(k1_ordinal1(B_313),B_314),B_315)
      | ~ r1_tarski(B_313,B_315)
      | '#skF_1'(k1_ordinal1(B_313),B_314) = B_313
      | r1_tarski(k1_ordinal1(B_313),B_314) ) ),
    inference(resolution,[status(thm)],[c_2267,c_2])).

tff(c_5599,plain,(
    ! [B_368,B_369] :
      ( ~ r1_tarski(B_368,B_369)
      | '#skF_1'(k1_ordinal1(B_368),B_369) = B_368
      | r1_tarski(k1_ordinal1(B_368),B_369) ) ),
    inference(resolution,[status(thm)],[c_4197,c_4])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_ordinal1(A_9,B_10)
      | ~ r1_tarski(A_9,B_10)
      | ~ v3_ordinal1(B_10)
      | ~ v3_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70089,plain,(
    ! [B_1071,B_1072] :
      ( r1_ordinal1(k1_ordinal1(B_1071),B_1072)
      | ~ v3_ordinal1(B_1072)
      | ~ v3_ordinal1(k1_ordinal1(B_1071))
      | ~ r1_tarski(B_1071,B_1072)
      | '#skF_1'(k1_ordinal1(B_1071),B_1072) = B_1071 ) ),
    inference(resolution,[status(thm)],[c_5599,c_12])).

tff(c_70250,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3')
    | '#skF_1'(k1_ordinal1('#skF_2'),'#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_70089,c_1487])).

tff(c_70345,plain,(
    '#skF_1'(k1_ordinal1('#skF_2'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51976,c_1742,c_28,c_70250])).

tff(c_70435,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r1_tarski(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_70345,c_4])).

tff(c_70473,plain,(
    r1_tarski(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_70435])).

tff(c_70567,plain,
    ( r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_70473,c_12])).

tff(c_70654,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_28,c_70567])).

tff(c_70656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1487,c_70654])).

tff(c_70658,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_51869])).

tff(c_70664,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_70658])).

tff(c_70672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_31003,c_70664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:36:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.80/16.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.80/16.05  
% 24.80/16.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.80/16.05  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 24.80/16.05  
% 24.80/16.05  %Foreground sorts:
% 24.80/16.05  
% 24.80/16.05  
% 24.80/16.05  %Background operators:
% 24.80/16.05  
% 24.80/16.05  
% 24.80/16.05  %Foreground operators:
% 24.80/16.05  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 24.80/16.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.80/16.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.80/16.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 24.80/16.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.80/16.05  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 24.80/16.05  tff('#skF_2', type, '#skF_2': $i).
% 24.80/16.05  tff('#skF_3', type, '#skF_3': $i).
% 24.80/16.05  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 24.80/16.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.80/16.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.80/16.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.80/16.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 24.80/16.05  
% 24.80/16.07  tff(f_77, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 24.80/16.07  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 24.80/16.07  tff(f_50, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 24.80/16.07  tff(f_40, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 24.80/16.07  tff(f_62, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 24.80/16.07  tff(f_58, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 24.80/16.07  tff(f_67, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 24.80/16.07  tff(c_30, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 24.80/16.07  tff(c_28, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 24.80/16.07  tff(c_1507, plain, (![A_140, B_141]: (r2_hidden('#skF_1'(A_140, B_141), A_140) | r1_tarski(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.80/16.07  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.80/16.07  tff(c_1515, plain, (![A_140]: (r1_tarski(A_140, A_140))), inference(resolution, [status(thm)], [c_1507, c_4])).
% 24.80/16.07  tff(c_1601, plain, (![A_158, B_159]: (r1_ordinal1(A_158, B_159) | ~r1_tarski(A_158, B_159) | ~v3_ordinal1(B_159) | ~v3_ordinal1(A_158))), inference(cnfTransformation, [status(thm)], [f_50])).
% 24.80/16.07  tff(c_1605, plain, (![A_140]: (r1_ordinal1(A_140, A_140) | ~v3_ordinal1(A_140))), inference(resolution, [status(thm)], [c_1515, c_1601])).
% 24.80/16.07  tff(c_8, plain, (![B_7, A_6]: (r1_ordinal1(B_7, A_6) | r1_ordinal1(A_6, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 24.80/16.07  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~r1_ordinal1(A_9, B_10) | ~v3_ordinal1(B_10) | ~v3_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 24.80/16.07  tff(c_1624, plain, (![A_166, B_167]: (r1_tarski(A_166, B_167) | ~r1_ordinal1(A_166, B_167) | ~v3_ordinal1(B_167) | ~v3_ordinal1(A_166))), inference(cnfTransformation, [status(thm)], [f_50])).
% 24.80/16.07  tff(c_32, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 24.80/16.07  tff(c_57, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 24.80/16.07  tff(c_24, plain, (![A_14]: (v3_ordinal1(k1_ordinal1(A_14)) | ~v3_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 24.80/16.07  tff(c_38, plain, (r2_hidden('#skF_2', '#skF_3') | r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 24.80/16.07  tff(c_58, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_57, c_38])).
% 24.80/16.07  tff(c_162, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~r1_ordinal1(A_51, B_52) | ~v3_ordinal1(B_52) | ~v3_ordinal1(A_51))), inference(cnfTransformation, [status(thm)], [f_50])).
% 24.80/16.07  tff(c_59, plain, (![A_24, B_25]: (~r2_hidden(A_24, B_25) | r2_hidden(A_24, k1_ordinal1(B_25)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 24.80/16.07  tff(c_26, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 24.80/16.07  tff(c_63, plain, (![B_25, A_24]: (~r1_tarski(k1_ordinal1(B_25), A_24) | ~r2_hidden(A_24, B_25))), inference(resolution, [status(thm)], [c_59, c_26])).
% 24.80/16.07  tff(c_1253, plain, (![B_121, B_122]: (~r2_hidden(B_121, B_122) | ~r1_ordinal1(k1_ordinal1(B_122), B_121) | ~v3_ordinal1(B_121) | ~v3_ordinal1(k1_ordinal1(B_122)))), inference(resolution, [status(thm)], [c_162, c_63])).
% 24.80/16.07  tff(c_1272, plain, (~r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_1253])).
% 24.80/16.07  tff(c_1279, plain, (~r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1272])).
% 24.80/16.07  tff(c_1280, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1279])).
% 24.80/16.07  tff(c_1283, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1280])).
% 24.80/16.07  tff(c_1287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1283])).
% 24.80/16.07  tff(c_1289, plain, (v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_1279])).
% 24.80/16.07  tff(c_20, plain, (![B_13]: (r2_hidden(B_13, k1_ordinal1(B_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 24.80/16.07  tff(c_120, plain, (![C_38, B_39, A_40]: (r2_hidden(C_38, B_39) | ~r2_hidden(C_38, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.80/16.07  tff(c_129, plain, (![B_13, B_39]: (r2_hidden(B_13, B_39) | ~r1_tarski(k1_ordinal1(B_13), B_39))), inference(resolution, [status(thm)], [c_20, c_120])).
% 24.80/16.07  tff(c_1456, plain, (![B_132, B_133]: (r2_hidden(B_132, B_133) | ~r1_ordinal1(k1_ordinal1(B_132), B_133) | ~v3_ordinal1(B_133) | ~v3_ordinal1(k1_ordinal1(B_132)))), inference(resolution, [status(thm)], [c_162, c_129])).
% 24.80/16.07  tff(c_1475, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_1456])).
% 24.80/16.07  tff(c_1484, plain, (r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1289, c_28, c_1475])).
% 24.80/16.07  tff(c_1486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_1484])).
% 24.80/16.07  tff(c_1488, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 24.80/16.07  tff(c_1556, plain, (![C_148, B_149, A_150]: (r2_hidden(C_148, B_149) | ~r2_hidden(C_148, A_150) | ~r1_tarski(A_150, B_149))), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.80/16.07  tff(c_1569, plain, (![B_151]: (r2_hidden('#skF_2', B_151) | ~r1_tarski('#skF_3', B_151))), inference(resolution, [status(thm)], [c_1488, c_1556])).
% 24.80/16.07  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.80/16.07  tff(c_1579, plain, (![B_2, B_151]: (r2_hidden('#skF_2', B_2) | ~r1_tarski(B_151, B_2) | ~r1_tarski('#skF_3', B_151))), inference(resolution, [status(thm)], [c_1569, c_2])).
% 24.80/16.07  tff(c_1931, plain, (![B_187, A_188]: (r2_hidden('#skF_2', B_187) | ~r1_tarski('#skF_3', A_188) | ~r1_ordinal1(A_188, B_187) | ~v3_ordinal1(B_187) | ~v3_ordinal1(A_188))), inference(resolution, [status(thm)], [c_1624, c_1579])).
% 24.80/16.07  tff(c_1937, plain, (![B_187, B_10]: (r2_hidden('#skF_2', B_187) | ~r1_ordinal1(B_10, B_187) | ~v3_ordinal1(B_187) | ~r1_ordinal1('#skF_3', B_10) | ~v3_ordinal1(B_10) | ~v3_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_1931])).
% 24.80/16.07  tff(c_19251, plain, (![B_662, B_663]: (r2_hidden('#skF_2', B_662) | ~r1_ordinal1(B_663, B_662) | ~v3_ordinal1(B_662) | ~r1_ordinal1('#skF_3', B_663) | ~v3_ordinal1(B_663))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1937])).
% 24.80/16.07  tff(c_30866, plain, (![A_765, B_766]: (r2_hidden('#skF_2', A_765) | ~r1_ordinal1('#skF_3', B_766) | r1_ordinal1(A_765, B_766) | ~v3_ordinal1(B_766) | ~v3_ordinal1(A_765))), inference(resolution, [status(thm)], [c_8, c_19251])).
% 24.80/16.07  tff(c_30920, plain, (![A_765]: (r2_hidden('#skF_2', A_765) | r1_ordinal1(A_765, '#skF_3') | ~v3_ordinal1(A_765) | ~v3_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_1605, c_30866])).
% 24.80/16.07  tff(c_30975, plain, (![A_767]: (r2_hidden('#skF_2', A_767) | r1_ordinal1(A_767, '#skF_3') | ~v3_ordinal1(A_767))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30920])).
% 24.80/16.07  tff(c_42, plain, (![B_20, A_21]: (~r1_tarski(B_20, A_21) | ~r2_hidden(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 24.80/16.07  tff(c_46, plain, (![B_13]: (~r1_tarski(k1_ordinal1(B_13), B_13))), inference(resolution, [status(thm)], [c_20, c_42])).
% 24.80/16.07  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.80/16.07  tff(c_1523, plain, (![B_143, A_144]: (B_143=A_144 | r2_hidden(A_144, B_143) | ~r2_hidden(A_144, k1_ordinal1(B_143)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 24.80/16.07  tff(c_2267, plain, (![B_213, B_214]: ('#skF_1'(k1_ordinal1(B_213), B_214)=B_213 | r2_hidden('#skF_1'(k1_ordinal1(B_213), B_214), B_213) | r1_tarski(k1_ordinal1(B_213), B_214))), inference(resolution, [status(thm)], [c_6, c_1523])).
% 24.80/16.07  tff(c_2281, plain, (![B_213]: ('#skF_1'(k1_ordinal1(B_213), B_213)=B_213 | r1_tarski(k1_ordinal1(B_213), B_213))), inference(resolution, [status(thm)], [c_2267, c_4])).
% 24.80/16.07  tff(c_2293, plain, (![B_215]: ('#skF_1'(k1_ordinal1(B_215), B_215)=B_215)), inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_2281])).
% 24.80/16.07  tff(c_2315, plain, (![B_215]: (~r2_hidden(B_215, B_215) | r1_tarski(k1_ordinal1(B_215), B_215))), inference(superposition, [status(thm), theory('equality')], [c_2293, c_4])).
% 24.80/16.07  tff(c_2327, plain, (![B_215]: (~r2_hidden(B_215, B_215))), inference(negUnitSimplification, [status(thm)], [c_46, c_2315])).
% 24.80/16.07  tff(c_30987, plain, (r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_30975, c_2327])).
% 24.80/16.07  tff(c_31003, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30987])).
% 24.80/16.07  tff(c_1487, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 24.80/16.07  tff(c_1706, plain, (![B_170, A_171]: (r1_ordinal1(B_170, A_171) | r1_ordinal1(A_171, B_170) | ~v3_ordinal1(B_170) | ~v3_ordinal1(A_171))), inference(cnfTransformation, [status(thm)], [f_40])).
% 24.80/16.07  tff(c_1713, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_1706, c_1487])).
% 24.80/16.07  tff(c_1726, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1713])).
% 24.80/16.07  tff(c_1733, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1726])).
% 24.80/16.07  tff(c_1736, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1733])).
% 24.80/16.07  tff(c_1740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1736])).
% 24.80/16.07  tff(c_1742, plain, (v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_1726])).
% 24.80/16.07  tff(c_22, plain, (![A_12, B_13]: (~r2_hidden(A_12, B_13) | r2_hidden(A_12, k1_ordinal1(B_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 24.80/16.07  tff(c_1501, plain, (![A_138, B_139]: (~r2_hidden('#skF_1'(A_138, B_139), B_139) | r1_tarski(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.80/16.07  tff(c_1765, plain, (![A_175, B_176]: (r1_tarski(A_175, k1_ordinal1(B_176)) | ~r2_hidden('#skF_1'(A_175, k1_ordinal1(B_176)), B_176))), inference(resolution, [status(thm)], [c_22, c_1501])).
% 24.80/16.07  tff(c_1776, plain, (![A_177]: (r1_tarski(A_177, k1_ordinal1(A_177)))), inference(resolution, [status(thm)], [c_6, c_1765])).
% 24.80/16.07  tff(c_1581, plain, (![B_151]: (~r1_tarski(B_151, '#skF_2') | ~r1_tarski('#skF_3', B_151))), inference(resolution, [status(thm)], [c_1569, c_26])).
% 24.80/16.07  tff(c_1643, plain, (![A_166]: (~r1_tarski('#skF_3', A_166) | ~r1_ordinal1(A_166, '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(A_166))), inference(resolution, [status(thm)], [c_1624, c_1581])).
% 24.80/16.07  tff(c_1664, plain, (![A_166]: (~r1_tarski('#skF_3', A_166) | ~r1_ordinal1(A_166, '#skF_2') | ~v3_ordinal1(A_166))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1643])).
% 24.80/16.07  tff(c_1798, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_1776, c_1664])).
% 24.80/16.07  tff(c_1836, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1798])).
% 24.80/16.07  tff(c_1839, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1836])).
% 24.80/16.07  tff(c_1843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1839])).
% 24.80/16.07  tff(c_1845, plain, (v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_1798])).
% 24.80/16.07  tff(c_1844, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_1798])).
% 24.80/16.07  tff(c_1848, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_1844])).
% 24.80/16.07  tff(c_1854, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1845, c_1848])).
% 24.80/16.07  tff(c_2015, plain, (![A_196, B_197, B_198]: (r2_hidden('#skF_1'(A_196, B_197), B_198) | ~r1_tarski(A_196, B_198) | r1_tarski(A_196, B_197))), inference(resolution, [status(thm)], [c_6, c_1556])).
% 24.80/16.07  tff(c_18, plain, (![B_13, A_12]: (B_13=A_12 | r2_hidden(A_12, B_13) | ~r2_hidden(A_12, k1_ordinal1(B_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 24.80/16.07  tff(c_4046, plain, (![B_306, A_307, B_308]: (B_306='#skF_1'(A_307, B_308) | r2_hidden('#skF_1'(A_307, B_308), B_306) | ~r1_tarski(A_307, k1_ordinal1(B_306)) | r1_tarski(A_307, B_308))), inference(resolution, [status(thm)], [c_2015, c_18])).
% 24.80/16.07  tff(c_4566, plain, (![A_330, B_331]: ('#skF_1'(A_330, B_331)=B_331 | ~r1_tarski(A_330, k1_ordinal1(B_331)) | r1_tarski(A_330, B_331))), inference(resolution, [status(thm)], [c_4046, c_4])).
% 24.80/16.07  tff(c_51694, plain, (![A_974, B_975]: ('#skF_1'(A_974, B_975)=B_975 | r1_tarski(A_974, B_975) | ~r1_ordinal1(A_974, k1_ordinal1(B_975)) | ~v3_ordinal1(k1_ordinal1(B_975)) | ~v3_ordinal1(A_974))), inference(resolution, [status(thm)], [c_14, c_4566])).
% 24.80/16.07  tff(c_51781, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | r1_tarski('#skF_2', '#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_1854, c_51694])).
% 24.80/16.07  tff(c_51869, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1845, c_51781])).
% 24.80/16.07  tff(c_51976, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_51869])).
% 24.80/16.07  tff(c_4197, plain, (![B_313, B_314, B_315]: (r2_hidden('#skF_1'(k1_ordinal1(B_313), B_314), B_315) | ~r1_tarski(B_313, B_315) | '#skF_1'(k1_ordinal1(B_313), B_314)=B_313 | r1_tarski(k1_ordinal1(B_313), B_314))), inference(resolution, [status(thm)], [c_2267, c_2])).
% 24.80/16.07  tff(c_5599, plain, (![B_368, B_369]: (~r1_tarski(B_368, B_369) | '#skF_1'(k1_ordinal1(B_368), B_369)=B_368 | r1_tarski(k1_ordinal1(B_368), B_369))), inference(resolution, [status(thm)], [c_4197, c_4])).
% 24.80/16.07  tff(c_12, plain, (![A_9, B_10]: (r1_ordinal1(A_9, B_10) | ~r1_tarski(A_9, B_10) | ~v3_ordinal1(B_10) | ~v3_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 24.80/16.07  tff(c_70089, plain, (![B_1071, B_1072]: (r1_ordinal1(k1_ordinal1(B_1071), B_1072) | ~v3_ordinal1(B_1072) | ~v3_ordinal1(k1_ordinal1(B_1071)) | ~r1_tarski(B_1071, B_1072) | '#skF_1'(k1_ordinal1(B_1071), B_1072)=B_1071)), inference(resolution, [status(thm)], [c_5599, c_12])).
% 24.80/16.07  tff(c_70250, plain, (~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~r1_tarski('#skF_2', '#skF_3') | '#skF_1'(k1_ordinal1('#skF_2'), '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_70089, c_1487])).
% 24.80/16.07  tff(c_70345, plain, ('#skF_1'(k1_ordinal1('#skF_2'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_51976, c_1742, c_28, c_70250])).
% 24.80/16.07  tff(c_70435, plain, (~r2_hidden('#skF_2', '#skF_3') | r1_tarski(k1_ordinal1('#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_70345, c_4])).
% 24.80/16.07  tff(c_70473, plain, (r1_tarski(k1_ordinal1('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_70435])).
% 24.80/16.07  tff(c_70567, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_70473, c_12])).
% 24.80/16.07  tff(c_70654, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_28, c_70567])).
% 24.80/16.07  tff(c_70656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1487, c_70654])).
% 24.80/16.07  tff(c_70658, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_51869])).
% 24.80/16.07  tff(c_70664, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_70658])).
% 24.80/16.07  tff(c_70672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_31003, c_70664])).
% 24.80/16.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.80/16.07  
% 24.80/16.07  Inference rules
% 24.80/16.07  ----------------------
% 24.80/16.07  #Ref     : 0
% 24.80/16.07  #Sup     : 14766
% 24.80/16.07  #Fact    : 17
% 24.80/16.07  #Define  : 0
% 24.80/16.07  #Split   : 11
% 24.80/16.07  #Chain   : 0
% 24.80/16.07  #Close   : 0
% 24.80/16.07  
% 24.80/16.07  Ordering : KBO
% 24.80/16.07  
% 24.80/16.07  Simplification rules
% 24.80/16.07  ----------------------
% 24.80/16.07  #Subsume      : 4734
% 24.80/16.07  #Demod        : 4106
% 24.80/16.07  #Tautology    : 1061
% 24.80/16.07  #SimpNegUnit  : 273
% 24.80/16.07  #BackRed      : 0
% 24.80/16.07  
% 24.80/16.07  #Partial instantiations: 0
% 24.80/16.07  #Strategies tried      : 1
% 24.80/16.07  
% 24.80/16.07  Timing (in seconds)
% 24.80/16.07  ----------------------
% 24.80/16.07  Preprocessing        : 0.28
% 24.80/16.07  Parsing              : 0.16
% 24.80/16.07  CNF conversion       : 0.02
% 24.80/16.08  Main loop            : 15.03
% 24.80/16.08  Inferencing          : 1.60
% 24.80/16.08  Reduction            : 2.95
% 24.80/16.08  Demodulation         : 1.82
% 24.80/16.08  BG Simplification    : 0.18
% 24.80/16.08  Subsumption          : 9.61
% 24.80/16.08  Abstraction          : 0.29
% 24.80/16.08  MUC search           : 0.00
% 24.80/16.08  Cooper               : 0.00
% 24.80/16.08  Total                : 15.36
% 24.80/16.08  Index Insertion      : 0.00
% 24.80/16.08  Index Deletion       : 0.00
% 24.80/16.08  Index Matching       : 0.00
% 24.80/16.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
