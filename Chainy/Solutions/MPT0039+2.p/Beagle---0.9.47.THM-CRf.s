%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0039+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:11 EST 2020

% Result     : Theorem 12.39s
% Output     : CNFRefutation 12.39s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 642 expanded)
%              Number of leaves         :   54 ( 241 expanded)
%              Depth                    :   14
%              Number of atoms          :  202 (1060 expanded)
%              Number of equality atoms :   55 ( 404 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_22',type,(
    '#skF_22': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_365,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

tff(f_127,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_381,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_199,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t4_xboole_0)).

tff(f_373,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d5_xboole_0)).

tff(f_125,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

tff(f_234,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k5_xboole_0)).

tff(f_109,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d6_xboole_0)).

tff(f_150,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t1_xboole_0)).

tff(f_157,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t2_tarski)).

tff(f_120,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

tff(f_226,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t6_xboole_0)).

tff(c_262,plain,(
    '#skF_21' != '#skF_22' ),
    inference(cnfTransformation,[status(thm)],[f_365])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_2'(A_15,B_16),A_15)
      | r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_106,plain,(
    ! [A_46] : k3_xboole_0(A_46,A_46) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_386,plain,(
    ! [A_190] :
      ( k1_xboole_0 = A_190
      | ~ v1_xboole_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_381])).

tff(c_395,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_386])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1659,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_82])).

tff(c_1756,plain,(
    ! [A_273,B_274,C_275] :
      ( ~ r1_xboole_0(A_273,B_274)
      | ~ r2_hidden(C_275,k3_xboole_0(A_273,B_274)) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_1788,plain,(
    ! [A_276,C_277] :
      ( ~ r1_xboole_0(A_276,A_276)
      | ~ r2_hidden(C_277,A_276) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_1756])).

tff(c_1791,plain,(
    ! [C_277,B_41] :
      ( ~ r2_hidden(C_277,B_41)
      | k3_xboole_0(B_41,B_41) != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1659,c_1788])).

tff(c_1794,plain,(
    ! [C_277] : ~ r2_hidden(C_277,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1791])).

tff(c_270,plain,(
    ! [A_159] : k4_xboole_0(k1_xboole_0,A_159) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_373])).

tff(c_399,plain,(
    ! [A_159] : k4_xboole_0('#skF_9',A_159) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_395,c_270])).

tff(c_21263,plain,(
    ! [D_900,A_901,B_902] :
      ( r2_hidden(D_900,A_901)
      | ~ r2_hidden(D_900,k4_xboole_0(A_901,B_902)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_21280,plain,(
    ! [D_900] :
      ( r2_hidden(D_900,'#skF_9')
      | ~ r2_hidden(D_900,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_21263])).

tff(c_21286,plain,(
    ! [D_900] : ~ r2_hidden(D_900,'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_1794,c_21280])).

tff(c_104,plain,(
    ! [A_44] : k2_xboole_0(A_44,A_44) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_190,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_968,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | A_79 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_190])).

tff(c_264,plain,(
    k4_xboole_0('#skF_21','#skF_22') = k4_xboole_0('#skF_22','#skF_21') ),
    inference(cnfTransformation,[status(thm)],[f_365])).

tff(c_1967,plain,(
    ! [D_295,B_296,A_297] :
      ( ~ r2_hidden(D_295,B_296)
      | ~ r2_hidden(D_295,k4_xboole_0(A_297,B_296)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2012,plain,(
    ! [D_303] :
      ( ~ r2_hidden(D_303,'#skF_22')
      | ~ r2_hidden(D_303,k4_xboole_0('#skF_22','#skF_21')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_1967])).

tff(c_2021,plain,
    ( ~ r2_hidden('#skF_18'(k4_xboole_0('#skF_22','#skF_21')),'#skF_22')
    | k4_xboole_0('#skF_22','#skF_21') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_968,c_2012])).

tff(c_2067,plain,(
    ~ r2_hidden('#skF_18'(k4_xboole_0('#skF_22','#skF_21')),'#skF_22') ),
    inference(splitLeft,[status(thm)],[c_2021])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_xboole_0(A_11)
      | r2_hidden('#skF_1'(A_11),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1795,plain,(
    ! [C_278,B_279] :
      ( ~ r2_hidden(C_278,B_279)
      | B_279 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1791])).

tff(c_1803,plain,(
    ! [A_11] :
      ( A_11 != '#skF_9'
      | v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_1795])).

tff(c_2206,plain,(
    ! [D_316,A_317,B_318] :
      ( r2_hidden(D_316,A_317)
      | ~ r2_hidden(D_316,k4_xboole_0(A_317,B_318)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2217,plain,(
    ! [D_316] :
      ( r2_hidden(D_316,'#skF_9')
      | ~ r2_hidden(D_316,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_2206])).

tff(c_2226,plain,(
    ! [D_316] : ~ r2_hidden(D_316,'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_1794,c_2217])).

tff(c_2287,plain,(
    ! [D_323] :
      ( r2_hidden(D_323,'#skF_21')
      | ~ r2_hidden(D_323,k4_xboole_0('#skF_22','#skF_21')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_2206])).

tff(c_2297,plain,
    ( r2_hidden('#skF_1'(k4_xboole_0('#skF_22','#skF_21')),'#skF_21')
    | v1_xboole_0(k4_xboole_0('#skF_22','#skF_21')) ),
    inference(resolution,[status(thm)],[c_14,c_2287])).

tff(c_2643,plain,(
    v1_xboole_0(k4_xboole_0('#skF_22','#skF_21')) ),
    inference(splitLeft,[status(thm)],[c_2297])).

tff(c_276,plain,(
    ! [A_166] :
      ( k1_xboole_0 = A_166
      | ~ v1_xboole_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_381])).

tff(c_396,plain,(
    ! [A_166] :
      ( A_166 = '#skF_9'
      | ~ v1_xboole_0(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_276])).

tff(c_2659,plain,(
    k4_xboole_0('#skF_22','#skF_21') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2643,c_396])).

tff(c_10,plain,(
    ! [B_10,A_9] : k5_xboole_0(B_10,A_9) = k5_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2664,plain,(
    k4_xboole_0('#skF_21','#skF_22') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2659,c_264])).

tff(c_6254,plain,(
    ! [A_496,B_497] : k2_xboole_0(k4_xboole_0(A_496,B_497),k4_xboole_0(B_497,A_496)) = k5_xboole_0(A_496,B_497) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6377,plain,(
    k2_xboole_0('#skF_9',k4_xboole_0('#skF_22','#skF_21')) = k5_xboole_0('#skF_21','#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_2664,c_6254])).

tff(c_6412,plain,(
    k5_xboole_0('#skF_22','#skF_21') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2659,c_10,c_6377])).

tff(c_6707,plain,(
    ! [A_503,C_504,B_505] :
      ( r2_hidden(A_503,C_504)
      | ~ r2_hidden(A_503,B_505)
      | r2_hidden(A_503,k5_xboole_0(B_505,C_504)) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_6734,plain,(
    ! [A_503] :
      ( r2_hidden(A_503,'#skF_21')
      | ~ r2_hidden(A_503,'#skF_22')
      | r2_hidden(A_503,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6412,c_6707])).

tff(c_6748,plain,(
    ! [A_503] :
      ( r2_hidden(A_503,'#skF_21')
      | ~ r2_hidden(A_503,'#skF_22') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2226,c_6734])).

tff(c_12342,plain,(
    ! [A_590,B_591] :
      ( r2_hidden('#skF_11'(A_590,B_591),B_591)
      | ~ r2_hidden('#skF_12'(A_590,B_591),B_591)
      | B_591 = A_590 ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_7024,plain,(
    ! [D_516,A_517,B_518] :
      ( r2_hidden(D_516,k4_xboole_0(A_517,B_518))
      | r2_hidden(D_516,B_518)
      | ~ r2_hidden(D_516,A_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7054,plain,(
    ! [D_516] :
      ( r2_hidden(D_516,'#skF_9')
      | r2_hidden(D_516,'#skF_22')
      | ~ r2_hidden(D_516,'#skF_21') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2664,c_7024])).

tff(c_7073,plain,(
    ! [D_516] :
      ( r2_hidden(D_516,'#skF_22')
      | ~ r2_hidden(D_516,'#skF_21') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2226,c_7054])).

tff(c_12515,plain,(
    ! [A_594] :
      ( r2_hidden('#skF_11'(A_594,'#skF_21'),'#skF_22')
      | ~ r2_hidden('#skF_12'(A_594,'#skF_21'),'#skF_21')
      | A_594 = '#skF_21' ) ),
    inference(resolution,[status(thm)],[c_12342,c_7073])).

tff(c_130,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden('#skF_11'(A_56,B_57),A_56)
      | ~ r2_hidden('#skF_12'(A_56,B_57),B_57)
      | B_57 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_12522,plain,
    ( ~ r2_hidden('#skF_12'('#skF_22','#skF_21'),'#skF_21')
    | '#skF_21' = '#skF_22' ),
    inference(resolution,[status(thm)],[c_12515,c_130])).

tff(c_12537,plain,(
    ~ r2_hidden('#skF_12'('#skF_22','#skF_21'),'#skF_21') ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_262,c_12522])).

tff(c_12545,plain,(
    ~ r2_hidden('#skF_12'('#skF_22','#skF_21'),'#skF_22') ),
    inference(resolution,[status(thm)],[c_6748,c_12537])).

tff(c_12629,plain,(
    ! [A_597,B_598] :
      ( r2_hidden('#skF_11'(A_597,B_598),B_598)
      | r2_hidden('#skF_12'(A_597,B_598),A_597)
      | B_598 = A_597 ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_12865,plain,(
    ! [A_601] :
      ( r2_hidden('#skF_11'(A_601,'#skF_21'),'#skF_22')
      | r2_hidden('#skF_12'(A_601,'#skF_21'),A_601)
      | A_601 = '#skF_21' ) ),
    inference(resolution,[status(thm)],[c_12629,c_7073])).

tff(c_134,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden('#skF_11'(A_56,B_57),A_56)
      | r2_hidden('#skF_12'(A_56,B_57),A_56)
      | B_57 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_12869,plain,
    ( r2_hidden('#skF_12'('#skF_22','#skF_21'),'#skF_22')
    | '#skF_21' = '#skF_22' ),
    inference(resolution,[status(thm)],[c_12865,c_134])).

tff(c_12941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_12545,c_262,c_12545,c_12869])).

tff(c_12943,plain,(
    ~ v1_xboole_0(k4_xboole_0('#skF_22','#skF_21')) ),
    inference(splitRight,[status(thm)],[c_2297])).

tff(c_12947,plain,(
    k4_xboole_0('#skF_22','#skF_21') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_1803,c_12943])).

tff(c_2296,plain,
    ( r2_hidden('#skF_18'(k4_xboole_0('#skF_22','#skF_21')),'#skF_21')
    | k4_xboole_0('#skF_22','#skF_21') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_968,c_2287])).

tff(c_13329,plain,(
    r2_hidden('#skF_18'(k4_xboole_0('#skF_22','#skF_21')),'#skF_21') ),
    inference(negUnitSimplification,[status(thm)],[c_12947,c_2296])).

tff(c_21002,plain,(
    ! [D_893,A_894,B_895] :
      ( r2_hidden(D_893,k4_xboole_0(A_894,B_895))
      | r2_hidden(D_893,B_895)
      | ~ r2_hidden(D_893,A_894) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_21102,plain,(
    ! [D_898] :
      ( r2_hidden(D_898,k4_xboole_0('#skF_22','#skF_21'))
      | r2_hidden(D_898,'#skF_22')
      | ~ r2_hidden(D_898,'#skF_21') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_21002])).

tff(c_64,plain,(
    ! [D_37,A_32,B_33] :
      ( r2_hidden(D_37,A_32)
      | ~ r2_hidden(D_37,k4_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_21147,plain,(
    ! [D_899] :
      ( r2_hidden(D_899,'#skF_22')
      | ~ r2_hidden(D_899,'#skF_21') ) ),
    inference(resolution,[status(thm)],[c_21102,c_64])).

tff(c_21193,plain,(
    r2_hidden('#skF_18'(k4_xboole_0('#skF_22','#skF_21')),'#skF_22') ),
    inference(resolution,[status(thm)],[c_13329,c_21147])).

tff(c_21232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2067,c_21193])).

tff(c_21233,plain,(
    k4_xboole_0('#skF_22','#skF_21') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2021])).

tff(c_21236,plain,(
    k4_xboole_0('#skF_21','#skF_22') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21233,c_264])).

tff(c_25172,plain,(
    ! [A_1062,B_1063] : k2_xboole_0(k4_xboole_0(A_1062,B_1063),k4_xboole_0(B_1063,A_1062)) = k5_xboole_0(A_1062,B_1063) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_25285,plain,(
    k2_xboole_0('#skF_9',k4_xboole_0('#skF_22','#skF_21')) = k5_xboole_0('#skF_21','#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_21236,c_25172])).

tff(c_25320,plain,(
    k5_xboole_0('#skF_22','#skF_21') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_21233,c_10,c_25285])).

tff(c_27059,plain,(
    ! [A_1122,C_1123,B_1124] :
      ( r2_hidden(A_1122,C_1123)
      | ~ r2_hidden(A_1122,B_1124)
      | r2_hidden(A_1122,k5_xboole_0(B_1124,C_1123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_27095,plain,(
    ! [A_1122] :
      ( r2_hidden(A_1122,'#skF_21')
      | ~ r2_hidden(A_1122,'#skF_22')
      | r2_hidden(A_1122,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25320,c_27059])).

tff(c_27112,plain,(
    ! [A_1125] :
      ( r2_hidden(A_1125,'#skF_21')
      | ~ r2_hidden(A_1125,'#skF_22') ) ),
    inference(negUnitSimplification,[status(thm)],[c_21286,c_27095])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden('#skF_2'(A_15,B_16),B_16)
      | r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_27382,plain,(
    ! [A_1140] :
      ( r1_tarski(A_1140,'#skF_21')
      | ~ r2_hidden('#skF_2'(A_1140,'#skF_21'),'#skF_22') ) ),
    inference(resolution,[status(thm)],[c_27112,c_20])).

tff(c_27387,plain,(
    r1_tarski('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_22,c_27382])).

tff(c_84,plain,(
    ! [A_42,B_43] :
      ( r2_xboole_0(A_42,B_43)
      | B_43 = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_188,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_17'(A_76,B_77),B_77)
      | ~ r2_xboole_0(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_27616,plain,(
    ! [D_1141,A_1142,B_1143] :
      ( r2_hidden(D_1141,k4_xboole_0(A_1142,B_1143))
      | r2_hidden(D_1141,B_1143)
      | ~ r2_hidden(D_1141,A_1142) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_27649,plain,(
    ! [D_1141] :
      ( r2_hidden(D_1141,'#skF_9')
      | r2_hidden(D_1141,'#skF_22')
      | ~ r2_hidden(D_1141,'#skF_21') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21236,c_27616])).

tff(c_27868,plain,(
    ! [D_1144] :
      ( r2_hidden(D_1144,'#skF_22')
      | ~ r2_hidden(D_1144,'#skF_21') ) ),
    inference(negUnitSimplification,[status(thm)],[c_21286,c_27649])).

tff(c_28431,plain,(
    ! [A_1156] :
      ( r2_hidden('#skF_17'(A_1156,'#skF_21'),'#skF_22')
      | ~ r2_xboole_0(A_1156,'#skF_21') ) ),
    inference(resolution,[status(thm)],[c_188,c_27868])).

tff(c_186,plain,(
    ! [A_76,B_77] :
      ( ~ r2_hidden('#skF_17'(A_76,B_77),A_76)
      | ~ r2_xboole_0(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_28447,plain,(
    ~ r2_xboole_0('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_28431,c_186])).

tff(c_28453,plain,
    ( '#skF_21' = '#skF_22'
    | ~ r1_tarski('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_84,c_28447])).

tff(c_28456,plain,(
    '#skF_21' = '#skF_22' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27387,c_28453])).

tff(c_28458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_28456])).
%------------------------------------------------------------------------------
