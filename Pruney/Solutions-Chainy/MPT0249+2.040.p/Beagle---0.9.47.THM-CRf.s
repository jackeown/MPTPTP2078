%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:29 EST 2020

% Result     : Theorem 16.26s
% Output     : CNFRefutation 16.52s
% Verified   : 
% Statistics : Number of formulae       :  298 (4226 expanded)
%              Number of leaves         :   35 (1398 expanded)
%              Depth                    :   19
%              Number of atoms          :  449 (8875 expanded)
%              Number of equality atoms :  239 (5744 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_5 > #skF_3

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_89,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_80,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_97,plain,(
    ! [A_56,B_57] : r1_tarski(A_56,k2_xboole_0(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_100,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_97])).

tff(c_318,plain,(
    ! [B_99,A_100] :
      ( k1_tarski(B_99) = A_100
      | k1_xboole_0 = A_100
      | ~ r1_tarski(A_100,k1_tarski(B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_328,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_100,c_318])).

tff(c_337,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_328])).

tff(c_64,plain,(
    ! [A_48,B_49] :
      ( r2_hidden(A_48,B_49)
      | ~ r1_tarski(k1_tarski(A_48),B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_368,plain,(
    ! [B_49] :
      ( r2_hidden('#skF_6',B_49)
      | ~ r1_tarski('#skF_7',B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_64])).

tff(c_72,plain,(
    ! [B_51] : r1_tarski(k1_xboole_0,k1_tarski(B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_138,plain,(
    ! [A_72,B_73] :
      ( k2_xboole_0(A_72,B_73) = B_73
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_154,plain,(
    ! [B_51] : k2_xboole_0(k1_xboole_0,k1_tarski(B_51)) = k1_tarski(B_51) ),
    inference(resolution,[status(thm)],[c_72,c_138])).

tff(c_302,plain,(
    ! [D_96,A_97,B_98] :
      ( ~ r2_hidden(D_96,A_97)
      | r2_hidden(D_96,k2_xboole_0(A_97,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_712,plain,(
    ! [D_124,B_125] :
      ( ~ r2_hidden(D_124,k1_xboole_0)
      | r2_hidden(D_124,k1_tarski(B_125)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_302])).

tff(c_66,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_tarski(A_48),B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_359,plain,(
    ! [B_49] :
      ( r1_tarski('#skF_7',B_49)
      | ~ r2_hidden('#skF_6',B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_66])).

tff(c_719,plain,(
    ! [B_125] :
      ( r1_tarski('#skF_7',k1_tarski(B_125))
      | ~ r2_hidden('#skF_6',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_712,c_359])).

tff(c_741,plain,(
    ~ r2_hidden('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_719])).

tff(c_745,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_368,c_741])).

tff(c_246,plain,(
    ! [D_90,B_91,A_92] :
      ( ~ r2_hidden(D_90,B_91)
      | r2_hidden(D_90,k2_xboole_0(A_92,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_258,plain,(
    ! [D_90] :
      ( ~ r2_hidden(D_90,'#skF_8')
      | r2_hidden(D_90,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_246])).

tff(c_340,plain,(
    ! [D_90] :
      ( ~ r2_hidden(D_90,'#skF_8')
      | r2_hidden(D_90,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_258])).

tff(c_68,plain,(
    ! [B_51,A_50] :
      ( k1_tarski(B_51) = A_50
      | k1_xboole_0 = A_50
      | ~ r1_tarski(A_50,k1_tarski(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_347,plain,(
    ! [A_50] :
      ( k1_tarski('#skF_6') = A_50
      | k1_xboole_0 = A_50
      | ~ r1_tarski(A_50,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_68])).

tff(c_721,plain,(
    ! [A_126] :
      ( A_126 = '#skF_7'
      | k1_xboole_0 = A_126
      | ~ r1_tarski(A_126,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_347])).

tff(c_26910,plain,(
    ! [A_112612] :
      ( k1_tarski(A_112612) = '#skF_7'
      | k1_tarski(A_112612) = k1_xboole_0
      | ~ r2_hidden(A_112612,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_721])).

tff(c_46853,plain,(
    ! [D_201670] :
      ( k1_tarski(D_201670) = '#skF_7'
      | k1_tarski(D_201670) = k1_xboole_0
      | ~ r2_hidden(D_201670,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_340,c_26910])).

tff(c_46865,plain,
    ( k1_tarski('#skF_3'('#skF_8')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_8')) = k1_xboole_0
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_46853])).

tff(c_46874,plain,
    ( k1_tarski('#skF_3'('#skF_8')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_8')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_46865])).

tff(c_46875,plain,(
    k1_tarski('#skF_3'('#skF_8')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46874])).

tff(c_70,plain,(
    ! [B_51] : r1_tarski(k1_tarski(B_51),k1_tarski(B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_185,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(A_76,B_77)
      | ~ r1_tarski(k1_tarski(A_76),B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_198,plain,(
    ! [B_51] : r2_hidden(B_51,k1_tarski(B_51)) ),
    inference(resolution,[status(thm)],[c_70,c_185])).

tff(c_46914,plain,(
    r2_hidden('#skF_3'('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46875,c_198])).

tff(c_371,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_7') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_154])).

tff(c_392,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_371])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_437,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,k1_xboole_0)
      | r2_hidden(D_6,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_6])).

tff(c_47043,plain,(
    r2_hidden('#skF_3'('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_46914,c_437])).

tff(c_217,plain,(
    ! [A_84,B_85] : k1_enumset1(A_84,A_84,B_85) = k2_tarski(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_229,plain,(
    ! [B_85,A_84] : r2_hidden(B_85,k2_tarski(A_84,B_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_28])).

tff(c_208,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k1_tarski(A_82),B_83)
      | ~ r2_hidden(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26123,plain,(
    ! [A_112582,B_112583] :
      ( k2_xboole_0(k1_tarski(A_112582),B_112583) = B_112583
      | ~ r2_hidden(A_112582,B_112583) ) ),
    inference(resolution,[status(thm)],[c_208,c_22])).

tff(c_26193,plain,(
    ! [B_112584] :
      ( k2_xboole_0('#skF_7',B_112584) = B_112584
      | ~ r2_hidden('#skF_6',B_112584) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_26123])).

tff(c_26392,plain,(
    ! [A_112594] : k2_xboole_0('#skF_7',k2_tarski(A_112594,'#skF_6')) = k2_tarski(A_112594,'#skF_6') ),
    inference(resolution,[status(thm)],[c_229,c_26193])).

tff(c_26406,plain,(
    ! [D_6,A_112594] :
      ( ~ r2_hidden(D_6,'#skF_7')
      | r2_hidden(D_6,k2_tarski(A_112594,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26392,c_6])).

tff(c_216,plain,(
    ! [A_82,B_83] :
      ( k2_xboole_0(k1_tarski(A_82),B_83) = B_83
      | ~ r2_hidden(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_208,c_22])).

tff(c_47745,plain,(
    ! [B_201699] :
      ( k2_xboole_0(k1_xboole_0,B_201699) = B_201699
      | ~ r2_hidden('#skF_3'('#skF_8'),B_201699) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46875,c_216])).

tff(c_47781,plain,(
    ! [A_112594] :
      ( k2_xboole_0(k1_xboole_0,k2_tarski(A_112594,'#skF_6')) = k2_tarski(A_112594,'#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26406,c_47745])).

tff(c_63632,plain,(
    ! [A_286300] : k2_xboole_0(k1_xboole_0,k2_tarski(A_286300,'#skF_6')) = k2_tarski(A_286300,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47043,c_47781])).

tff(c_24,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_199,plain,(
    ! [A_76,B_12] : r2_hidden(A_76,k2_xboole_0(k1_tarski(A_76),B_12)) ),
    inference(resolution,[status(thm)],[c_24,c_185])).

tff(c_46911,plain,(
    ! [B_12] : r2_hidden('#skF_3'('#skF_8'),k2_xboole_0(k1_xboole_0,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46875,c_199])).

tff(c_63637,plain,(
    ! [A_286300] : r2_hidden('#skF_3'('#skF_8'),k2_tarski(A_286300,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_63632,c_46911])).

tff(c_52,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_752,plain,(
    ! [E_128,C_129,B_130,A_131] :
      ( E_128 = C_129
      | E_128 = B_130
      | E_128 = A_131
      | ~ r2_hidden(E_128,k1_enumset1(A_131,B_130,C_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_70391,plain,(
    ! [E_309616,B_309617,A_309618] :
      ( E_309616 = B_309617
      | E_309616 = A_309618
      | E_309616 = A_309618
      | ~ r2_hidden(E_309616,k2_tarski(A_309618,B_309617)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_752])).

tff(c_70480,plain,(
    ! [A_286300] :
      ( '#skF_3'('#skF_8') = '#skF_6'
      | A_286300 = '#skF_3'('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_63637,c_70391])).

tff(c_70558,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_70480])).

tff(c_70587,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70558,c_46914])).

tff(c_70607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_741,c_70587])).

tff(c_70877,plain,(
    '#skF_3'('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70480])).

tff(c_50,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_106,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_115,plain,(
    ! [A_20] : k3_tarski(k1_tarski(A_20)) = k2_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_106])).

tff(c_377,plain,(
    k2_xboole_0('#skF_6','#skF_6') = k3_tarski('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_115])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_746,plain,(
    ! [D_127] :
      ( ~ r2_hidden(D_127,'#skF_6')
      | r2_hidden(D_127,k3_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_4])).

tff(c_751,plain,
    ( r1_tarski('#skF_7',k3_tarski('#skF_7'))
    | ~ r2_hidden('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_746,c_359])).

tff(c_781,plain,(
    ~ r2_hidden('#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_751])).

tff(c_857,plain,(
    ! [A_134,B_135] :
      ( k2_xboole_0(k1_tarski(A_134),B_135) = B_135
      | ~ r2_hidden(A_134,B_135) ) ),
    inference(resolution,[status(thm)],[c_208,c_22])).

tff(c_927,plain,(
    ! [B_136] :
      ( k2_xboole_0('#skF_7',B_136) = B_136
      | ~ r2_hidden('#skF_6',B_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_857])).

tff(c_9809,plain,(
    ! [A_27352,B_27353] : k2_xboole_0('#skF_7',k1_enumset1(A_27352,B_27353,'#skF_6')) = k1_enumset1(A_27352,B_27353,'#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_927])).

tff(c_9864,plain,(
    ! [D_27354,A_27355,B_27356] :
      ( ~ r2_hidden(D_27354,'#skF_7')
      | r2_hidden(D_27354,k1_enumset1(A_27355,B_27356,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9809,c_6])).

tff(c_26,plain,(
    ! [E_19,C_15,B_14,A_13] :
      ( E_19 = C_15
      | E_19 = B_14
      | E_19 = A_13
      | ~ r2_hidden(E_19,k1_enumset1(A_13,B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_9959,plain,(
    ! [D_27359,B_27360,A_27361] :
      ( D_27359 = '#skF_6'
      | D_27359 = B_27360
      | D_27359 = A_27361
      | ~ r2_hidden(D_27359,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9864,c_26])).

tff(c_9998,plain,(
    ! [B_27360,A_27361] :
      ( '#skF_3'('#skF_7') = '#skF_6'
      | B_27360 = '#skF_3'('#skF_7')
      | A_27361 = '#skF_3'('#skF_7')
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_20,c_9959])).

tff(c_10022,plain,(
    ! [B_27360,A_27361] :
      ( '#skF_3'('#skF_7') = '#skF_6'
      | B_27360 = '#skF_3'('#skF_7')
      | A_27361 = '#skF_3'('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9998])).

tff(c_11838,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10022])).

tff(c_495,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_6')
      | r2_hidden(D_6,k3_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_4])).

tff(c_1557,plain,(
    ! [A_166] :
      ( k1_tarski(A_166) = '#skF_7'
      | k1_tarski(A_166) = k1_xboole_0
      | ~ r2_hidden(A_166,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_721])).

tff(c_1571,plain,
    ( k1_tarski('#skF_3'('#skF_7')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_7')) = k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_20,c_1557])).

tff(c_1582,plain,
    ( k1_tarski('#skF_3'('#skF_7')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1571])).

tff(c_1583,plain,(
    k1_tarski('#skF_3'('#skF_7')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1582])).

tff(c_1912,plain,(
    ! [B_178] :
      ( r1_tarski(k1_xboole_0,B_178)
      | ~ r2_hidden('#skF_3'('#skF_7'),B_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1583,c_66])).

tff(c_2008,plain,
    ( r1_tarski(k1_xboole_0,k3_tarski('#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_495,c_1912])).

tff(c_2297,plain,(
    ~ r2_hidden('#skF_3'('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2008])).

tff(c_3814,plain,(
    ! [A_250,B_251] : k2_xboole_0('#skF_7',k1_enumset1(A_250,B_251,'#skF_6')) = k1_enumset1(A_250,B_251,'#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_927])).

tff(c_4086,plain,(
    ! [D_260,A_261,B_262] :
      ( ~ r2_hidden(D_260,'#skF_7')
      | r2_hidden(D_260,k1_enumset1(A_261,B_262,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3814,c_6])).

tff(c_4340,plain,(
    ! [D_272,B_273,A_274] :
      ( D_272 = '#skF_6'
      | D_272 = B_273
      | D_272 = A_274
      | ~ r2_hidden(D_272,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4086,c_26])).

tff(c_4379,plain,(
    ! [B_273,A_274] :
      ( '#skF_3'('#skF_7') = '#skF_6'
      | B_273 = '#skF_3'('#skF_7')
      | A_274 = '#skF_3'('#skF_7')
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_20,c_4340])).

tff(c_4403,plain,(
    ! [B_273,A_274] :
      ( '#skF_3'('#skF_7') = '#skF_6'
      | B_273 = '#skF_3'('#skF_7')
      | A_274 = '#skF_3'('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4379])).

tff(c_6455,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4403])).

tff(c_1622,plain,(
    r2_hidden('#skF_3'('#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1583,c_198])).

tff(c_6476,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6455,c_1622])).

tff(c_6487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_741,c_6476])).

tff(c_6488,plain,(
    ! [A_274,B_273] :
      ( A_274 = '#skF_3'('#skF_7')
      | B_273 = '#skF_3'('#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_4403])).

tff(c_6491,plain,(
    ! [B_9256] : B_9256 = '#skF_3'('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_6488])).

tff(c_1637,plain,(
    r1_tarski(k1_tarski('#skF_3'('#skF_7')),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1583,c_70])).

tff(c_1650,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1583,c_1637])).

tff(c_503,plain,(
    ! [D_105,B_106,A_107] :
      ( r2_hidden(D_105,B_106)
      | r2_hidden(D_105,A_107)
      | ~ r2_hidden(D_105,k2_xboole_0(A_107,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3634,plain,(
    ! [D_246] :
      ( r2_hidden(D_246,'#skF_6')
      | r2_hidden(D_246,'#skF_6')
      | ~ r2_hidden(D_246,k3_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_503])).

tff(c_3679,plain,
    ( r2_hidden('#skF_3'(k3_tarski('#skF_7')),'#skF_6')
    | k3_tarski('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_3634])).

tff(c_3680,plain,(
    k3_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3679])).

tff(c_1625,plain,(
    ! [B_49] :
      ( r2_hidden('#skF_3'('#skF_7'),B_49)
      | ~ r1_tarski(k1_xboole_0,B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1583,c_64])).

tff(c_3654,plain,
    ( r2_hidden('#skF_3'('#skF_7'),'#skF_6')
    | ~ r1_tarski(k1_xboole_0,k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1625,c_3634])).

tff(c_3674,plain,(
    ~ r1_tarski(k1_xboole_0,k3_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_2297,c_2297,c_3654])).

tff(c_3681,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3680,c_3674])).

tff(c_3690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_3681])).

tff(c_3691,plain,(
    r2_hidden('#skF_3'(k3_tarski('#skF_7')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_3679])).

tff(c_6548,plain,(
    r2_hidden('#skF_3'('#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6491,c_3691])).

tff(c_7195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2297,c_6548])).

tff(c_7197,plain,(
    ! [A_18275] : A_18275 = '#skF_3'('#skF_7') ),
    inference(splitRight,[status(thm)],[c_6488])).

tff(c_7254,plain,(
    r2_hidden('#skF_3'('#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7197,c_3691])).

tff(c_7901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2297,c_7254])).

tff(c_7903,plain,(
    r2_hidden('#skF_3'('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2008])).

tff(c_11843,plain,(
    r2_hidden('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11838,c_7903])).

tff(c_11865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_781,c_11843])).

tff(c_11867,plain,(
    '#skF_3'('#skF_7') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10022])).

tff(c_11866,plain,(
    ! [A_27361,B_27360] :
      ( A_27361 = '#skF_3'('#skF_7')
      | B_27360 = '#skF_3'('#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_10022])).

tff(c_11869,plain,(
    ! [B_36222] : B_36222 = '#skF_3'('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_11866])).

tff(c_1599,plain,(
    ! [B_83] :
      ( k2_xboole_0(k1_xboole_0,B_83) = B_83
      | ~ r2_hidden('#skF_3'('#skF_7'),B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1583,c_216])).

tff(c_7960,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7903,c_1599])).

tff(c_12133,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_11869,c_7960])).

tff(c_12603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11867,c_12133])).

tff(c_12605,plain,(
    ! [A_45187] : A_45187 = '#skF_3'('#skF_7') ),
    inference(splitRight,[status(thm)],[c_11866])).

tff(c_12869,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_12605,c_7960])).

tff(c_13339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11867,c_12869])).

tff(c_13340,plain,(
    k1_tarski('#skF_3'('#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1582])).

tff(c_1005,plain,(
    ! [D_137,A_138] :
      ( ~ r2_hidden(D_137,A_138)
      | r2_hidden(D_137,k3_tarski(k1_tarski(A_138))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_302])).

tff(c_1027,plain,(
    ! [A_138] :
      ( r1_tarski('#skF_7',k3_tarski(k1_tarski(A_138)))
      | ~ r2_hidden('#skF_6',A_138) ) ),
    inference(resolution,[status(thm)],[c_1005,c_359])).

tff(c_13345,plain,
    ( r1_tarski('#skF_7',k3_tarski('#skF_7'))
    | ~ r2_hidden('#skF_6','#skF_3'('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13340,c_1027])).

tff(c_13748,plain,(
    ~ r2_hidden('#skF_6','#skF_3'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_13345])).

tff(c_13752,plain,(
    ~ r1_tarski('#skF_7','#skF_3'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_368,c_13748])).

tff(c_15268,plain,(
    ! [A_54230,B_54231] : k2_xboole_0('#skF_7',k1_enumset1(A_54230,B_54231,'#skF_6')) = k1_enumset1(A_54230,B_54231,'#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_927])).

tff(c_15628,plain,(
    ! [D_54244,A_54245,B_54246] :
      ( ~ r2_hidden(D_54244,'#skF_7')
      | r2_hidden(D_54244,k1_enumset1(A_54245,B_54246,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15268,c_6])).

tff(c_15958,plain,(
    ! [D_54261,B_54262,A_54263] :
      ( D_54261 = '#skF_6'
      | D_54261 = B_54262
      | D_54261 = A_54263
      | ~ r2_hidden(D_54261,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_15628,c_26])).

tff(c_16133,plain,(
    ! [D_54267,B_54268,A_54269] :
      ( D_54267 = '#skF_6'
      | D_54267 = B_54268
      | D_54267 = A_54269
      | ~ r2_hidden(D_54267,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_340,c_15958])).

tff(c_16166,plain,(
    ! [B_54268,A_54269] :
      ( '#skF_3'('#skF_8') = '#skF_6'
      | B_54268 = '#skF_3'('#skF_8')
      | A_54269 = '#skF_3'('#skF_8')
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_20,c_16133])).

tff(c_16182,plain,(
    ! [B_54268,A_54269] :
      ( '#skF_3'('#skF_8') = '#skF_6'
      | B_54268 = '#skF_3'('#skF_8')
      | A_54269 = '#skF_3'('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_16166])).

tff(c_18058,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_16182])).

tff(c_13970,plain,(
    ! [D_54178] :
      ( k1_tarski(D_54178) = '#skF_7'
      | k1_tarski(D_54178) = k1_xboole_0
      | ~ r2_hidden(D_54178,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_340,c_1557])).

tff(c_13982,plain,
    ( k1_tarski('#skF_3'('#skF_8')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_8')) = k1_xboole_0
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_13970])).

tff(c_13991,plain,
    ( k1_tarski('#skF_3'('#skF_8')) = '#skF_7'
    | k1_tarski('#skF_3'('#skF_8')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_13982])).

tff(c_13992,plain,(
    k1_tarski('#skF_3'('#skF_8')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13991])).

tff(c_14031,plain,(
    r2_hidden('#skF_3'('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13992,c_198])).

tff(c_18079,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18058,c_14031])).

tff(c_18090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_741,c_18079])).

tff(c_18092,plain,(
    '#skF_3'('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_16182])).

tff(c_18091,plain,(
    ! [A_54269,B_54268] :
      ( A_54269 = '#skF_3'('#skF_8')
      | B_54268 = '#skF_3'('#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_16182])).

tff(c_18094,plain,(
    ! [B_61834] : B_61834 = '#skF_3'('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_18091])).

tff(c_30,plain,(
    ! [E_19,A_13,C_15] : r2_hidden(E_19,k1_enumset1(A_13,E_19,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1492,plain,(
    ! [A_162,C_163] : k2_xboole_0('#skF_7',k1_enumset1(A_162,'#skF_6',C_163)) = k1_enumset1(A_162,'#skF_6',C_163) ),
    inference(resolution,[status(thm)],[c_30,c_927])).

tff(c_15423,plain,(
    ! [D_54236,A_54237,C_54238] :
      ( ~ r2_hidden(D_54236,'#skF_7')
      | r2_hidden(D_54236,k1_enumset1(A_54237,'#skF_6',C_54238)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1492,c_6])).

tff(c_15902,plain,(
    ! [D_54258,C_54259,A_54260] :
      ( D_54258 = C_54259
      | D_54258 = '#skF_6'
      | D_54258 = A_54260
      | ~ r2_hidden(D_54258,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_15423,c_26])).

tff(c_15935,plain,(
    ! [C_54259,A_54260] :
      ( C_54259 = '#skF_3'('#skF_7')
      | '#skF_3'('#skF_7') = '#skF_6'
      | A_54260 = '#skF_3'('#skF_7')
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_20,c_15902])).

tff(c_15957,plain,(
    ! [C_54259,A_54260] :
      ( C_54259 = '#skF_3'('#skF_7')
      | '#skF_3'('#skF_7') = '#skF_6'
      | A_54260 = '#skF_3'('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_15935])).

tff(c_16183,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_15957])).

tff(c_18125,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_18094,c_16183])).

tff(c_18680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18092,c_18125])).

tff(c_18682,plain,(
    ! [A_69503] : A_69503 = '#skF_3'('#skF_8') ),
    inference(splitRight,[status(thm)],[c_18091])).

tff(c_18713,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_18682,c_16183])).

tff(c_19268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18092,c_18713])).

tff(c_19269,plain,(
    ! [A_54260,C_54259] :
      ( A_54260 = '#skF_3'('#skF_7')
      | C_54259 = '#skF_3'('#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_15957])).

tff(c_21537,plain,(
    ! [C_85924] : C_85924 = '#skF_3'('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_19269])).

tff(c_13493,plain,(
    ! [B_54156] :
      ( r1_tarski('#skF_7',B_54156)
      | ~ r2_hidden('#skF_3'('#skF_7'),B_54156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13340,c_66])).

tff(c_13591,plain,(
    ! [A_13,C_15] : r1_tarski('#skF_7',k1_enumset1(A_13,'#skF_3'('#skF_7'),C_15)) ),
    inference(resolution,[status(thm)],[c_30,c_13493])).

tff(c_21789,plain,(
    r1_tarski('#skF_7','#skF_3'('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21537,c_13591])).

tff(c_22232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13752,c_21789])).

tff(c_22933,plain,(
    ! [A_103638] : A_103638 = '#skF_3'('#skF_7') ),
    inference(splitRight,[status(thm)],[c_19269])).

tff(c_23185,plain,(
    r1_tarski('#skF_7','#skF_3'('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22933,c_13591])).

tff(c_23628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13752,c_23185])).

tff(c_23629,plain,(
    k1_tarski('#skF_3'('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_13991])).

tff(c_23802,plain,(
    ! [B_112506] :
      ( r1_tarski('#skF_7',B_112506)
      | ~ r2_hidden('#skF_3'('#skF_8'),B_112506) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23629,c_66])).

tff(c_23873,plain,
    ( r1_tarski('#skF_7','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_23802])).

tff(c_23917,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_23873])).

tff(c_23924,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_23917,c_22])).

tff(c_343,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_82])).

tff(c_23925,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23924,c_343])).

tff(c_23927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_23925])).

tff(c_23928,plain,(
    r1_tarski('#skF_7',k3_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_13345])).

tff(c_23933,plain,(
    k2_xboole_0('#skF_7',k3_tarski('#skF_7')) = k3_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_23928,c_22])).

tff(c_362,plain,(
    ! [B_12] : r2_hidden('#skF_6',k2_xboole_0('#skF_7',B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_199])).

tff(c_23995,plain,(
    r2_hidden('#skF_6',k3_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23933,c_362])).

tff(c_25863,plain,(
    ! [D_112571] :
      ( r2_hidden(D_112571,'#skF_6')
      | r2_hidden(D_112571,'#skF_6')
      | ~ r2_hidden(D_112571,k3_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_503])).

tff(c_25905,plain,(
    r2_hidden('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_23995,c_25863])).

tff(c_25937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_781,c_781,c_25905])).

tff(c_25939,plain,(
    r2_hidden('#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_25943,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_25939,c_359])).

tff(c_26840,plain,(
    ! [A_112608,B_112609] : k2_xboole_0('#skF_7',k1_enumset1(A_112608,B_112609,'#skF_6')) = k1_enumset1(A_112608,B_112609,'#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_26193])).

tff(c_48853,plain,(
    ! [D_201729,A_201730,B_201731] :
      ( ~ r2_hidden(D_201729,'#skF_7')
      | r2_hidden(D_201729,k1_enumset1(A_201730,B_201731,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26840,c_6])).

tff(c_53421,plain,(
    ! [D_220703,B_220704,A_220705] :
      ( D_220703 = '#skF_6'
      | D_220703 = B_220704
      | D_220703 = A_220705
      | ~ r2_hidden(D_220703,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48853,c_26])).

tff(c_53485,plain,(
    ! [D_220814,B_220815,A_220816] :
      ( D_220814 = '#skF_6'
      | D_220814 = B_220815
      | D_220814 = A_220816
      | ~ r2_hidden(D_220814,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_340,c_53421])).

tff(c_53518,plain,(
    ! [B_220815,A_220816] :
      ( '#skF_3'('#skF_8') = '#skF_6'
      | B_220815 = '#skF_3'('#skF_8')
      | A_220816 = '#skF_3'('#skF_8')
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_20,c_53485])).

tff(c_53534,plain,(
    ! [B_220815,A_220816] :
      ( '#skF_3'('#skF_8') = '#skF_6'
      | B_220815 = '#skF_3'('#skF_8')
      | A_220816 = '#skF_3'('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_53518])).

tff(c_55515,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_53534])).

tff(c_26305,plain,(
    ! [D_112591,A_112592] :
      ( ~ r2_hidden(D_112591,A_112592)
      | r2_hidden(D_112591,k3_tarski(k1_tarski(A_112592))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_246])).

tff(c_26327,plain,(
    ! [A_112592] :
      ( r1_tarski('#skF_7',k3_tarski(k1_tarski(A_112592)))
      | ~ r2_hidden('#skF_6',A_112592) ) ),
    inference(resolution,[status(thm)],[c_26305,c_359])).

tff(c_46879,plain,
    ( r1_tarski('#skF_7',k3_tarski(k1_xboole_0))
    | ~ r2_hidden('#skF_6','#skF_3'('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46875,c_26327])).

tff(c_48140,plain,(
    ~ r2_hidden('#skF_6','#skF_3'('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_46879])).

tff(c_48144,plain,(
    ~ r1_tarski('#skF_7','#skF_3'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_368,c_48140])).

tff(c_55519,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55515,c_48144])).

tff(c_55543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25943,c_55519])).

tff(c_55545,plain,(
    '#skF_3'('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_53534])).

tff(c_55544,plain,(
    ! [A_220816,B_220815] :
      ( A_220816 = '#skF_3'('#skF_8')
      | B_220815 = '#skF_3'('#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_53534])).

tff(c_55547,plain,(
    ! [B_229947] : B_229947 = '#skF_3'('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_55544])).

tff(c_53460,plain,(
    ! [B_220704,A_220705] :
      ( '#skF_3'('#skF_7') = '#skF_6'
      | B_220704 = '#skF_3'('#skF_7')
      | A_220705 = '#skF_3'('#skF_7')
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_20,c_53421])).

tff(c_53484,plain,(
    ! [B_220704,A_220705] :
      ( '#skF_3'('#skF_7') = '#skF_6'
      | B_220704 = '#skF_3'('#skF_7')
      | A_220705 = '#skF_3'('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_53460])).

tff(c_53535,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_53484])).

tff(c_55585,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_55547,c_53535])).

tff(c_56215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55545,c_55585])).

tff(c_56217,plain,(
    ! [A_238642] : A_238642 = '#skF_3'('#skF_8') ),
    inference(splitRight,[status(thm)],[c_55544])).

tff(c_56255,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_56217,c_53535])).

tff(c_56885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55545,c_56255])).

tff(c_56887,plain,(
    '#skF_3'('#skF_7') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_53484])).

tff(c_56886,plain,(
    ! [A_220705,B_220704] :
      ( A_220705 = '#skF_3'('#skF_7')
      | B_220704 = '#skF_3'('#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_53484])).

tff(c_59187,plain,(
    ! [B_257169] : B_257169 = '#skF_3'('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56886])).

tff(c_25947,plain,(
    k2_xboole_0('#skF_7','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_25943,c_22])).

tff(c_25960,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_7')
      | r2_hidden(D_6,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25947,c_6])).

tff(c_47057,plain,(
    r2_hidden('#skF_3'('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_47043,c_25960])).

tff(c_47270,plain,(
    ! [B_201684] :
      ( r1_tarski(k1_xboole_0,B_201684)
      | ~ r2_hidden('#skF_3'('#skF_8'),B_201684) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46875,c_66])).

tff(c_47370,plain,(
    r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(resolution,[status(thm)],[c_47057,c_47270])).

tff(c_47416,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_47370,c_22])).

tff(c_59392,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_59187,c_47416])).

tff(c_59976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56887,c_59392])).

tff(c_59979,plain,(
    ! [A_266998] : A_266998 = '#skF_3'('#skF_7') ),
    inference(splitRight,[status(thm)],[c_56886])).

tff(c_60184,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_59979,c_47416])).

tff(c_60768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56887,c_60184])).

tff(c_60770,plain,(
    r2_hidden('#skF_6','#skF_3'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_46879])).

tff(c_60782,plain,(
    r1_tarski('#skF_7','#skF_3'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_60770,c_359])).

tff(c_70878,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70877,c_60782])).

tff(c_71452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_745,c_70878])).

tff(c_71453,plain,(
    k1_tarski('#skF_3'('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_46874])).

tff(c_71777,plain,(
    ! [B_319838] :
      ( r1_tarski('#skF_7',B_319838)
      | ~ r2_hidden('#skF_3'('#skF_8'),B_319838) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71453,c_66])).

tff(c_71862,plain,
    ( r1_tarski('#skF_7','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_71777])).

tff(c_71918,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_71862])).

tff(c_71925,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_71918,c_22])).

tff(c_71926,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71925,c_343])).

tff(c_71928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_71926])).

tff(c_71944,plain,(
    ! [B_319839] : r1_tarski('#skF_7',k1_tarski(B_319839)) ),
    inference(splitRight,[status(thm)],[c_719])).

tff(c_71947,plain,(
    ! [B_319839] :
      ( k1_tarski(B_319839) = '#skF_7'
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_71944,c_68])).

tff(c_71955,plain,(
    ! [B_319839] : k1_tarski(B_319839) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_71947])).

tff(c_259,plain,(
    ! [B_93] : k2_xboole_0(k1_tarski(B_93),k1_tarski(B_93)) = k1_tarski(B_93) ),
    inference(resolution,[status(thm)],[c_70,c_138])).

tff(c_271,plain,(
    ! [B_93] : k3_tarski(k1_tarski(k1_tarski(B_93))) = k1_tarski(B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_115])).

tff(c_350,plain,(
    k3_tarski(k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_271])).

tff(c_389,plain,(
    k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_350])).

tff(c_71989,plain,(
    k3_tarski('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71955,c_389])).

tff(c_118,plain,(
    ! [A_71] : k3_tarski(k1_tarski(A_71)) = k2_xboole_0(A_71,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_106])).

tff(c_127,plain,(
    ! [A_71] : r1_tarski(A_71,k3_tarski(k1_tarski(A_71))) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_24])).

tff(c_71999,plain,(
    ! [A_71] : r1_tarski(A_71,k3_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71955,c_127])).

tff(c_72109,plain,(
    ! [A_71] : r1_tarski(A_71,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71989,c_71999])).

tff(c_388,plain,(
    ! [A_50] :
      ( A_50 = '#skF_7'
      | k1_xboole_0 = A_50
      | ~ r1_tarski(A_50,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_347])).

tff(c_72153,plain,
    ( '#skF_7' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72109,c_388])).

tff(c_72112,plain,(
    ! [A_50] :
      ( A_50 = '#skF_7'
      | k1_xboole_0 = A_50 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72109,c_388])).

tff(c_72154,plain,(
    ! [A_50] :
      ( A_50 = '#skF_7'
      | A_50 = '#skF_8'
      | '#skF_7' = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72153,c_72112])).

tff(c_72378,plain,(
    ! [A_322393] :
      ( A_322393 = '#skF_7'
      | A_322393 = '#skF_8' ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_72154])).

tff(c_72625,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_72378,c_78])).

tff(c_72721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_72625])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.26/8.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.26/8.06  
% 16.26/8.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.52/8.07  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_5 > #skF_3
% 16.52/8.07  
% 16.52/8.07  %Foreground sorts:
% 16.52/8.07  
% 16.52/8.07  
% 16.52/8.07  %Background operators:
% 16.52/8.07  
% 16.52/8.07  
% 16.52/8.07  %Foreground operators:
% 16.52/8.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.52/8.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.52/8.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.52/8.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.52/8.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.52/8.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.52/8.07  tff('#skF_7', type, '#skF_7': $i).
% 16.52/8.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.52/8.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.52/8.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.52/8.07  tff('#skF_6', type, '#skF_6': $i).
% 16.52/8.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.52/8.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.52/8.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.52/8.07  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 16.52/8.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 16.52/8.07  tff('#skF_8', type, '#skF_8': $i).
% 16.52/8.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.52/8.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.52/8.07  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 16.52/8.07  tff('#skF_3', type, '#skF_3': $i > $i).
% 16.52/8.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.52/8.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.52/8.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 16.52/8.07  
% 16.52/8.10  tff(f_102, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 16.52/8.10  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 16.52/8.10  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 16.52/8.10  tff(f_87, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 16.52/8.10  tff(f_81, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 16.52/8.10  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 16.52/8.10  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 16.52/8.10  tff(f_67, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 16.52/8.10  tff(f_63, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 16.52/8.10  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 16.52/8.10  tff(f_89, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 16.52/8.10  tff(c_76, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.52/8.10  tff(c_80, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.52/8.10  tff(c_78, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.52/8.10  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.52/8.10  tff(c_82, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.52/8.10  tff(c_97, plain, (![A_56, B_57]: (r1_tarski(A_56, k2_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 16.52/8.10  tff(c_100, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_97])).
% 16.52/8.10  tff(c_318, plain, (![B_99, A_100]: (k1_tarski(B_99)=A_100 | k1_xboole_0=A_100 | ~r1_tarski(A_100, k1_tarski(B_99)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.52/8.10  tff(c_328, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_100, c_318])).
% 16.52/8.10  tff(c_337, plain, (k1_tarski('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_78, c_328])).
% 16.52/8.10  tff(c_64, plain, (![A_48, B_49]: (r2_hidden(A_48, B_49) | ~r1_tarski(k1_tarski(A_48), B_49))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.52/8.10  tff(c_368, plain, (![B_49]: (r2_hidden('#skF_6', B_49) | ~r1_tarski('#skF_7', B_49))), inference(superposition, [status(thm), theory('equality')], [c_337, c_64])).
% 16.52/8.10  tff(c_72, plain, (![B_51]: (r1_tarski(k1_xboole_0, k1_tarski(B_51)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.52/8.10  tff(c_138, plain, (![A_72, B_73]: (k2_xboole_0(A_72, B_73)=B_73 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.52/8.10  tff(c_154, plain, (![B_51]: (k2_xboole_0(k1_xboole_0, k1_tarski(B_51))=k1_tarski(B_51))), inference(resolution, [status(thm)], [c_72, c_138])).
% 16.52/8.10  tff(c_302, plain, (![D_96, A_97, B_98]: (~r2_hidden(D_96, A_97) | r2_hidden(D_96, k2_xboole_0(A_97, B_98)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.52/8.10  tff(c_712, plain, (![D_124, B_125]: (~r2_hidden(D_124, k1_xboole_0) | r2_hidden(D_124, k1_tarski(B_125)))), inference(superposition, [status(thm), theory('equality')], [c_154, c_302])).
% 16.52/8.10  tff(c_66, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), B_49) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.52/8.10  tff(c_359, plain, (![B_49]: (r1_tarski('#skF_7', B_49) | ~r2_hidden('#skF_6', B_49))), inference(superposition, [status(thm), theory('equality')], [c_337, c_66])).
% 16.52/8.10  tff(c_719, plain, (![B_125]: (r1_tarski('#skF_7', k1_tarski(B_125)) | ~r2_hidden('#skF_6', k1_xboole_0))), inference(resolution, [status(thm)], [c_712, c_359])).
% 16.52/8.10  tff(c_741, plain, (~r2_hidden('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_719])).
% 16.52/8.10  tff(c_745, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_368, c_741])).
% 16.52/8.10  tff(c_246, plain, (![D_90, B_91, A_92]: (~r2_hidden(D_90, B_91) | r2_hidden(D_90, k2_xboole_0(A_92, B_91)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.52/8.10  tff(c_258, plain, (![D_90]: (~r2_hidden(D_90, '#skF_8') | r2_hidden(D_90, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_82, c_246])).
% 16.52/8.10  tff(c_340, plain, (![D_90]: (~r2_hidden(D_90, '#skF_8') | r2_hidden(D_90, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_258])).
% 16.52/8.10  tff(c_68, plain, (![B_51, A_50]: (k1_tarski(B_51)=A_50 | k1_xboole_0=A_50 | ~r1_tarski(A_50, k1_tarski(B_51)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.52/8.10  tff(c_347, plain, (![A_50]: (k1_tarski('#skF_6')=A_50 | k1_xboole_0=A_50 | ~r1_tarski(A_50, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_337, c_68])).
% 16.52/8.10  tff(c_721, plain, (![A_126]: (A_126='#skF_7' | k1_xboole_0=A_126 | ~r1_tarski(A_126, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_347])).
% 16.52/8.10  tff(c_26910, plain, (![A_112612]: (k1_tarski(A_112612)='#skF_7' | k1_tarski(A_112612)=k1_xboole_0 | ~r2_hidden(A_112612, '#skF_7'))), inference(resolution, [status(thm)], [c_66, c_721])).
% 16.52/8.10  tff(c_46853, plain, (![D_201670]: (k1_tarski(D_201670)='#skF_7' | k1_tarski(D_201670)=k1_xboole_0 | ~r2_hidden(D_201670, '#skF_8'))), inference(resolution, [status(thm)], [c_340, c_26910])).
% 16.52/8.10  tff(c_46865, plain, (k1_tarski('#skF_3'('#skF_8'))='#skF_7' | k1_tarski('#skF_3'('#skF_8'))=k1_xboole_0 | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_46853])).
% 16.52/8.10  tff(c_46874, plain, (k1_tarski('#skF_3'('#skF_8'))='#skF_7' | k1_tarski('#skF_3'('#skF_8'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_76, c_46865])).
% 16.52/8.10  tff(c_46875, plain, (k1_tarski('#skF_3'('#skF_8'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46874])).
% 16.52/8.10  tff(c_70, plain, (![B_51]: (r1_tarski(k1_tarski(B_51), k1_tarski(B_51)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.52/8.10  tff(c_185, plain, (![A_76, B_77]: (r2_hidden(A_76, B_77) | ~r1_tarski(k1_tarski(A_76), B_77))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.52/8.10  tff(c_198, plain, (![B_51]: (r2_hidden(B_51, k1_tarski(B_51)))), inference(resolution, [status(thm)], [c_70, c_185])).
% 16.52/8.10  tff(c_46914, plain, (r2_hidden('#skF_3'('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46875, c_198])).
% 16.52/8.10  tff(c_371, plain, (k2_xboole_0(k1_xboole_0, '#skF_7')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_337, c_154])).
% 16.52/8.10  tff(c_392, plain, (k2_xboole_0(k1_xboole_0, '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_337, c_371])).
% 16.52/8.10  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.52/8.10  tff(c_437, plain, (![D_6]: (~r2_hidden(D_6, k1_xboole_0) | r2_hidden(D_6, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_392, c_6])).
% 16.52/8.10  tff(c_47043, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_46914, c_437])).
% 16.52/8.10  tff(c_217, plain, (![A_84, B_85]: (k1_enumset1(A_84, A_84, B_85)=k2_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.52/8.10  tff(c_28, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.52/8.10  tff(c_229, plain, (![B_85, A_84]: (r2_hidden(B_85, k2_tarski(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_28])).
% 16.52/8.10  tff(c_208, plain, (![A_82, B_83]: (r1_tarski(k1_tarski(A_82), B_83) | ~r2_hidden(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.52/8.10  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.52/8.10  tff(c_26123, plain, (![A_112582, B_112583]: (k2_xboole_0(k1_tarski(A_112582), B_112583)=B_112583 | ~r2_hidden(A_112582, B_112583))), inference(resolution, [status(thm)], [c_208, c_22])).
% 16.52/8.10  tff(c_26193, plain, (![B_112584]: (k2_xboole_0('#skF_7', B_112584)=B_112584 | ~r2_hidden('#skF_6', B_112584))), inference(superposition, [status(thm), theory('equality')], [c_337, c_26123])).
% 16.52/8.10  tff(c_26392, plain, (![A_112594]: (k2_xboole_0('#skF_7', k2_tarski(A_112594, '#skF_6'))=k2_tarski(A_112594, '#skF_6'))), inference(resolution, [status(thm)], [c_229, c_26193])).
% 16.52/8.10  tff(c_26406, plain, (![D_6, A_112594]: (~r2_hidden(D_6, '#skF_7') | r2_hidden(D_6, k2_tarski(A_112594, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_26392, c_6])).
% 16.52/8.10  tff(c_216, plain, (![A_82, B_83]: (k2_xboole_0(k1_tarski(A_82), B_83)=B_83 | ~r2_hidden(A_82, B_83))), inference(resolution, [status(thm)], [c_208, c_22])).
% 16.52/8.10  tff(c_47745, plain, (![B_201699]: (k2_xboole_0(k1_xboole_0, B_201699)=B_201699 | ~r2_hidden('#skF_3'('#skF_8'), B_201699))), inference(superposition, [status(thm), theory('equality')], [c_46875, c_216])).
% 16.52/8.10  tff(c_47781, plain, (![A_112594]: (k2_xboole_0(k1_xboole_0, k2_tarski(A_112594, '#skF_6'))=k2_tarski(A_112594, '#skF_6') | ~r2_hidden('#skF_3'('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_26406, c_47745])).
% 16.52/8.10  tff(c_63632, plain, (![A_286300]: (k2_xboole_0(k1_xboole_0, k2_tarski(A_286300, '#skF_6'))=k2_tarski(A_286300, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_47043, c_47781])).
% 16.52/8.10  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 16.52/8.10  tff(c_199, plain, (![A_76, B_12]: (r2_hidden(A_76, k2_xboole_0(k1_tarski(A_76), B_12)))), inference(resolution, [status(thm)], [c_24, c_185])).
% 16.52/8.10  tff(c_46911, plain, (![B_12]: (r2_hidden('#skF_3'('#skF_8'), k2_xboole_0(k1_xboole_0, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_46875, c_199])).
% 16.52/8.10  tff(c_63637, plain, (![A_286300]: (r2_hidden('#skF_3'('#skF_8'), k2_tarski(A_286300, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_63632, c_46911])).
% 16.52/8.10  tff(c_52, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.52/8.10  tff(c_752, plain, (![E_128, C_129, B_130, A_131]: (E_128=C_129 | E_128=B_130 | E_128=A_131 | ~r2_hidden(E_128, k1_enumset1(A_131, B_130, C_129)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.52/8.10  tff(c_70391, plain, (![E_309616, B_309617, A_309618]: (E_309616=B_309617 | E_309616=A_309618 | E_309616=A_309618 | ~r2_hidden(E_309616, k2_tarski(A_309618, B_309617)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_752])).
% 16.52/8.10  tff(c_70480, plain, (![A_286300]: ('#skF_3'('#skF_8')='#skF_6' | A_286300='#skF_3'('#skF_8'))), inference(resolution, [status(thm)], [c_63637, c_70391])).
% 16.52/8.10  tff(c_70558, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_70480])).
% 16.52/8.10  tff(c_70587, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70558, c_46914])).
% 16.52/8.10  tff(c_70607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_741, c_70587])).
% 16.52/8.10  tff(c_70877, plain, ('#skF_3'('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_70480])).
% 16.52/8.10  tff(c_50, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.52/8.10  tff(c_106, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_89])).
% 16.52/8.10  tff(c_115, plain, (![A_20]: (k3_tarski(k1_tarski(A_20))=k2_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_50, c_106])).
% 16.52/8.10  tff(c_377, plain, (k2_xboole_0('#skF_6', '#skF_6')=k3_tarski('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_337, c_115])).
% 16.52/8.10  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.52/8.10  tff(c_746, plain, (![D_127]: (~r2_hidden(D_127, '#skF_6') | r2_hidden(D_127, k3_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_377, c_4])).
% 16.52/8.10  tff(c_751, plain, (r1_tarski('#skF_7', k3_tarski('#skF_7')) | ~r2_hidden('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_746, c_359])).
% 16.52/8.10  tff(c_781, plain, (~r2_hidden('#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_751])).
% 16.52/8.10  tff(c_857, plain, (![A_134, B_135]: (k2_xboole_0(k1_tarski(A_134), B_135)=B_135 | ~r2_hidden(A_134, B_135))), inference(resolution, [status(thm)], [c_208, c_22])).
% 16.52/8.10  tff(c_927, plain, (![B_136]: (k2_xboole_0('#skF_7', B_136)=B_136 | ~r2_hidden('#skF_6', B_136))), inference(superposition, [status(thm), theory('equality')], [c_337, c_857])).
% 16.52/8.10  tff(c_9809, plain, (![A_27352, B_27353]: (k2_xboole_0('#skF_7', k1_enumset1(A_27352, B_27353, '#skF_6'))=k1_enumset1(A_27352, B_27353, '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_927])).
% 16.52/8.10  tff(c_9864, plain, (![D_27354, A_27355, B_27356]: (~r2_hidden(D_27354, '#skF_7') | r2_hidden(D_27354, k1_enumset1(A_27355, B_27356, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_9809, c_6])).
% 16.52/8.10  tff(c_26, plain, (![E_19, C_15, B_14, A_13]: (E_19=C_15 | E_19=B_14 | E_19=A_13 | ~r2_hidden(E_19, k1_enumset1(A_13, B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.52/8.10  tff(c_9959, plain, (![D_27359, B_27360, A_27361]: (D_27359='#skF_6' | D_27359=B_27360 | D_27359=A_27361 | ~r2_hidden(D_27359, '#skF_7'))), inference(resolution, [status(thm)], [c_9864, c_26])).
% 16.52/8.10  tff(c_9998, plain, (![B_27360, A_27361]: ('#skF_3'('#skF_7')='#skF_6' | B_27360='#skF_3'('#skF_7') | A_27361='#skF_3'('#skF_7') | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_20, c_9959])).
% 16.52/8.10  tff(c_10022, plain, (![B_27360, A_27361]: ('#skF_3'('#skF_7')='#skF_6' | B_27360='#skF_3'('#skF_7') | A_27361='#skF_3'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_9998])).
% 16.52/8.10  tff(c_11838, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_10022])).
% 16.52/8.10  tff(c_495, plain, (![D_6]: (~r2_hidden(D_6, '#skF_6') | r2_hidden(D_6, k3_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_377, c_4])).
% 16.52/8.10  tff(c_1557, plain, (![A_166]: (k1_tarski(A_166)='#skF_7' | k1_tarski(A_166)=k1_xboole_0 | ~r2_hidden(A_166, '#skF_7'))), inference(resolution, [status(thm)], [c_66, c_721])).
% 16.52/8.10  tff(c_1571, plain, (k1_tarski('#skF_3'('#skF_7'))='#skF_7' | k1_tarski('#skF_3'('#skF_7'))=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_20, c_1557])).
% 16.52/8.10  tff(c_1582, plain, (k1_tarski('#skF_3'('#skF_7'))='#skF_7' | k1_tarski('#skF_3'('#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_78, c_1571])).
% 16.52/8.10  tff(c_1583, plain, (k1_tarski('#skF_3'('#skF_7'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1582])).
% 16.52/8.10  tff(c_1912, plain, (![B_178]: (r1_tarski(k1_xboole_0, B_178) | ~r2_hidden('#skF_3'('#skF_7'), B_178))), inference(superposition, [status(thm), theory('equality')], [c_1583, c_66])).
% 16.52/8.10  tff(c_2008, plain, (r1_tarski(k1_xboole_0, k3_tarski('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_495, c_1912])).
% 16.52/8.10  tff(c_2297, plain, (~r2_hidden('#skF_3'('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_2008])).
% 16.52/8.10  tff(c_3814, plain, (![A_250, B_251]: (k2_xboole_0('#skF_7', k1_enumset1(A_250, B_251, '#skF_6'))=k1_enumset1(A_250, B_251, '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_927])).
% 16.52/8.10  tff(c_4086, plain, (![D_260, A_261, B_262]: (~r2_hidden(D_260, '#skF_7') | r2_hidden(D_260, k1_enumset1(A_261, B_262, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3814, c_6])).
% 16.52/8.10  tff(c_4340, plain, (![D_272, B_273, A_274]: (D_272='#skF_6' | D_272=B_273 | D_272=A_274 | ~r2_hidden(D_272, '#skF_7'))), inference(resolution, [status(thm)], [c_4086, c_26])).
% 16.52/8.10  tff(c_4379, plain, (![B_273, A_274]: ('#skF_3'('#skF_7')='#skF_6' | B_273='#skF_3'('#skF_7') | A_274='#skF_3'('#skF_7') | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_20, c_4340])).
% 16.52/8.10  tff(c_4403, plain, (![B_273, A_274]: ('#skF_3'('#skF_7')='#skF_6' | B_273='#skF_3'('#skF_7') | A_274='#skF_3'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_4379])).
% 16.52/8.10  tff(c_6455, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_4403])).
% 16.52/8.10  tff(c_1622, plain, (r2_hidden('#skF_3'('#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1583, c_198])).
% 16.52/8.10  tff(c_6476, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6455, c_1622])).
% 16.52/8.10  tff(c_6487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_741, c_6476])).
% 16.52/8.10  tff(c_6488, plain, (![A_274, B_273]: (A_274='#skF_3'('#skF_7') | B_273='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_4403])).
% 16.52/8.10  tff(c_6491, plain, (![B_9256]: (B_9256='#skF_3'('#skF_7'))), inference(splitLeft, [status(thm)], [c_6488])).
% 16.52/8.10  tff(c_1637, plain, (r1_tarski(k1_tarski('#skF_3'('#skF_7')), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1583, c_70])).
% 16.52/8.10  tff(c_1650, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1583, c_1637])).
% 16.52/8.10  tff(c_503, plain, (![D_105, B_106, A_107]: (r2_hidden(D_105, B_106) | r2_hidden(D_105, A_107) | ~r2_hidden(D_105, k2_xboole_0(A_107, B_106)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.52/8.10  tff(c_3634, plain, (![D_246]: (r2_hidden(D_246, '#skF_6') | r2_hidden(D_246, '#skF_6') | ~r2_hidden(D_246, k3_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_377, c_503])).
% 16.52/8.10  tff(c_3679, plain, (r2_hidden('#skF_3'(k3_tarski('#skF_7')), '#skF_6') | k3_tarski('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_3634])).
% 16.52/8.10  tff(c_3680, plain, (k3_tarski('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3679])).
% 16.52/8.10  tff(c_1625, plain, (![B_49]: (r2_hidden('#skF_3'('#skF_7'), B_49) | ~r1_tarski(k1_xboole_0, B_49))), inference(superposition, [status(thm), theory('equality')], [c_1583, c_64])).
% 16.52/8.10  tff(c_3654, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_6') | ~r1_tarski(k1_xboole_0, k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_1625, c_3634])).
% 16.52/8.10  tff(c_3674, plain, (~r1_tarski(k1_xboole_0, k3_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_2297, c_2297, c_3654])).
% 16.52/8.10  tff(c_3681, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3680, c_3674])).
% 16.52/8.10  tff(c_3690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1650, c_3681])).
% 16.52/8.10  tff(c_3691, plain, (r2_hidden('#skF_3'(k3_tarski('#skF_7')), '#skF_6')), inference(splitRight, [status(thm)], [c_3679])).
% 16.52/8.10  tff(c_6548, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6491, c_3691])).
% 16.52/8.10  tff(c_7195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2297, c_6548])).
% 16.52/8.10  tff(c_7197, plain, (![A_18275]: (A_18275='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_6488])).
% 16.52/8.10  tff(c_7254, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7197, c_3691])).
% 16.52/8.10  tff(c_7901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2297, c_7254])).
% 16.52/8.10  tff(c_7903, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_2008])).
% 16.52/8.10  tff(c_11843, plain, (r2_hidden('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11838, c_7903])).
% 16.52/8.10  tff(c_11865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_781, c_11843])).
% 16.52/8.10  tff(c_11867, plain, ('#skF_3'('#skF_7')!='#skF_6'), inference(splitRight, [status(thm)], [c_10022])).
% 16.52/8.10  tff(c_11866, plain, (![A_27361, B_27360]: (A_27361='#skF_3'('#skF_7') | B_27360='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_10022])).
% 16.52/8.10  tff(c_11869, plain, (![B_36222]: (B_36222='#skF_3'('#skF_7'))), inference(splitLeft, [status(thm)], [c_11866])).
% 16.52/8.10  tff(c_1599, plain, (![B_83]: (k2_xboole_0(k1_xboole_0, B_83)=B_83 | ~r2_hidden('#skF_3'('#skF_7'), B_83))), inference(superposition, [status(thm), theory('equality')], [c_1583, c_216])).
% 16.52/8.10  tff(c_7960, plain, (k2_xboole_0(k1_xboole_0, '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_7903, c_1599])).
% 16.52/8.10  tff(c_12133, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_11869, c_7960])).
% 16.52/8.10  tff(c_12603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11867, c_12133])).
% 16.52/8.10  tff(c_12605, plain, (![A_45187]: (A_45187='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_11866])).
% 16.52/8.10  tff(c_12869, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_12605, c_7960])).
% 16.52/8.10  tff(c_13339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11867, c_12869])).
% 16.52/8.10  tff(c_13340, plain, (k1_tarski('#skF_3'('#skF_7'))='#skF_7'), inference(splitRight, [status(thm)], [c_1582])).
% 16.52/8.10  tff(c_1005, plain, (![D_137, A_138]: (~r2_hidden(D_137, A_138) | r2_hidden(D_137, k3_tarski(k1_tarski(A_138))))), inference(superposition, [status(thm), theory('equality')], [c_115, c_302])).
% 16.52/8.10  tff(c_1027, plain, (![A_138]: (r1_tarski('#skF_7', k3_tarski(k1_tarski(A_138))) | ~r2_hidden('#skF_6', A_138))), inference(resolution, [status(thm)], [c_1005, c_359])).
% 16.52/8.10  tff(c_13345, plain, (r1_tarski('#skF_7', k3_tarski('#skF_7')) | ~r2_hidden('#skF_6', '#skF_3'('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_13340, c_1027])).
% 16.52/8.10  tff(c_13748, plain, (~r2_hidden('#skF_6', '#skF_3'('#skF_7'))), inference(splitLeft, [status(thm)], [c_13345])).
% 16.52/8.10  tff(c_13752, plain, (~r1_tarski('#skF_7', '#skF_3'('#skF_7'))), inference(resolution, [status(thm)], [c_368, c_13748])).
% 16.52/8.10  tff(c_15268, plain, (![A_54230, B_54231]: (k2_xboole_0('#skF_7', k1_enumset1(A_54230, B_54231, '#skF_6'))=k1_enumset1(A_54230, B_54231, '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_927])).
% 16.52/8.10  tff(c_15628, plain, (![D_54244, A_54245, B_54246]: (~r2_hidden(D_54244, '#skF_7') | r2_hidden(D_54244, k1_enumset1(A_54245, B_54246, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_15268, c_6])).
% 16.52/8.10  tff(c_15958, plain, (![D_54261, B_54262, A_54263]: (D_54261='#skF_6' | D_54261=B_54262 | D_54261=A_54263 | ~r2_hidden(D_54261, '#skF_7'))), inference(resolution, [status(thm)], [c_15628, c_26])).
% 16.52/8.10  tff(c_16133, plain, (![D_54267, B_54268, A_54269]: (D_54267='#skF_6' | D_54267=B_54268 | D_54267=A_54269 | ~r2_hidden(D_54267, '#skF_8'))), inference(resolution, [status(thm)], [c_340, c_15958])).
% 16.52/8.10  tff(c_16166, plain, (![B_54268, A_54269]: ('#skF_3'('#skF_8')='#skF_6' | B_54268='#skF_3'('#skF_8') | A_54269='#skF_3'('#skF_8') | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_20, c_16133])).
% 16.52/8.10  tff(c_16182, plain, (![B_54268, A_54269]: ('#skF_3'('#skF_8')='#skF_6' | B_54268='#skF_3'('#skF_8') | A_54269='#skF_3'('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_76, c_16166])).
% 16.52/8.10  tff(c_18058, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_16182])).
% 16.52/8.10  tff(c_13970, plain, (![D_54178]: (k1_tarski(D_54178)='#skF_7' | k1_tarski(D_54178)=k1_xboole_0 | ~r2_hidden(D_54178, '#skF_8'))), inference(resolution, [status(thm)], [c_340, c_1557])).
% 16.52/8.10  tff(c_13982, plain, (k1_tarski('#skF_3'('#skF_8'))='#skF_7' | k1_tarski('#skF_3'('#skF_8'))=k1_xboole_0 | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_13970])).
% 16.52/8.10  tff(c_13991, plain, (k1_tarski('#skF_3'('#skF_8'))='#skF_7' | k1_tarski('#skF_3'('#skF_8'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_76, c_13982])).
% 16.52/8.10  tff(c_13992, plain, (k1_tarski('#skF_3'('#skF_8'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13991])).
% 16.52/8.10  tff(c_14031, plain, (r2_hidden('#skF_3'('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13992, c_198])).
% 16.52/8.10  tff(c_18079, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18058, c_14031])).
% 16.52/8.10  tff(c_18090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_741, c_18079])).
% 16.52/8.10  tff(c_18092, plain, ('#skF_3'('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_16182])).
% 16.52/8.10  tff(c_18091, plain, (![A_54269, B_54268]: (A_54269='#skF_3'('#skF_8') | B_54268='#skF_3'('#skF_8'))), inference(splitRight, [status(thm)], [c_16182])).
% 16.52/8.10  tff(c_18094, plain, (![B_61834]: (B_61834='#skF_3'('#skF_8'))), inference(splitLeft, [status(thm)], [c_18091])).
% 16.52/8.10  tff(c_30, plain, (![E_19, A_13, C_15]: (r2_hidden(E_19, k1_enumset1(A_13, E_19, C_15)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.52/8.10  tff(c_1492, plain, (![A_162, C_163]: (k2_xboole_0('#skF_7', k1_enumset1(A_162, '#skF_6', C_163))=k1_enumset1(A_162, '#skF_6', C_163))), inference(resolution, [status(thm)], [c_30, c_927])).
% 16.52/8.10  tff(c_15423, plain, (![D_54236, A_54237, C_54238]: (~r2_hidden(D_54236, '#skF_7') | r2_hidden(D_54236, k1_enumset1(A_54237, '#skF_6', C_54238)))), inference(superposition, [status(thm), theory('equality')], [c_1492, c_6])).
% 16.52/8.10  tff(c_15902, plain, (![D_54258, C_54259, A_54260]: (D_54258=C_54259 | D_54258='#skF_6' | D_54258=A_54260 | ~r2_hidden(D_54258, '#skF_7'))), inference(resolution, [status(thm)], [c_15423, c_26])).
% 16.52/8.10  tff(c_15935, plain, (![C_54259, A_54260]: (C_54259='#skF_3'('#skF_7') | '#skF_3'('#skF_7')='#skF_6' | A_54260='#skF_3'('#skF_7') | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_20, c_15902])).
% 16.52/8.10  tff(c_15957, plain, (![C_54259, A_54260]: (C_54259='#skF_3'('#skF_7') | '#skF_3'('#skF_7')='#skF_6' | A_54260='#skF_3'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_15935])).
% 16.52/8.10  tff(c_16183, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_15957])).
% 16.52/8.10  tff(c_18125, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_18094, c_16183])).
% 16.52/8.10  tff(c_18680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18092, c_18125])).
% 16.52/8.10  tff(c_18682, plain, (![A_69503]: (A_69503='#skF_3'('#skF_8'))), inference(splitRight, [status(thm)], [c_18091])).
% 16.52/8.10  tff(c_18713, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_18682, c_16183])).
% 16.52/8.10  tff(c_19268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18092, c_18713])).
% 16.52/8.10  tff(c_19269, plain, (![A_54260, C_54259]: (A_54260='#skF_3'('#skF_7') | C_54259='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_15957])).
% 16.52/8.10  tff(c_21537, plain, (![C_85924]: (C_85924='#skF_3'('#skF_7'))), inference(splitLeft, [status(thm)], [c_19269])).
% 16.52/8.10  tff(c_13493, plain, (![B_54156]: (r1_tarski('#skF_7', B_54156) | ~r2_hidden('#skF_3'('#skF_7'), B_54156))), inference(superposition, [status(thm), theory('equality')], [c_13340, c_66])).
% 16.52/8.10  tff(c_13591, plain, (![A_13, C_15]: (r1_tarski('#skF_7', k1_enumset1(A_13, '#skF_3'('#skF_7'), C_15)))), inference(resolution, [status(thm)], [c_30, c_13493])).
% 16.52/8.10  tff(c_21789, plain, (r1_tarski('#skF_7', '#skF_3'('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_21537, c_13591])).
% 16.52/8.10  tff(c_22232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13752, c_21789])).
% 16.52/8.10  tff(c_22933, plain, (![A_103638]: (A_103638='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_19269])).
% 16.52/8.10  tff(c_23185, plain, (r1_tarski('#skF_7', '#skF_3'('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_22933, c_13591])).
% 16.52/8.10  tff(c_23628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13752, c_23185])).
% 16.52/8.10  tff(c_23629, plain, (k1_tarski('#skF_3'('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_13991])).
% 16.52/8.10  tff(c_23802, plain, (![B_112506]: (r1_tarski('#skF_7', B_112506) | ~r2_hidden('#skF_3'('#skF_8'), B_112506))), inference(superposition, [status(thm), theory('equality')], [c_23629, c_66])).
% 16.52/8.10  tff(c_23873, plain, (r1_tarski('#skF_7', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_23802])).
% 16.52/8.10  tff(c_23917, plain, (r1_tarski('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_76, c_23873])).
% 16.52/8.10  tff(c_23924, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_23917, c_22])).
% 16.52/8.10  tff(c_343, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_337, c_82])).
% 16.52/8.10  tff(c_23925, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_23924, c_343])).
% 16.52/8.10  tff(c_23927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_23925])).
% 16.52/8.10  tff(c_23928, plain, (r1_tarski('#skF_7', k3_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_13345])).
% 16.52/8.10  tff(c_23933, plain, (k2_xboole_0('#skF_7', k3_tarski('#skF_7'))=k3_tarski('#skF_7')), inference(resolution, [status(thm)], [c_23928, c_22])).
% 16.52/8.10  tff(c_362, plain, (![B_12]: (r2_hidden('#skF_6', k2_xboole_0('#skF_7', B_12)))), inference(superposition, [status(thm), theory('equality')], [c_337, c_199])).
% 16.52/8.10  tff(c_23995, plain, (r2_hidden('#skF_6', k3_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_23933, c_362])).
% 16.52/8.10  tff(c_25863, plain, (![D_112571]: (r2_hidden(D_112571, '#skF_6') | r2_hidden(D_112571, '#skF_6') | ~r2_hidden(D_112571, k3_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_377, c_503])).
% 16.52/8.10  tff(c_25905, plain, (r2_hidden('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_23995, c_25863])).
% 16.52/8.10  tff(c_25937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_781, c_781, c_25905])).
% 16.52/8.10  tff(c_25939, plain, (r2_hidden('#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_751])).
% 16.52/8.10  tff(c_25943, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_25939, c_359])).
% 16.52/8.10  tff(c_26840, plain, (![A_112608, B_112609]: (k2_xboole_0('#skF_7', k1_enumset1(A_112608, B_112609, '#skF_6'))=k1_enumset1(A_112608, B_112609, '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_26193])).
% 16.52/8.10  tff(c_48853, plain, (![D_201729, A_201730, B_201731]: (~r2_hidden(D_201729, '#skF_7') | r2_hidden(D_201729, k1_enumset1(A_201730, B_201731, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_26840, c_6])).
% 16.52/8.10  tff(c_53421, plain, (![D_220703, B_220704, A_220705]: (D_220703='#skF_6' | D_220703=B_220704 | D_220703=A_220705 | ~r2_hidden(D_220703, '#skF_7'))), inference(resolution, [status(thm)], [c_48853, c_26])).
% 16.52/8.10  tff(c_53485, plain, (![D_220814, B_220815, A_220816]: (D_220814='#skF_6' | D_220814=B_220815 | D_220814=A_220816 | ~r2_hidden(D_220814, '#skF_8'))), inference(resolution, [status(thm)], [c_340, c_53421])).
% 16.52/8.10  tff(c_53518, plain, (![B_220815, A_220816]: ('#skF_3'('#skF_8')='#skF_6' | B_220815='#skF_3'('#skF_8') | A_220816='#skF_3'('#skF_8') | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_20, c_53485])).
% 16.52/8.10  tff(c_53534, plain, (![B_220815, A_220816]: ('#skF_3'('#skF_8')='#skF_6' | B_220815='#skF_3'('#skF_8') | A_220816='#skF_3'('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_76, c_53518])).
% 16.52/8.10  tff(c_55515, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_53534])).
% 16.52/8.10  tff(c_26305, plain, (![D_112591, A_112592]: (~r2_hidden(D_112591, A_112592) | r2_hidden(D_112591, k3_tarski(k1_tarski(A_112592))))), inference(superposition, [status(thm), theory('equality')], [c_115, c_246])).
% 16.52/8.10  tff(c_26327, plain, (![A_112592]: (r1_tarski('#skF_7', k3_tarski(k1_tarski(A_112592))) | ~r2_hidden('#skF_6', A_112592))), inference(resolution, [status(thm)], [c_26305, c_359])).
% 16.52/8.10  tff(c_46879, plain, (r1_tarski('#skF_7', k3_tarski(k1_xboole_0)) | ~r2_hidden('#skF_6', '#skF_3'('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_46875, c_26327])).
% 16.52/8.10  tff(c_48140, plain, (~r2_hidden('#skF_6', '#skF_3'('#skF_8'))), inference(splitLeft, [status(thm)], [c_46879])).
% 16.52/8.10  tff(c_48144, plain, (~r1_tarski('#skF_7', '#skF_3'('#skF_8'))), inference(resolution, [status(thm)], [c_368, c_48140])).
% 16.52/8.10  tff(c_55519, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_55515, c_48144])).
% 16.52/8.10  tff(c_55543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25943, c_55519])).
% 16.52/8.10  tff(c_55545, plain, ('#skF_3'('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_53534])).
% 16.52/8.10  tff(c_55544, plain, (![A_220816, B_220815]: (A_220816='#skF_3'('#skF_8') | B_220815='#skF_3'('#skF_8'))), inference(splitRight, [status(thm)], [c_53534])).
% 16.52/8.10  tff(c_55547, plain, (![B_229947]: (B_229947='#skF_3'('#skF_8'))), inference(splitLeft, [status(thm)], [c_55544])).
% 16.52/8.10  tff(c_53460, plain, (![B_220704, A_220705]: ('#skF_3'('#skF_7')='#skF_6' | B_220704='#skF_3'('#skF_7') | A_220705='#skF_3'('#skF_7') | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_20, c_53421])).
% 16.52/8.10  tff(c_53484, plain, (![B_220704, A_220705]: ('#skF_3'('#skF_7')='#skF_6' | B_220704='#skF_3'('#skF_7') | A_220705='#skF_3'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_53460])).
% 16.52/8.10  tff(c_53535, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_53484])).
% 16.52/8.10  tff(c_55585, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_55547, c_53535])).
% 16.52/8.10  tff(c_56215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55545, c_55585])).
% 16.52/8.10  tff(c_56217, plain, (![A_238642]: (A_238642='#skF_3'('#skF_8'))), inference(splitRight, [status(thm)], [c_55544])).
% 16.52/8.10  tff(c_56255, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_56217, c_53535])).
% 16.52/8.10  tff(c_56885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55545, c_56255])).
% 16.52/8.10  tff(c_56887, plain, ('#skF_3'('#skF_7')!='#skF_6'), inference(splitRight, [status(thm)], [c_53484])).
% 16.52/8.10  tff(c_56886, plain, (![A_220705, B_220704]: (A_220705='#skF_3'('#skF_7') | B_220704='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_53484])).
% 16.52/8.10  tff(c_59187, plain, (![B_257169]: (B_257169='#skF_3'('#skF_7'))), inference(splitLeft, [status(thm)], [c_56886])).
% 16.52/8.10  tff(c_25947, plain, (k2_xboole_0('#skF_7', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_25943, c_22])).
% 16.52/8.10  tff(c_25960, plain, (![D_6]: (~r2_hidden(D_6, '#skF_7') | r2_hidden(D_6, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_25947, c_6])).
% 16.52/8.10  tff(c_47057, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_47043, c_25960])).
% 16.52/8.10  tff(c_47270, plain, (![B_201684]: (r1_tarski(k1_xboole_0, B_201684) | ~r2_hidden('#skF_3'('#skF_8'), B_201684))), inference(superposition, [status(thm), theory('equality')], [c_46875, c_66])).
% 16.52/8.10  tff(c_47370, plain, (r1_tarski(k1_xboole_0, '#skF_6')), inference(resolution, [status(thm)], [c_47057, c_47270])).
% 16.52/8.10  tff(c_47416, plain, (k2_xboole_0(k1_xboole_0, '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_47370, c_22])).
% 16.52/8.10  tff(c_59392, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_59187, c_47416])).
% 16.52/8.10  tff(c_59976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56887, c_59392])).
% 16.52/8.10  tff(c_59979, plain, (![A_266998]: (A_266998='#skF_3'('#skF_7'))), inference(splitRight, [status(thm)], [c_56886])).
% 16.52/8.10  tff(c_60184, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_59979, c_47416])).
% 16.52/8.10  tff(c_60768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56887, c_60184])).
% 16.52/8.10  tff(c_60770, plain, (r2_hidden('#skF_6', '#skF_3'('#skF_8'))), inference(splitRight, [status(thm)], [c_46879])).
% 16.52/8.10  tff(c_60782, plain, (r1_tarski('#skF_7', '#skF_3'('#skF_8'))), inference(resolution, [status(thm)], [c_60770, c_359])).
% 16.52/8.10  tff(c_70878, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70877, c_60782])).
% 16.52/8.10  tff(c_71452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_745, c_70878])).
% 16.52/8.10  tff(c_71453, plain, (k1_tarski('#skF_3'('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_46874])).
% 16.52/8.10  tff(c_71777, plain, (![B_319838]: (r1_tarski('#skF_7', B_319838) | ~r2_hidden('#skF_3'('#skF_8'), B_319838))), inference(superposition, [status(thm), theory('equality')], [c_71453, c_66])).
% 16.52/8.10  tff(c_71862, plain, (r1_tarski('#skF_7', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_71777])).
% 16.52/8.10  tff(c_71918, plain, (r1_tarski('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_76, c_71862])).
% 16.52/8.10  tff(c_71925, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_71918, c_22])).
% 16.52/8.10  tff(c_71926, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_71925, c_343])).
% 16.52/8.10  tff(c_71928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_71926])).
% 16.52/8.10  tff(c_71944, plain, (![B_319839]: (r1_tarski('#skF_7', k1_tarski(B_319839)))), inference(splitRight, [status(thm)], [c_719])).
% 16.52/8.10  tff(c_71947, plain, (![B_319839]: (k1_tarski(B_319839)='#skF_7' | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_71944, c_68])).
% 16.52/8.10  tff(c_71955, plain, (![B_319839]: (k1_tarski(B_319839)='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_78, c_71947])).
% 16.52/8.10  tff(c_259, plain, (![B_93]: (k2_xboole_0(k1_tarski(B_93), k1_tarski(B_93))=k1_tarski(B_93))), inference(resolution, [status(thm)], [c_70, c_138])).
% 16.52/8.10  tff(c_271, plain, (![B_93]: (k3_tarski(k1_tarski(k1_tarski(B_93)))=k1_tarski(B_93))), inference(superposition, [status(thm), theory('equality')], [c_259, c_115])).
% 16.52/8.10  tff(c_350, plain, (k3_tarski(k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_337, c_271])).
% 16.52/8.10  tff(c_389, plain, (k3_tarski(k1_tarski('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_337, c_350])).
% 16.52/8.10  tff(c_71989, plain, (k3_tarski('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_71955, c_389])).
% 16.52/8.10  tff(c_118, plain, (![A_71]: (k3_tarski(k1_tarski(A_71))=k2_xboole_0(A_71, A_71))), inference(superposition, [status(thm), theory('equality')], [c_50, c_106])).
% 16.52/8.10  tff(c_127, plain, (![A_71]: (r1_tarski(A_71, k3_tarski(k1_tarski(A_71))))), inference(superposition, [status(thm), theory('equality')], [c_118, c_24])).
% 16.52/8.10  tff(c_71999, plain, (![A_71]: (r1_tarski(A_71, k3_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_71955, c_127])).
% 16.52/8.10  tff(c_72109, plain, (![A_71]: (r1_tarski(A_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_71989, c_71999])).
% 16.52/8.10  tff(c_388, plain, (![A_50]: (A_50='#skF_7' | k1_xboole_0=A_50 | ~r1_tarski(A_50, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_347])).
% 16.52/8.10  tff(c_72153, plain, ('#skF_7'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72109, c_388])).
% 16.52/8.10  tff(c_72112, plain, (![A_50]: (A_50='#skF_7' | k1_xboole_0=A_50)), inference(demodulation, [status(thm), theory('equality')], [c_72109, c_388])).
% 16.52/8.10  tff(c_72154, plain, (![A_50]: (A_50='#skF_7' | A_50='#skF_8' | '#skF_7'='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_72153, c_72112])).
% 16.52/8.10  tff(c_72378, plain, (![A_322393]: (A_322393='#skF_7' | A_322393='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_80, c_72154])).
% 16.52/8.10  tff(c_72625, plain, (k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_72378, c_78])).
% 16.52/8.10  tff(c_72721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_72625])).
% 16.52/8.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.52/8.10  
% 16.52/8.10  Inference rules
% 16.52/8.10  ----------------------
% 16.52/8.10  #Ref     : 0
% 16.52/8.10  #Sup     : 12499
% 16.52/8.10  #Fact    : 142
% 16.52/8.10  #Define  : 0
% 16.52/8.10  #Split   : 54
% 16.52/8.10  #Chain   : 0
% 16.52/8.10  #Close   : 0
% 16.52/8.10  
% 16.52/8.10  Ordering : KBO
% 16.52/8.10  
% 16.52/8.10  Simplification rules
% 16.52/8.10  ----------------------
% 16.52/8.10  #Subsume      : 1105
% 16.52/8.10  #Demod        : 4553
% 16.52/8.10  #Tautology    : 3450
% 16.52/8.10  #SimpNegUnit  : 330
% 16.52/8.10  #BackRed      : 372
% 16.52/8.10  
% 16.52/8.10  #Partial instantiations: 70327
% 16.52/8.10  #Strategies tried      : 1
% 16.52/8.10  
% 16.52/8.10  Timing (in seconds)
% 16.52/8.10  ----------------------
% 16.52/8.10  Preprocessing        : 0.34
% 16.52/8.10  Parsing              : 0.17
% 16.52/8.10  CNF conversion       : 0.03
% 16.52/8.10  Main loop            : 6.94
% 16.52/8.10  Inferencing          : 3.31
% 16.52/8.10  Reduction            : 2.12
% 16.52/8.10  Demodulation         : 1.69
% 16.52/8.10  BG Simplification    : 0.18
% 16.52/8.10  Subsumption          : 1.03
% 16.52/8.11  Abstraction          : 0.25
% 16.52/8.11  MUC search           : 0.00
% 16.52/8.11  Cooper               : 0.00
% 16.52/8.11  Total                : 7.37
% 16.52/8.11  Index Insertion      : 0.00
% 16.52/8.11  Index Deletion       : 0.00
% 16.52/8.11  Index Matching       : 0.00
% 16.52/8.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
