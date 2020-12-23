%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:12 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 249 expanded)
%              Number of leaves         :   43 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  141 ( 472 expanded)
%              Number of equality atoms :   53 ( 286 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_112,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_79,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_83,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_77,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_64,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_62,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_87,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,(
    ! [A_64,B_65] :
      ( r1_xboole_0(k1_tarski(A_64),B_65)
      | r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_68,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_103,plain,(
    ! [A_77,B_78] : r1_tarski(A_77,k2_xboole_0(A_77,B_78)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_106,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_103])).

tff(c_233,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_251,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_106,c_233])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_608,plain,(
    ! [A_123,B_124,C_125] :
      ( ~ r1_xboole_0(A_123,B_124)
      | ~ r2_hidden(C_125,k3_xboole_0(A_123,B_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_681,plain,(
    ! [A_130,B_131] :
      ( ~ r1_xboole_0(A_130,B_131)
      | v1_xboole_0(k3_xboole_0(A_130,B_131)) ) ),
    inference(resolution,[status(thm)],[c_6,c_608])).

tff(c_733,plain,(
    ! [B_135,A_136] :
      ( ~ r1_xboole_0(B_135,A_136)
      | v1_xboole_0(k3_xboole_0(A_136,B_135)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_681])).

tff(c_745,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_733])).

tff(c_761,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_745])).

tff(c_765,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_761])).

tff(c_1143,plain,(
    ! [B_153,A_154] :
      ( k3_xboole_0(B_153,k1_tarski(A_154)) = k1_tarski(A_154)
      | ~ r2_hidden(A_154,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1169,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_251])).

tff(c_1212,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_1169])).

tff(c_1214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_1212])).

tff(c_1215,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_745])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1219,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1215,c_8])).

tff(c_1223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1219])).

tff(c_1224,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1225,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_30,plain,(
    ! [A_28] : r1_tarski(k1_xboole_0,A_28) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1229,plain,(
    ! [A_28] : r1_tarski('#skF_4',A_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1225,c_30])).

tff(c_1461,plain,(
    ! [A_190,B_191] :
      ( k2_xboole_0(A_190,B_191) = B_191
      | ~ r1_tarski(A_190,B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1481,plain,(
    ! [A_28] : k2_xboole_0('#skF_4',A_28) = A_28 ),
    inference(resolution,[status(thm)],[c_1229,c_1461])).

tff(c_1493,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1481,c_68])).

tff(c_1495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1224,c_1493])).

tff(c_1496,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_54,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_tarski(A_62),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1497,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1502,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1497,c_68])).

tff(c_2494,plain,(
    ! [A_263,C_264,B_265] :
      ( r1_tarski(A_263,k2_xboole_0(C_264,B_265))
      | ~ r1_tarski(A_263,B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2583,plain,(
    ! [A_268] :
      ( r1_tarski(A_268,'#skF_4')
      | ~ r1_tarski(A_268,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1502,c_2494])).

tff(c_3509,plain,(
    ! [A_307] :
      ( r1_tarski(k1_tarski(A_307),'#skF_4')
      | ~ r2_hidden(A_307,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_2583])).

tff(c_52,plain,(
    ! [A_62,B_63] :
      ( r2_hidden(A_62,B_63)
      | ~ r1_tarski(k1_tarski(A_62),B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3534,plain,(
    ! [A_308] :
      ( r2_hidden(A_308,'#skF_4')
      | ~ r2_hidden(A_308,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3509,c_52])).

tff(c_3551,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_3534])).

tff(c_3552,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3551])).

tff(c_3558,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3552,c_8])).

tff(c_3563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1496,c_3558])).

tff(c_3565,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3551])).

tff(c_66,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1529,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1497,c_1497,c_66])).

tff(c_2103,plain,(
    ! [A_243,B_244] :
      ( r1_xboole_0(k1_tarski(A_243),B_244)
      | r2_hidden(A_243,B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2107,plain,(
    ! [B_245] :
      ( r1_xboole_0('#skF_4',B_245)
      | r2_hidden('#skF_3',B_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_2103])).

tff(c_1748,plain,(
    ! [A_217,B_218] :
      ( r1_tarski(k1_tarski(A_217),B_218)
      | ~ r2_hidden(A_217,B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1760,plain,(
    ! [B_218] :
      ( r1_tarski('#skF_4',B_218)
      | ~ r2_hidden('#skF_3',B_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_1748])).

tff(c_2114,plain,(
    ! [B_245] :
      ( r1_tarski('#skF_4',B_245)
      | r1_xboole_0('#skF_4',B_245) ) ),
    inference(resolution,[status(thm)],[c_2107,c_1760])).

tff(c_34,plain,(
    ! [A_31] : k5_xboole_0(A_31,k1_xboole_0) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    ! [A_27] : k3_xboole_0(A_27,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2269,plain,(
    ! [A_255,B_256] : k5_xboole_0(A_255,k3_xboole_0(A_255,B_256)) = k4_xboole_0(A_255,B_256) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2299,plain,(
    ! [A_27] : k5_xboole_0(A_27,k1_xboole_0) = k4_xboole_0(A_27,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2269])).

tff(c_2318,plain,(
    ! [A_257] : k4_xboole_0(A_257,k1_xboole_0) = A_257 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2299])).

tff(c_32,plain,(
    ! [A_29,B_30] : r1_tarski(k4_xboole_0(A_29,B_30),A_29) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2338,plain,(
    ! [A_257] : r1_tarski(A_257,A_257) ),
    inference(superposition,[status(thm),theory(equality)],[c_2318,c_32])).

tff(c_2604,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2338,c_2583])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2621,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2604,c_26])).

tff(c_2806,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2621,c_2])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2827,plain,(
    ! [C_12] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_12,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2806,c_12])).

tff(c_3620,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2827])).

tff(c_3631,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_2114,c_3620])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3658,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3631,c_22])).

tff(c_3669,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1502,c_3658])).

tff(c_3671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1529,c_3669])).

tff(c_3674,plain,(
    ! [C_323] : ~ r2_hidden(C_323,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_2827])).

tff(c_3686,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_3674])).

tff(c_3692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3565,c_3686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.79  
% 4.42/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.79  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.42/1.79  
% 4.42/1.79  %Foreground sorts:
% 4.42/1.79  
% 4.42/1.79  
% 4.42/1.79  %Background operators:
% 4.42/1.79  
% 4.42/1.79  
% 4.42/1.79  %Foreground operators:
% 4.42/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.42/1.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.42/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.42/1.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.42/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.42/1.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.42/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.42/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.42/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.42/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.42/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.42/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.42/1.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.42/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.42/1.79  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.79  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.79  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.42/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.42/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.42/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.42/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.42/1.79  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.42/1.79  
% 4.53/1.82  tff(f_133, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.53/1.82  tff(f_108, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.53/1.82  tff(f_85, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.53/1.82  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.53/1.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.53/1.82  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.53/1.82  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.53/1.82  tff(f_112, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 4.53/1.82  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.53/1.82  tff(f_79, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.53/1.82  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.53/1.82  tff(f_103, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.53/1.82  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.53/1.82  tff(f_83, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.53/1.82  tff(f_77, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.53/1.82  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.53/1.82  tff(f_81, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.53/1.82  tff(c_64, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.53/1.82  tff(c_88, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_64])).
% 4.53/1.82  tff(c_62, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.53/1.82  tff(c_87, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_62])).
% 4.53/1.82  tff(c_56, plain, (![A_64, B_65]: (r1_xboole_0(k1_tarski(A_64), B_65) | r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.53/1.82  tff(c_68, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.53/1.82  tff(c_103, plain, (![A_77, B_78]: (r1_tarski(A_77, k2_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.53/1.82  tff(c_106, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_103])).
% 4.53/1.82  tff(c_233, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=A_89 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.53/1.82  tff(c_251, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(resolution, [status(thm)], [c_106, c_233])).
% 4.53/1.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.53/1.82  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.53/1.82  tff(c_608, plain, (![A_123, B_124, C_125]: (~r1_xboole_0(A_123, B_124) | ~r2_hidden(C_125, k3_xboole_0(A_123, B_124)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.53/1.82  tff(c_681, plain, (![A_130, B_131]: (~r1_xboole_0(A_130, B_131) | v1_xboole_0(k3_xboole_0(A_130, B_131)))), inference(resolution, [status(thm)], [c_6, c_608])).
% 4.53/1.82  tff(c_733, plain, (![B_135, A_136]: (~r1_xboole_0(B_135, A_136) | v1_xboole_0(k3_xboole_0(A_136, B_135)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_681])).
% 4.53/1.82  tff(c_745, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_251, c_733])).
% 4.53/1.82  tff(c_761, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_745])).
% 4.53/1.82  tff(c_765, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_761])).
% 4.53/1.82  tff(c_1143, plain, (![B_153, A_154]: (k3_xboole_0(B_153, k1_tarski(A_154))=k1_tarski(A_154) | ~r2_hidden(A_154, B_153))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.53/1.82  tff(c_1169, plain, (k1_tarski('#skF_3')='#skF_4' | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1143, c_251])).
% 4.53/1.82  tff(c_1212, plain, (k1_tarski('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_765, c_1169])).
% 4.53/1.82  tff(c_1214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_1212])).
% 4.53/1.82  tff(c_1215, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_745])).
% 4.53/1.82  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.53/1.82  tff(c_1219, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1215, c_8])).
% 4.53/1.82  tff(c_1223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_1219])).
% 4.53/1.82  tff(c_1224, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_64])).
% 4.53/1.82  tff(c_1225, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_64])).
% 4.53/1.82  tff(c_30, plain, (![A_28]: (r1_tarski(k1_xboole_0, A_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.53/1.82  tff(c_1229, plain, (![A_28]: (r1_tarski('#skF_4', A_28))), inference(demodulation, [status(thm), theory('equality')], [c_1225, c_30])).
% 4.53/1.82  tff(c_1461, plain, (![A_190, B_191]: (k2_xboole_0(A_190, B_191)=B_191 | ~r1_tarski(A_190, B_191))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.53/1.82  tff(c_1481, plain, (![A_28]: (k2_xboole_0('#skF_4', A_28)=A_28)), inference(resolution, [status(thm)], [c_1229, c_1461])).
% 4.53/1.82  tff(c_1493, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1481, c_68])).
% 4.53/1.82  tff(c_1495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1224, c_1493])).
% 4.53/1.82  tff(c_1496, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 4.53/1.82  tff(c_54, plain, (![A_62, B_63]: (r1_tarski(k1_tarski(A_62), B_63) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.53/1.82  tff(c_1497, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_62])).
% 4.53/1.82  tff(c_1502, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1497, c_68])).
% 4.53/1.82  tff(c_2494, plain, (![A_263, C_264, B_265]: (r1_tarski(A_263, k2_xboole_0(C_264, B_265)) | ~r1_tarski(A_263, B_265))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.53/1.82  tff(c_2583, plain, (![A_268]: (r1_tarski(A_268, '#skF_4') | ~r1_tarski(A_268, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1502, c_2494])).
% 4.53/1.82  tff(c_3509, plain, (![A_307]: (r1_tarski(k1_tarski(A_307), '#skF_4') | ~r2_hidden(A_307, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_2583])).
% 4.53/1.82  tff(c_52, plain, (![A_62, B_63]: (r2_hidden(A_62, B_63) | ~r1_tarski(k1_tarski(A_62), B_63))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.53/1.82  tff(c_3534, plain, (![A_308]: (r2_hidden(A_308, '#skF_4') | ~r2_hidden(A_308, '#skF_5'))), inference(resolution, [status(thm)], [c_3509, c_52])).
% 4.53/1.82  tff(c_3551, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6, c_3534])).
% 4.53/1.82  tff(c_3552, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_3551])).
% 4.53/1.82  tff(c_3558, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3552, c_8])).
% 4.53/1.82  tff(c_3563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1496, c_3558])).
% 4.53/1.82  tff(c_3565, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_3551])).
% 4.53/1.82  tff(c_66, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.53/1.82  tff(c_1529, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1497, c_1497, c_66])).
% 4.53/1.82  tff(c_2103, plain, (![A_243, B_244]: (r1_xboole_0(k1_tarski(A_243), B_244) | r2_hidden(A_243, B_244))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.53/1.82  tff(c_2107, plain, (![B_245]: (r1_xboole_0('#skF_4', B_245) | r2_hidden('#skF_3', B_245))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_2103])).
% 4.53/1.82  tff(c_1748, plain, (![A_217, B_218]: (r1_tarski(k1_tarski(A_217), B_218) | ~r2_hidden(A_217, B_218))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.53/1.82  tff(c_1760, plain, (![B_218]: (r1_tarski('#skF_4', B_218) | ~r2_hidden('#skF_3', B_218))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_1748])).
% 4.53/1.82  tff(c_2114, plain, (![B_245]: (r1_tarski('#skF_4', B_245) | r1_xboole_0('#skF_4', B_245))), inference(resolution, [status(thm)], [c_2107, c_1760])).
% 4.53/1.82  tff(c_34, plain, (![A_31]: (k5_xboole_0(A_31, k1_xboole_0)=A_31)), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.53/1.82  tff(c_28, plain, (![A_27]: (k3_xboole_0(A_27, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.53/1.82  tff(c_2269, plain, (![A_255, B_256]: (k5_xboole_0(A_255, k3_xboole_0(A_255, B_256))=k4_xboole_0(A_255, B_256))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.53/1.82  tff(c_2299, plain, (![A_27]: (k5_xboole_0(A_27, k1_xboole_0)=k4_xboole_0(A_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2269])).
% 4.53/1.82  tff(c_2318, plain, (![A_257]: (k4_xboole_0(A_257, k1_xboole_0)=A_257)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2299])).
% 4.53/1.82  tff(c_32, plain, (![A_29, B_30]: (r1_tarski(k4_xboole_0(A_29, B_30), A_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.53/1.82  tff(c_2338, plain, (![A_257]: (r1_tarski(A_257, A_257))), inference(superposition, [status(thm), theory('equality')], [c_2318, c_32])).
% 4.53/1.82  tff(c_2604, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2338, c_2583])).
% 4.53/1.82  tff(c_26, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.53/1.82  tff(c_2621, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_2604, c_26])).
% 4.53/1.82  tff(c_2806, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2621, c_2])).
% 4.53/1.82  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.53/1.82  tff(c_2827, plain, (![C_12]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_12, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2806, c_12])).
% 4.53/1.82  tff(c_3620, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_2827])).
% 4.53/1.82  tff(c_3631, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_2114, c_3620])).
% 4.53/1.82  tff(c_22, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.53/1.82  tff(c_3658, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_3631, c_22])).
% 4.53/1.82  tff(c_3669, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1502, c_3658])).
% 4.53/1.82  tff(c_3671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1529, c_3669])).
% 4.53/1.82  tff(c_3674, plain, (![C_323]: (~r2_hidden(C_323, '#skF_5'))), inference(splitRight, [status(thm)], [c_2827])).
% 4.53/1.82  tff(c_3686, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6, c_3674])).
% 4.53/1.82  tff(c_3692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3565, c_3686])).
% 4.53/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.82  
% 4.53/1.82  Inference rules
% 4.53/1.82  ----------------------
% 4.53/1.82  #Ref     : 1
% 4.53/1.82  #Sup     : 873
% 4.53/1.82  #Fact    : 0
% 4.53/1.82  #Define  : 0
% 4.53/1.82  #Split   : 12
% 4.53/1.82  #Chain   : 0
% 4.53/1.82  #Close   : 0
% 4.53/1.82  
% 4.53/1.82  Ordering : KBO
% 4.53/1.82  
% 4.53/1.82  Simplification rules
% 4.53/1.82  ----------------------
% 4.53/1.82  #Subsume      : 81
% 4.53/1.82  #Demod        : 296
% 4.53/1.82  #Tautology    : 528
% 4.53/1.82  #SimpNegUnit  : 15
% 4.53/1.82  #BackRed      : 24
% 4.53/1.82  
% 4.53/1.82  #Partial instantiations: 0
% 4.53/1.82  #Strategies tried      : 1
% 4.53/1.82  
% 4.53/1.82  Timing (in seconds)
% 4.53/1.82  ----------------------
% 4.53/1.83  Preprocessing        : 0.33
% 4.53/1.83  Parsing              : 0.18
% 4.53/1.83  CNF conversion       : 0.02
% 4.53/1.83  Main loop            : 0.69
% 4.53/1.83  Inferencing          : 0.26
% 4.53/1.83  Reduction            : 0.24
% 4.53/1.83  Demodulation         : 0.17
% 4.53/1.83  BG Simplification    : 0.03
% 4.53/1.83  Subsumption          : 0.10
% 4.53/1.83  Abstraction          : 0.03
% 4.53/1.83  MUC search           : 0.00
% 4.53/1.83  Cooper               : 0.00
% 4.53/1.83  Total                : 1.09
% 4.53/1.83  Index Insertion      : 0.00
% 4.53/1.83  Index Deletion       : 0.00
% 4.53/1.83  Index Matching       : 0.00
% 4.53/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
