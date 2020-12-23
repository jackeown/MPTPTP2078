%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:46 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 130 expanded)
%              Number of leaves         :   39 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 171 expanded)
%              Number of equality atoms :   38 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_83,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_105,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_70,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    ! [A_24] : k2_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,(
    ! [A_27] : r1_tarski(k1_xboole_0,A_27) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_178,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = A_69
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_185,plain,(
    ! [A_27] : k3_xboole_0(k1_xboole_0,A_27) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_178])).

tff(c_248,plain,(
    ! [D_78,B_79,A_80] :
      ( r2_hidden(D_78,B_79)
      | ~ r2_hidden(D_78,k3_xboole_0(A_80,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_260,plain,(
    ! [D_81,A_82] :
      ( r2_hidden(D_81,A_82)
      | ~ r2_hidden(D_81,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_248])).

tff(c_264,plain,(
    ! [A_82] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_82)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_260])).

tff(c_265,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_578,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_4'(A_105,B_106),A_105)
      | r1_xboole_0(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_604,plain,(
    ! [A_105,B_106] :
      ( ~ v1_xboole_0(A_105)
      | r1_xboole_0(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_578,c_4])).

tff(c_52,plain,(
    ! [B_33,A_32] : k2_tarski(B_33,A_32) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_150,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_278,plain,(
    ! [B_86,A_87] : k3_tarski(k2_tarski(B_86,A_87)) = k2_xboole_0(A_87,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_150])).

tff(c_66,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_305,plain,(
    ! [B_88,A_89] : k2_xboole_0(B_88,A_89) = k2_xboole_0(A_89,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_66])).

tff(c_321,plain,(
    ! [A_89] : k2_xboole_0(k1_xboole_0,A_89) = A_89 ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_42])).

tff(c_668,plain,(
    ! [A_116,B_117] :
      ( k4_xboole_0(k2_xboole_0(A_116,B_117),B_117) = A_116
      | ~ r1_xboole_0(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_710,plain,(
    ! [A_118] :
      ( k4_xboole_0(A_118,A_118) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_668])).

tff(c_716,plain,(
    ! [B_106] :
      ( k4_xboole_0(B_106,B_106) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_604,c_710])).

tff(c_720,plain,(
    ! [B_106] : k4_xboole_0(B_106,B_106) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_716])).

tff(c_38,plain,(
    ! [B_21] : r1_tarski(B_21,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_186,plain,(
    ! [B_21] : k3_xboole_0(B_21,B_21) = B_21 ),
    inference(resolution,[status(thm)],[c_38,c_178])).

tff(c_423,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k4_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_432,plain,(
    ! [B_21] : k5_xboole_0(B_21,B_21) = k4_xboole_0(B_21,B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_423])).

tff(c_722,plain,(
    ! [B_21] : k5_xboole_0(B_21,B_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_432])).

tff(c_239,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k1_tarski(A_76),B_77)
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1101,plain,(
    ! [A_157,B_158] :
      ( k3_xboole_0(k1_tarski(A_157),B_158) = k1_tarski(A_157)
      | ~ r2_hidden(A_157,B_158) ) ),
    inference(resolution,[status(thm)],[c_239,c_44])).

tff(c_40,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1110,plain,(
    ! [A_157,B_158] :
      ( k5_xboole_0(k1_tarski(A_157),k1_tarski(A_157)) = k4_xboole_0(k1_tarski(A_157),B_158)
      | ~ r2_hidden(A_157,B_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1101,c_40])).

tff(c_1137,plain,(
    ! [A_159,B_160] :
      ( k4_xboole_0(k1_tarski(A_159),B_160) = k1_xboole_0
      | ~ r2_hidden(A_159,B_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_1110])).

tff(c_48,plain,(
    ! [A_28,B_29] : k2_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1151,plain,(
    ! [B_160,A_159] :
      ( k2_xboole_0(B_160,k1_tarski(A_159)) = k2_xboole_0(B_160,k1_xboole_0)
      | ~ r2_hidden(A_159,B_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1137,c_48])).

tff(c_1172,plain,(
    ! [B_161,A_162] :
      ( k2_xboole_0(B_161,k1_tarski(A_162)) = B_161
      | ~ r2_hidden(A_162,B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1151])).

tff(c_284,plain,(
    ! [B_86,A_87] : k2_xboole_0(B_86,A_87) = k2_xboole_0(A_87,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_66])).

tff(c_68,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_304,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_68])).

tff(c_1185,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1172,c_304])).

tff(c_1222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1185])).

tff(c_1225,plain,(
    ! [A_163] : r2_hidden('#skF_1'(k1_xboole_0),A_163) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_1248,plain,(
    ! [A_163] : ~ v1_xboole_0(A_163) ),
    inference(resolution,[status(thm)],[c_1225,c_4])).

tff(c_136,plain,(
    ! [B_59,A_60] :
      ( ~ r2_hidden(B_59,A_60)
      | ~ r2_hidden(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_141,plain,(
    ! [A_3] :
      ( ~ r2_hidden(A_3,'#skF_1'(A_3))
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_1246,plain,(
    v1_xboole_0('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1225,c_141])).

tff(c_1270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1248,c_1246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 09:40:59 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.50  
% 3.23/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.23/1.50  
% 3.23/1.50  %Foreground sorts:
% 3.23/1.50  
% 3.23/1.50  
% 3.23/1.50  %Background operators:
% 3.23/1.50  
% 3.23/1.50  
% 3.23/1.50  %Foreground operators:
% 3.23/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.23/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.23/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.23/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.23/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.23/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.23/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.23/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.23/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.23/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.23/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.23/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.23/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.23/1.50  
% 3.23/1.52  tff(f_110, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.23/1.52  tff(f_77, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.23/1.52  tff(f_36, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.23/1.52  tff(f_83, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.23/1.52  tff(f_81, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.23/1.52  tff(f_45, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.23/1.52  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.23/1.52  tff(f_91, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.23/1.52  tff(f_105, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.23/1.52  tff(f_89, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 3.23/1.52  tff(f_73, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.23/1.52  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.23/1.52  tff(f_103, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.23/1.52  tff(f_85, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.23/1.52  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.23/1.52  tff(c_70, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.23/1.52  tff(c_42, plain, (![A_24]: (k2_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.23/1.52  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.23/1.52  tff(c_46, plain, (![A_27]: (r1_tarski(k1_xboole_0, A_27))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.52  tff(c_178, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=A_69 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.23/1.52  tff(c_185, plain, (![A_27]: (k3_xboole_0(k1_xboole_0, A_27)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_178])).
% 3.23/1.52  tff(c_248, plain, (![D_78, B_79, A_80]: (r2_hidden(D_78, B_79) | ~r2_hidden(D_78, k3_xboole_0(A_80, B_79)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.23/1.52  tff(c_260, plain, (![D_81, A_82]: (r2_hidden(D_81, A_82) | ~r2_hidden(D_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_185, c_248])).
% 3.23/1.52  tff(c_264, plain, (![A_82]: (r2_hidden('#skF_1'(k1_xboole_0), A_82) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_260])).
% 3.23/1.52  tff(c_265, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_264])).
% 3.23/1.52  tff(c_578, plain, (![A_105, B_106]: (r2_hidden('#skF_4'(A_105, B_106), A_105) | r1_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.23/1.52  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.23/1.52  tff(c_604, plain, (![A_105, B_106]: (~v1_xboole_0(A_105) | r1_xboole_0(A_105, B_106))), inference(resolution, [status(thm)], [c_578, c_4])).
% 3.23/1.52  tff(c_52, plain, (![B_33, A_32]: (k2_tarski(B_33, A_32)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.23/1.52  tff(c_150, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.52  tff(c_278, plain, (![B_86, A_87]: (k3_tarski(k2_tarski(B_86, A_87))=k2_xboole_0(A_87, B_86))), inference(superposition, [status(thm), theory('equality')], [c_52, c_150])).
% 3.23/1.52  tff(c_66, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.52  tff(c_305, plain, (![B_88, A_89]: (k2_xboole_0(B_88, A_89)=k2_xboole_0(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_278, c_66])).
% 3.23/1.52  tff(c_321, plain, (![A_89]: (k2_xboole_0(k1_xboole_0, A_89)=A_89)), inference(superposition, [status(thm), theory('equality')], [c_305, c_42])).
% 3.23/1.52  tff(c_668, plain, (![A_116, B_117]: (k4_xboole_0(k2_xboole_0(A_116, B_117), B_117)=A_116 | ~r1_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.23/1.52  tff(c_710, plain, (![A_118]: (k4_xboole_0(A_118, A_118)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_118))), inference(superposition, [status(thm), theory('equality')], [c_321, c_668])).
% 3.23/1.52  tff(c_716, plain, (![B_106]: (k4_xboole_0(B_106, B_106)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_604, c_710])).
% 3.23/1.52  tff(c_720, plain, (![B_106]: (k4_xboole_0(B_106, B_106)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_265, c_716])).
% 3.23/1.52  tff(c_38, plain, (![B_21]: (r1_tarski(B_21, B_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.23/1.52  tff(c_186, plain, (![B_21]: (k3_xboole_0(B_21, B_21)=B_21)), inference(resolution, [status(thm)], [c_38, c_178])).
% 3.23/1.52  tff(c_423, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k4_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.52  tff(c_432, plain, (![B_21]: (k5_xboole_0(B_21, B_21)=k4_xboole_0(B_21, B_21))), inference(superposition, [status(thm), theory('equality')], [c_186, c_423])).
% 3.23/1.52  tff(c_722, plain, (![B_21]: (k5_xboole_0(B_21, B_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_720, c_432])).
% 3.23/1.52  tff(c_239, plain, (![A_76, B_77]: (r1_tarski(k1_tarski(A_76), B_77) | ~r2_hidden(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.23/1.52  tff(c_44, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.23/1.52  tff(c_1101, plain, (![A_157, B_158]: (k3_xboole_0(k1_tarski(A_157), B_158)=k1_tarski(A_157) | ~r2_hidden(A_157, B_158))), inference(resolution, [status(thm)], [c_239, c_44])).
% 3.23/1.52  tff(c_40, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.52  tff(c_1110, plain, (![A_157, B_158]: (k5_xboole_0(k1_tarski(A_157), k1_tarski(A_157))=k4_xboole_0(k1_tarski(A_157), B_158) | ~r2_hidden(A_157, B_158))), inference(superposition, [status(thm), theory('equality')], [c_1101, c_40])).
% 3.23/1.52  tff(c_1137, plain, (![A_159, B_160]: (k4_xboole_0(k1_tarski(A_159), B_160)=k1_xboole_0 | ~r2_hidden(A_159, B_160))), inference(demodulation, [status(thm), theory('equality')], [c_722, c_1110])).
% 3.23/1.52  tff(c_48, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.23/1.52  tff(c_1151, plain, (![B_160, A_159]: (k2_xboole_0(B_160, k1_tarski(A_159))=k2_xboole_0(B_160, k1_xboole_0) | ~r2_hidden(A_159, B_160))), inference(superposition, [status(thm), theory('equality')], [c_1137, c_48])).
% 3.23/1.52  tff(c_1172, plain, (![B_161, A_162]: (k2_xboole_0(B_161, k1_tarski(A_162))=B_161 | ~r2_hidden(A_162, B_161))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1151])).
% 3.23/1.52  tff(c_284, plain, (![B_86, A_87]: (k2_xboole_0(B_86, A_87)=k2_xboole_0(A_87, B_86))), inference(superposition, [status(thm), theory('equality')], [c_278, c_66])).
% 3.23/1.52  tff(c_68, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.23/1.52  tff(c_304, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_284, c_68])).
% 3.23/1.52  tff(c_1185, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1172, c_304])).
% 3.23/1.52  tff(c_1222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1185])).
% 3.23/1.52  tff(c_1225, plain, (![A_163]: (r2_hidden('#skF_1'(k1_xboole_0), A_163))), inference(splitRight, [status(thm)], [c_264])).
% 3.23/1.52  tff(c_1248, plain, (![A_163]: (~v1_xboole_0(A_163))), inference(resolution, [status(thm)], [c_1225, c_4])).
% 3.23/1.52  tff(c_136, plain, (![B_59, A_60]: (~r2_hidden(B_59, A_60) | ~r2_hidden(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.23/1.52  tff(c_141, plain, (![A_3]: (~r2_hidden(A_3, '#skF_1'(A_3)) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_136])).
% 3.23/1.52  tff(c_1246, plain, (v1_xboole_0('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_1225, c_141])).
% 3.23/1.52  tff(c_1270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1248, c_1246])).
% 3.23/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.52  
% 3.23/1.52  Inference rules
% 3.23/1.52  ----------------------
% 3.23/1.52  #Ref     : 0
% 3.23/1.52  #Sup     : 270
% 3.23/1.52  #Fact    : 0
% 3.23/1.52  #Define  : 0
% 3.23/1.52  #Split   : 2
% 3.23/1.52  #Chain   : 0
% 3.23/1.52  #Close   : 0
% 3.23/1.52  
% 3.23/1.52  Ordering : KBO
% 3.23/1.52  
% 3.23/1.52  Simplification rules
% 3.23/1.52  ----------------------
% 3.23/1.52  #Subsume      : 38
% 3.23/1.52  #Demod        : 87
% 3.23/1.52  #Tautology    : 153
% 3.23/1.52  #SimpNegUnit  : 6
% 3.23/1.52  #BackRed      : 9
% 3.23/1.52  
% 3.23/1.52  #Partial instantiations: 0
% 3.23/1.52  #Strategies tried      : 1
% 3.23/1.52  
% 3.23/1.52  Timing (in seconds)
% 3.23/1.52  ----------------------
% 3.23/1.52  Preprocessing        : 0.33
% 3.23/1.52  Parsing              : 0.17
% 3.23/1.52  CNF conversion       : 0.02
% 3.23/1.52  Main loop            : 0.41
% 3.23/1.52  Inferencing          : 0.15
% 3.23/1.52  Reduction            : 0.13
% 3.23/1.52  Demodulation         : 0.10
% 3.23/1.52  BG Simplification    : 0.02
% 3.23/1.52  Subsumption          : 0.08
% 3.23/1.52  Abstraction          : 0.02
% 3.23/1.52  MUC search           : 0.00
% 3.23/1.52  Cooper               : 0.00
% 3.23/1.52  Total                : 0.77
% 3.23/1.52  Index Insertion      : 0.00
% 3.23/1.52  Index Deletion       : 0.00
% 3.23/1.52  Index Matching       : 0.00
% 3.23/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
