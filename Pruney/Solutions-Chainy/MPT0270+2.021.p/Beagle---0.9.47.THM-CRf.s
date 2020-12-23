%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:55 EST 2020

% Result     : Theorem 6.22s
% Output     : CNFRefutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 150 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :   92 ( 166 expanded)
%              Number of equality atoms :   54 ( 102 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_82,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_22,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(k1_tarski(A_53),B_54)
      | r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_328,plain,(
    ! [A_81,B_82,C_83] :
      ( ~ r1_xboole_0(A_81,B_82)
      | ~ r2_hidden(C_83,k3_xboole_0(A_81,B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_362,plain,(
    ! [A_87,B_88] :
      ( ~ r1_xboole_0(A_87,B_88)
      | k3_xboole_0(A_87,B_88) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_328])).

tff(c_1227,plain,(
    ! [A_149,B_150] :
      ( k3_xboole_0(k1_tarski(A_149),B_150) = k1_xboole_0
      | r2_hidden(A_149,B_150) ) ),
    inference(resolution,[status(thm)],[c_40,c_362])).

tff(c_14,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1242,plain,(
    ! [A_149,B_150] :
      ( k5_xboole_0(k1_tarski(A_149),k1_xboole_0) = k4_xboole_0(k1_tarski(A_149),B_150)
      | r2_hidden(A_149,B_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1227,c_14])).

tff(c_7282,plain,(
    ! [A_235,B_236] :
      ( k4_xboole_0(k1_tarski(A_235),B_236) = k1_tarski(A_235)
      | r2_hidden(A_235,B_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1242])).

tff(c_46,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_163,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_7352,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7282,c_163])).

tff(c_7400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_7352])).

tff(c_7401,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_18,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7457,plain,(
    ! [A_242,B_243] :
      ( k3_xboole_0(A_242,B_243) = A_242
      | ~ r1_tarski(A_242,B_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7462,plain,(
    ! [A_244] : k3_xboole_0(k1_xboole_0,A_244) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_7457])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_7467,plain,(
    ! [A_244] : k3_xboole_0(A_244,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7462,c_2])).

tff(c_7608,plain,(
    ! [A_258,B_259] : k5_xboole_0(A_258,k3_xboole_0(A_258,B_259)) = k4_xboole_0(A_258,B_259) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7621,plain,(
    ! [A_244] : k5_xboole_0(A_244,k1_xboole_0) = k4_xboole_0(A_244,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7467,c_7608])).

tff(c_7683,plain,(
    ! [A_261] : k4_xboole_0(A_261,k1_xboole_0) = A_261 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7621])).

tff(c_20,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7693,plain,(
    ! [A_261] : k4_xboole_0(A_261,A_261) = k3_xboole_0(A_261,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7683,c_20])).

tff(c_7703,plain,(
    ! [A_261] : k4_xboole_0(A_261,A_261) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7467,c_7693])).

tff(c_7402,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7562,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7402,c_50])).

tff(c_7585,plain,(
    ! [A_256,B_257] : k4_xboole_0(A_256,k4_xboole_0(A_256,B_257)) = k3_xboole_0(A_256,B_257) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7600,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7562,c_7585])).

tff(c_7606,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7600])).

tff(c_7706,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7703,c_7606])).

tff(c_7743,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7706,c_14])).

tff(c_7749,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7743])).

tff(c_42,plain,(
    ! [B_56,A_55] :
      ( ~ r2_hidden(B_56,A_55)
      | k4_xboole_0(A_55,k1_tarski(B_56)) != A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7757,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7749,c_42])).

tff(c_7764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7401,c_7757])).

tff(c_7765,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_7897,plain,(
    ! [A_270,B_271] :
      ( k3_xboole_0(A_270,B_271) = A_270
      | ~ r1_tarski(A_270,B_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7902,plain,(
    ! [A_272] : k3_xboole_0(k1_xboole_0,A_272) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_7897])).

tff(c_7907,plain,(
    ! [A_272] : k3_xboole_0(A_272,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7902,c_2])).

tff(c_8035,plain,(
    ! [A_286,B_287] : k5_xboole_0(A_286,k3_xboole_0(A_286,B_287)) = k4_xboole_0(A_286,B_287) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8048,plain,(
    ! [A_272] : k5_xboole_0(A_272,k1_xboole_0) = k4_xboole_0(A_272,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7907,c_8035])).

tff(c_8068,plain,(
    ! [A_272] : k4_xboole_0(A_272,k1_xboole_0) = A_272 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8048])).

tff(c_8150,plain,(
    ! [A_293,B_294] : k4_xboole_0(A_293,k4_xboole_0(A_293,B_294)) = k3_xboole_0(A_293,B_294) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8169,plain,(
    ! [A_272] : k4_xboole_0(A_272,A_272) = k3_xboole_0(A_272,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8068,c_8150])).

tff(c_8186,plain,(
    ! [A_272] : k4_xboole_0(A_272,A_272) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7907,c_8169])).

tff(c_7766,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7978,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7766,c_52])).

tff(c_8182,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7978,c_8150])).

tff(c_8189,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8182])).

tff(c_8207,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8186,c_8189])).

tff(c_8280,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8207,c_14])).

tff(c_8286,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8280])).

tff(c_8294,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8286,c_42])).

tff(c_8307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7765,c_8294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:51:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.22/2.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.22/2.41  
% 6.22/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.22/2.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 6.22/2.42  
% 6.22/2.42  %Foreground sorts:
% 6.22/2.42  
% 6.22/2.42  
% 6.22/2.42  %Background operators:
% 6.22/2.42  
% 6.22/2.42  
% 6.22/2.42  %Foreground operators:
% 6.22/2.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.22/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.22/2.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.22/2.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.22/2.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.22/2.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.22/2.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.22/2.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.22/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.22/2.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.22/2.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.22/2.42  tff('#skF_5', type, '#skF_5': $i).
% 6.22/2.42  tff('#skF_6', type, '#skF_6': $i).
% 6.22/2.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.22/2.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.22/2.42  tff('#skF_3', type, '#skF_3': $i).
% 6.22/2.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.22/2.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.22/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.22/2.42  tff('#skF_4', type, '#skF_4': $i).
% 6.22/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.22/2.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.22/2.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.22/2.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.22/2.42  
% 6.32/2.43  tff(f_97, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 6.32/2.43  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.32/2.43  tff(f_86, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.32/2.43  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.32/2.43  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.32/2.43  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.32/2.43  tff(f_61, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.32/2.43  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.32/2.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.32/2.43  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.32/2.43  tff(f_91, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.32/2.43  tff(c_48, plain, (~r2_hidden('#skF_3', '#skF_4') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.32/2.43  tff(c_82, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 6.32/2.43  tff(c_22, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.32/2.43  tff(c_40, plain, (![A_53, B_54]: (r1_xboole_0(k1_tarski(A_53), B_54) | r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.32/2.43  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.32/2.43  tff(c_328, plain, (![A_81, B_82, C_83]: (~r1_xboole_0(A_81, B_82) | ~r2_hidden(C_83, k3_xboole_0(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.32/2.43  tff(c_362, plain, (![A_87, B_88]: (~r1_xboole_0(A_87, B_88) | k3_xboole_0(A_87, B_88)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_328])).
% 6.32/2.43  tff(c_1227, plain, (![A_149, B_150]: (k3_xboole_0(k1_tarski(A_149), B_150)=k1_xboole_0 | r2_hidden(A_149, B_150))), inference(resolution, [status(thm)], [c_40, c_362])).
% 6.32/2.43  tff(c_14, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.32/2.43  tff(c_1242, plain, (![A_149, B_150]: (k5_xboole_0(k1_tarski(A_149), k1_xboole_0)=k4_xboole_0(k1_tarski(A_149), B_150) | r2_hidden(A_149, B_150))), inference(superposition, [status(thm), theory('equality')], [c_1227, c_14])).
% 6.32/2.43  tff(c_7282, plain, (![A_235, B_236]: (k4_xboole_0(k1_tarski(A_235), B_236)=k1_tarski(A_235) | r2_hidden(A_235, B_236))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1242])).
% 6.32/2.43  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.32/2.43  tff(c_163, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 6.32/2.43  tff(c_7352, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7282, c_163])).
% 6.32/2.43  tff(c_7400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_7352])).
% 6.32/2.43  tff(c_7401, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_46])).
% 6.32/2.43  tff(c_18, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.32/2.43  tff(c_7457, plain, (![A_242, B_243]: (k3_xboole_0(A_242, B_243)=A_242 | ~r1_tarski(A_242, B_243))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.32/2.43  tff(c_7462, plain, (![A_244]: (k3_xboole_0(k1_xboole_0, A_244)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_7457])).
% 6.32/2.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.32/2.43  tff(c_7467, plain, (![A_244]: (k3_xboole_0(A_244, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7462, c_2])).
% 6.32/2.43  tff(c_7608, plain, (![A_258, B_259]: (k5_xboole_0(A_258, k3_xboole_0(A_258, B_259))=k4_xboole_0(A_258, B_259))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.32/2.43  tff(c_7621, plain, (![A_244]: (k5_xboole_0(A_244, k1_xboole_0)=k4_xboole_0(A_244, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7467, c_7608])).
% 6.32/2.43  tff(c_7683, plain, (![A_261]: (k4_xboole_0(A_261, k1_xboole_0)=A_261)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_7621])).
% 6.32/2.43  tff(c_20, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.32/2.43  tff(c_7693, plain, (![A_261]: (k4_xboole_0(A_261, A_261)=k3_xboole_0(A_261, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7683, c_20])).
% 6.32/2.43  tff(c_7703, plain, (![A_261]: (k4_xboole_0(A_261, A_261)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7467, c_7693])).
% 6.32/2.43  tff(c_7402, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 6.32/2.43  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.32/2.43  tff(c_7562, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7402, c_50])).
% 6.32/2.43  tff(c_7585, plain, (![A_256, B_257]: (k4_xboole_0(A_256, k4_xboole_0(A_256, B_257))=k3_xboole_0(A_256, B_257))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.32/2.43  tff(c_7600, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7562, c_7585])).
% 6.32/2.43  tff(c_7606, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7600])).
% 6.32/2.43  tff(c_7706, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7703, c_7606])).
% 6.32/2.43  tff(c_7743, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7706, c_14])).
% 6.32/2.43  tff(c_7749, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_7743])).
% 6.32/2.43  tff(c_42, plain, (![B_56, A_55]: (~r2_hidden(B_56, A_55) | k4_xboole_0(A_55, k1_tarski(B_56))!=A_55)), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.32/2.43  tff(c_7757, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7749, c_42])).
% 6.32/2.43  tff(c_7764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7401, c_7757])).
% 6.32/2.43  tff(c_7765, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 6.32/2.43  tff(c_7897, plain, (![A_270, B_271]: (k3_xboole_0(A_270, B_271)=A_270 | ~r1_tarski(A_270, B_271))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.32/2.43  tff(c_7902, plain, (![A_272]: (k3_xboole_0(k1_xboole_0, A_272)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_7897])).
% 6.32/2.43  tff(c_7907, plain, (![A_272]: (k3_xboole_0(A_272, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7902, c_2])).
% 6.32/2.43  tff(c_8035, plain, (![A_286, B_287]: (k5_xboole_0(A_286, k3_xboole_0(A_286, B_287))=k4_xboole_0(A_286, B_287))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.32/2.43  tff(c_8048, plain, (![A_272]: (k5_xboole_0(A_272, k1_xboole_0)=k4_xboole_0(A_272, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7907, c_8035])).
% 6.32/2.43  tff(c_8068, plain, (![A_272]: (k4_xboole_0(A_272, k1_xboole_0)=A_272)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8048])).
% 6.32/2.43  tff(c_8150, plain, (![A_293, B_294]: (k4_xboole_0(A_293, k4_xboole_0(A_293, B_294))=k3_xboole_0(A_293, B_294))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.32/2.43  tff(c_8169, plain, (![A_272]: (k4_xboole_0(A_272, A_272)=k3_xboole_0(A_272, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8068, c_8150])).
% 6.32/2.43  tff(c_8186, plain, (![A_272]: (k4_xboole_0(A_272, A_272)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7907, c_8169])).
% 6.32/2.43  tff(c_7766, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 6.32/2.43  tff(c_52, plain, (~r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.32/2.43  tff(c_7978, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7766, c_52])).
% 6.32/2.43  tff(c_8182, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7978, c_8150])).
% 6.32/2.43  tff(c_8189, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8182])).
% 6.32/2.43  tff(c_8207, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8186, c_8189])).
% 6.32/2.43  tff(c_8280, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8207, c_14])).
% 6.32/2.43  tff(c_8286, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8280])).
% 6.32/2.43  tff(c_8294, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8286, c_42])).
% 6.32/2.43  tff(c_8307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7765, c_8294])).
% 6.32/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.32/2.43  
% 6.32/2.43  Inference rules
% 6.32/2.43  ----------------------
% 6.32/2.43  #Ref     : 0
% 6.32/2.43  #Sup     : 2025
% 6.32/2.43  #Fact    : 0
% 6.32/2.43  #Define  : 0
% 6.32/2.43  #Split   : 5
% 6.32/2.43  #Chain   : 0
% 6.32/2.43  #Close   : 0
% 6.32/2.43  
% 6.32/2.43  Ordering : KBO
% 6.32/2.43  
% 6.32/2.43  Simplification rules
% 6.32/2.43  ----------------------
% 6.32/2.43  #Subsume      : 197
% 6.32/2.43  #Demod        : 2168
% 6.32/2.43  #Tautology    : 1291
% 6.32/2.43  #SimpNegUnit  : 18
% 6.32/2.43  #BackRed      : 4
% 6.32/2.43  
% 6.32/2.43  #Partial instantiations: 0
% 6.32/2.43  #Strategies tried      : 1
% 6.32/2.43  
% 6.32/2.43  Timing (in seconds)
% 6.32/2.43  ----------------------
% 6.32/2.44  Preprocessing        : 0.35
% 6.32/2.44  Parsing              : 0.18
% 6.32/2.44  CNF conversion       : 0.03
% 6.32/2.44  Main loop            : 1.27
% 6.32/2.44  Inferencing          : 0.35
% 6.32/2.44  Reduction            : 0.66
% 6.32/2.44  Demodulation         : 0.57
% 6.32/2.44  BG Simplification    : 0.04
% 6.32/2.44  Subsumption          : 0.16
% 6.32/2.44  Abstraction          : 0.07
% 6.32/2.44  MUC search           : 0.00
% 6.32/2.44  Cooper               : 0.00
% 6.32/2.44  Total                : 1.66
% 6.32/2.44  Index Insertion      : 0.00
% 6.32/2.44  Index Deletion       : 0.00
% 6.32/2.44  Index Matching       : 0.00
% 6.32/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
