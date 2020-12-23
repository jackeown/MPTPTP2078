%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:49 EST 2020

% Result     : Theorem 10.12s
% Output     : CNFRefutation 10.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 390 expanded)
%              Number of leaves         :   32 ( 148 expanded)
%              Depth                    :   18
%              Number of atoms          :   72 ( 384 expanded)
%              Number of equality atoms :   57 ( 365 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(k2_xboole_0(C,k2_tarski(A,B)),k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_40,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [C_39,A_37,B_38] :
      ( k4_xboole_0(C_39,k2_tarski(A_37,B_38)) = C_39
      | r2_hidden(B_38,C_39)
      | r2_hidden(A_37,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_702,plain,(
    ! [A_78,B_79,C_80] : k5_xboole_0(k5_xboole_0(A_78,B_79),C_80) = k5_xboole_0(A_78,k5_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k2_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3248,plain,(
    ! [A_145,B_146] : k5_xboole_0(A_145,k5_xboole_0(B_146,k2_xboole_0(A_145,B_146))) = k3_xboole_0(A_145,B_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_20])).

tff(c_66,plain,(
    ! [B_43,A_44] : k5_xboole_0(B_43,A_44) = k5_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    ! [A_44] : k5_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_16])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_562,plain,(
    ! [A_74,B_75] : k5_xboole_0(k5_xboole_0(A_74,B_75),k2_xboole_0(A_74,B_75)) = k3_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_622,plain,(
    ! [A_13] : k5_xboole_0(A_13,k2_xboole_0(A_13,k1_xboole_0)) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_562])).

tff(c_632,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_622])).

tff(c_745,plain,(
    ! [A_13,C_80] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_80)) = k5_xboole_0(k1_xboole_0,C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_702])).

tff(c_792,plain,(
    ! [A_13,C_80] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_80)) = C_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_745])).

tff(c_3305,plain,(
    ! [B_146,A_145] : k5_xboole_0(B_146,k2_xboole_0(A_145,B_146)) = k5_xboole_0(A_145,k3_xboole_0(A_145,B_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3248,c_792])).

tff(c_3414,plain,(
    ! [B_147,A_148] : k5_xboole_0(B_147,k2_xboole_0(A_148,B_147)) = k4_xboole_0(A_148,B_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3305])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_832,plain,(
    ! [A_82,C_83] : k5_xboole_0(A_82,k5_xboole_0(A_82,C_83)) = C_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_745])).

tff(c_887,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_832])).

tff(c_3553,plain,(
    ! [A_149,B_150] : k5_xboole_0(k2_xboole_0(A_149,B_150),k4_xboole_0(A_149,B_150)) = B_150 ),
    inference(superposition,[status(thm),theory(equality)],[c_3414,c_887])).

tff(c_3610,plain,(
    ! [A_149,B_150] : k5_xboole_0(k2_xboole_0(A_149,B_150),B_150) = k4_xboole_0(A_149,B_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_3553,c_792])).

tff(c_3670,plain,(
    ! [A_1,B_2] : k5_xboole_0(k2_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3553])).

tff(c_14,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4413,plain,(
    ! [A_161,B_162] : k5_xboole_0(k2_xboole_0(A_161,B_162),B_162) = k4_xboole_0(A_161,B_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_3553,c_792])).

tff(c_4522,plain,(
    ! [A_11,B_12] : k5_xboole_0(k2_xboole_0(A_11,B_12),k4_xboole_0(B_12,A_11)) = k4_xboole_0(A_11,k4_xboole_0(B_12,A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_4413])).

tff(c_4564,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3670,c_4522])).

tff(c_3471,plain,(
    ! [B_147,A_148] : k5_xboole_0(B_147,k4_xboole_0(A_148,B_147)) = k2_xboole_0(A_148,B_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_3414,c_792])).

tff(c_3807,plain,(
    ! [B_153,A_154] : k5_xboole_0(B_153,k2_xboole_0(B_153,A_154)) = k4_xboole_0(A_154,B_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3414])).

tff(c_11363,plain,(
    ! [B_231,A_232] : k5_xboole_0(B_231,k4_xboole_0(A_232,B_231)) = k2_xboole_0(B_231,A_232) ),
    inference(superposition,[status(thm),theory(equality)],[c_3807,c_792])).

tff(c_22,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),k5_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_263,plain,(
    ! [A_54,B_55] :
      ( k2_xboole_0(A_54,B_55) = B_55
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_271,plain,(
    ! [A_19,B_20] : k2_xboole_0(k4_xboole_0(A_19,B_20),k5_xboole_0(A_19,B_20)) = k5_xboole_0(A_19,B_20) ),
    inference(resolution,[status(thm)],[c_22,c_263])).

tff(c_11430,plain,(
    ! [B_231,A_232] : k2_xboole_0(k4_xboole_0(B_231,k4_xboole_0(A_232,B_231)),k2_xboole_0(B_231,A_232)) = k5_xboole_0(B_231,k4_xboole_0(A_232,B_231)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11363,c_271])).

tff(c_16119,plain,(
    ! [B_270,A_271] : k2_xboole_0(B_270,k2_xboole_0(B_270,A_271)) = k2_xboole_0(A_271,B_270) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4564,c_3471,c_11430])).

tff(c_3528,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3414])).

tff(c_4959,plain,(
    ! [A_175,A_173,B_174] : k5_xboole_0(A_175,k5_xboole_0(A_173,B_174)) = k5_xboole_0(A_173,k5_xboole_0(B_174,A_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_702])).

tff(c_6490,plain,(
    ! [A_192,A_193] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_192,A_193)) = k5_xboole_0(A_193,A_192) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_4959])).

tff(c_6623,plain,(
    ! [B_2,A_1] : k5_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3528,c_6490])).

tff(c_6735,plain,(
    ! [B_2,A_1] : k5_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6623])).

tff(c_16167,plain,(
    ! [A_271,B_270] : k5_xboole_0(k2_xboole_0(A_271,B_270),B_270) = k4_xboole_0(k2_xboole_0(B_270,A_271),B_270) ),
    inference(superposition,[status(thm),theory(equality)],[c_16119,c_6735])).

tff(c_20813,plain,(
    ! [B_301,A_302] : k4_xboole_0(k2_xboole_0(B_301,A_302),B_301) = k4_xboole_0(A_302,B_301) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3610,c_16167])).

tff(c_20982,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_20813])).

tff(c_36,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_21516,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20982,c_36])).

tff(c_21764,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_21516])).

tff(c_21768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_21764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.12/4.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.20/4.43  
% 10.20/4.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.20/4.43  %$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.20/4.43  
% 10.20/4.43  %Foreground sorts:
% 10.20/4.43  
% 10.20/4.43  
% 10.20/4.43  %Background operators:
% 10.20/4.43  
% 10.20/4.43  
% 10.20/4.43  %Foreground operators:
% 10.20/4.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.20/4.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.20/4.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.20/4.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.20/4.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.20/4.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.20/4.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.20/4.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.20/4.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.20/4.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.20/4.43  tff('#skF_2', type, '#skF_2': $i).
% 10.20/4.43  tff('#skF_3', type, '#skF_3': $i).
% 10.20/4.43  tff('#skF_1', type, '#skF_1': $i).
% 10.20/4.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.20/4.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.20/4.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.20/4.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.20/4.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.20/4.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.20/4.43  
% 10.22/4.45  tff(f_80, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(k2_xboole_0(C, k2_tarski(A, B)), k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 10.22/4.45  tff(f_69, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 10.22/4.45  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.22/4.45  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.22/4.45  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.22/4.45  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.22/4.45  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.22/4.45  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 10.22/4.45  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.22/4.45  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.22/4.45  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.22/4.45  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 10.22/4.45  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.22/4.45  tff(c_40, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.22/4.45  tff(c_38, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.22/4.45  tff(c_34, plain, (![C_39, A_37, B_38]: (k4_xboole_0(C_39, k2_tarski(A_37, B_38))=C_39 | r2_hidden(B_38, C_39) | r2_hidden(A_37, C_39))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.22/4.45  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.22/4.45  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.22/4.45  tff(c_702, plain, (![A_78, B_79, C_80]: (k5_xboole_0(k5_xboole_0(A_78, B_79), C_80)=k5_xboole_0(A_78, k5_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.22/4.45  tff(c_20, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k2_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.22/4.45  tff(c_3248, plain, (![A_145, B_146]: (k5_xboole_0(A_145, k5_xboole_0(B_146, k2_xboole_0(A_145, B_146)))=k3_xboole_0(A_145, B_146))), inference(superposition, [status(thm), theory('equality')], [c_702, c_20])).
% 10.22/4.45  tff(c_66, plain, (![B_43, A_44]: (k5_xboole_0(B_43, A_44)=k5_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.22/4.45  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.22/4.45  tff(c_82, plain, (![A_44]: (k5_xboole_0(k1_xboole_0, A_44)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_66, c_16])).
% 10.22/4.45  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.22/4.45  tff(c_10, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.22/4.45  tff(c_562, plain, (![A_74, B_75]: (k5_xboole_0(k5_xboole_0(A_74, B_75), k2_xboole_0(A_74, B_75))=k3_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.22/4.45  tff(c_622, plain, (![A_13]: (k5_xboole_0(A_13, k2_xboole_0(A_13, k1_xboole_0))=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_562])).
% 10.22/4.45  tff(c_632, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_622])).
% 10.22/4.45  tff(c_745, plain, (![A_13, C_80]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_80))=k5_xboole_0(k1_xboole_0, C_80))), inference(superposition, [status(thm), theory('equality')], [c_632, c_702])).
% 10.22/4.45  tff(c_792, plain, (![A_13, C_80]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_80))=C_80)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_745])).
% 10.22/4.45  tff(c_3305, plain, (![B_146, A_145]: (k5_xboole_0(B_146, k2_xboole_0(A_145, B_146))=k5_xboole_0(A_145, k3_xboole_0(A_145, B_146)))), inference(superposition, [status(thm), theory('equality')], [c_3248, c_792])).
% 10.22/4.45  tff(c_3414, plain, (![B_147, A_148]: (k5_xboole_0(B_147, k2_xboole_0(A_148, B_147))=k4_xboole_0(A_148, B_147))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3305])).
% 10.22/4.45  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.22/4.45  tff(c_832, plain, (![A_82, C_83]: (k5_xboole_0(A_82, k5_xboole_0(A_82, C_83))=C_83)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_745])).
% 10.22/4.45  tff(c_887, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_832])).
% 10.22/4.45  tff(c_3553, plain, (![A_149, B_150]: (k5_xboole_0(k2_xboole_0(A_149, B_150), k4_xboole_0(A_149, B_150))=B_150)), inference(superposition, [status(thm), theory('equality')], [c_3414, c_887])).
% 10.22/4.45  tff(c_3610, plain, (![A_149, B_150]: (k5_xboole_0(k2_xboole_0(A_149, B_150), B_150)=k4_xboole_0(A_149, B_150))), inference(superposition, [status(thm), theory('equality')], [c_3553, c_792])).
% 10.22/4.45  tff(c_3670, plain, (![A_1, B_2]: (k5_xboole_0(k2_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3553])).
% 10.22/4.45  tff(c_14, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.22/4.45  tff(c_4413, plain, (![A_161, B_162]: (k5_xboole_0(k2_xboole_0(A_161, B_162), B_162)=k4_xboole_0(A_161, B_162))), inference(superposition, [status(thm), theory('equality')], [c_3553, c_792])).
% 10.22/4.45  tff(c_4522, plain, (![A_11, B_12]: (k5_xboole_0(k2_xboole_0(A_11, B_12), k4_xboole_0(B_12, A_11))=k4_xboole_0(A_11, k4_xboole_0(B_12, A_11)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_4413])).
% 10.22/4.45  tff(c_4564, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(B_12, A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_3670, c_4522])).
% 10.22/4.45  tff(c_3471, plain, (![B_147, A_148]: (k5_xboole_0(B_147, k4_xboole_0(A_148, B_147))=k2_xboole_0(A_148, B_147))), inference(superposition, [status(thm), theory('equality')], [c_3414, c_792])).
% 10.22/4.45  tff(c_3807, plain, (![B_153, A_154]: (k5_xboole_0(B_153, k2_xboole_0(B_153, A_154))=k4_xboole_0(A_154, B_153))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3414])).
% 10.22/4.45  tff(c_11363, plain, (![B_231, A_232]: (k5_xboole_0(B_231, k4_xboole_0(A_232, B_231))=k2_xboole_0(B_231, A_232))), inference(superposition, [status(thm), theory('equality')], [c_3807, c_792])).
% 10.22/4.45  tff(c_22, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), k5_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.22/4.45  tff(c_263, plain, (![A_54, B_55]: (k2_xboole_0(A_54, B_55)=B_55 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.22/4.45  tff(c_271, plain, (![A_19, B_20]: (k2_xboole_0(k4_xboole_0(A_19, B_20), k5_xboole_0(A_19, B_20))=k5_xboole_0(A_19, B_20))), inference(resolution, [status(thm)], [c_22, c_263])).
% 10.22/4.45  tff(c_11430, plain, (![B_231, A_232]: (k2_xboole_0(k4_xboole_0(B_231, k4_xboole_0(A_232, B_231)), k2_xboole_0(B_231, A_232))=k5_xboole_0(B_231, k4_xboole_0(A_232, B_231)))), inference(superposition, [status(thm), theory('equality')], [c_11363, c_271])).
% 10.22/4.45  tff(c_16119, plain, (![B_270, A_271]: (k2_xboole_0(B_270, k2_xboole_0(B_270, A_271))=k2_xboole_0(A_271, B_270))), inference(demodulation, [status(thm), theory('equality')], [c_4564, c_3471, c_11430])).
% 10.22/4.45  tff(c_3528, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3414])).
% 10.22/4.45  tff(c_4959, plain, (![A_175, A_173, B_174]: (k5_xboole_0(A_175, k5_xboole_0(A_173, B_174))=k5_xboole_0(A_173, k5_xboole_0(B_174, A_175)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_702])).
% 10.22/4.45  tff(c_6490, plain, (![A_192, A_193]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_192, A_193))=k5_xboole_0(A_193, A_192))), inference(superposition, [status(thm), theory('equality')], [c_82, c_4959])).
% 10.22/4.45  tff(c_6623, plain, (![B_2, A_1]: (k5_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_3528, c_6490])).
% 10.22/4.45  tff(c_6735, plain, (![B_2, A_1]: (k5_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_6623])).
% 10.22/4.45  tff(c_16167, plain, (![A_271, B_270]: (k5_xboole_0(k2_xboole_0(A_271, B_270), B_270)=k4_xboole_0(k2_xboole_0(B_270, A_271), B_270))), inference(superposition, [status(thm), theory('equality')], [c_16119, c_6735])).
% 10.22/4.45  tff(c_20813, plain, (![B_301, A_302]: (k4_xboole_0(k2_xboole_0(B_301, A_302), B_301)=k4_xboole_0(A_302, B_301))), inference(demodulation, [status(thm), theory('equality')], [c_3610, c_16167])).
% 10.22/4.45  tff(c_20982, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_20813])).
% 10.22/4.45  tff(c_36, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.22/4.45  tff(c_21516, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20982, c_36])).
% 10.22/4.45  tff(c_21764, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_21516])).
% 10.22/4.45  tff(c_21768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_21764])).
% 10.22/4.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.22/4.45  
% 10.22/4.45  Inference rules
% 10.22/4.45  ----------------------
% 10.22/4.45  #Ref     : 0
% 10.22/4.45  #Sup     : 5666
% 10.22/4.45  #Fact    : 0
% 10.22/4.45  #Define  : 0
% 10.22/4.45  #Split   : 1
% 10.22/4.45  #Chain   : 0
% 10.22/4.45  #Close   : 0
% 10.22/4.45  
% 10.22/4.45  Ordering : KBO
% 10.22/4.45  
% 10.22/4.45  Simplification rules
% 10.22/4.45  ----------------------
% 10.22/4.45  #Subsume      : 113
% 10.22/4.45  #Demod        : 7492
% 10.22/4.45  #Tautology    : 2935
% 10.22/4.45  #SimpNegUnit  : 1
% 10.22/4.45  #BackRed      : 9
% 10.22/4.45  
% 10.22/4.45  #Partial instantiations: 0
% 10.22/4.45  #Strategies tried      : 1
% 10.22/4.45  
% 10.22/4.45  Timing (in seconds)
% 10.22/4.45  ----------------------
% 10.22/4.45  Preprocessing        : 0.31
% 10.22/4.45  Parsing              : 0.17
% 10.22/4.45  CNF conversion       : 0.02
% 10.22/4.45  Main loop            : 3.37
% 10.22/4.45  Inferencing          : 0.59
% 10.22/4.45  Reduction            : 2.07
% 10.22/4.45  Demodulation         : 1.88
% 10.22/4.45  BG Simplification    : 0.09
% 10.22/4.45  Subsumption          : 0.46
% 10.22/4.45  Abstraction          : 0.14
% 10.22/4.45  MUC search           : 0.00
% 10.22/4.45  Cooper               : 0.00
% 10.22/4.45  Total                : 3.71
% 10.22/4.45  Index Insertion      : 0.00
% 10.22/4.45  Index Deletion       : 0.00
% 10.22/4.45  Index Matching       : 0.00
% 10.22/4.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
