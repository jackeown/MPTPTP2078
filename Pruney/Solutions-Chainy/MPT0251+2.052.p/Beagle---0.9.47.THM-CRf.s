%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:53 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 134 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :   74 ( 135 expanded)
%              Number of equality atoms :   50 ( 109 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_42,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_150,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_178,plain,(
    ! [B_49,A_50] : k3_tarski(k2_tarski(B_49,A_50)) = k2_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_150])).

tff(c_32,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_206,plain,(
    ! [B_51,A_52] : k2_xboole_0(B_51,A_52) = k2_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_32])).

tff(c_222,plain,(
    ! [A_52] : k2_xboole_0(k1_xboole_0,A_52) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_10])).

tff(c_502,plain,(
    ! [A_72,B_73] : k2_xboole_0(A_72,k4_xboole_0(B_73,A_72)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_512,plain,(
    ! [B_73] : k4_xboole_0(B_73,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_222])).

tff(c_536,plain,(
    ! [B_74] : k4_xboole_0(B_74,k1_xboole_0) = B_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_512])).

tff(c_20,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_553,plain,(
    ! [B_74] : k5_xboole_0(k1_xboole_0,B_74) = k2_xboole_0(k1_xboole_0,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_20])).

tff(c_567,plain,(
    ! [B_74] : k5_xboole_0(k1_xboole_0,B_74) = B_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_553])).

tff(c_12,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_268,plain,(
    ! [A_56] : k2_xboole_0(k1_xboole_0,A_56) = A_56 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_10])).

tff(c_308,plain,(
    ! [B_7] : k3_xboole_0(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_268])).

tff(c_712,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_729,plain,(
    ! [B_7] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_712])).

tff(c_737,plain,(
    ! [B_7] : k4_xboole_0(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_729])).

tff(c_359,plain,(
    ! [A_61,B_62] : k4_xboole_0(k2_xboole_0(A_61,B_62),B_62) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_368,plain,(
    ! [A_52] : k4_xboole_0(k1_xboole_0,A_52) = k4_xboole_0(A_52,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_359])).

tff(c_740,plain,(
    ! [A_52] : k4_xboole_0(A_52,A_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_368])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_732,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_712])).

tff(c_852,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_732])).

tff(c_24,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1155,plain,(
    ! [A_104,B_105,C_106] :
      ( r1_tarski(k2_tarski(A_104,B_105),C_106)
      | ~ r2_hidden(B_105,C_106)
      | ~ r2_hidden(A_104,C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1680,plain,(
    ! [A_119,C_120] :
      ( r1_tarski(k1_tarski(A_119),C_120)
      | ~ r2_hidden(A_119,C_120)
      | ~ r2_hidden(A_119,C_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1155])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2051,plain,(
    ! [A_127,C_128] :
      ( k3_xboole_0(k1_tarski(A_127),C_128) = k1_tarski(A_127)
      | ~ r2_hidden(A_127,C_128) ) ),
    inference(resolution,[status(thm)],[c_1680,c_14])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2063,plain,(
    ! [A_127,C_128] :
      ( k5_xboole_0(k1_tarski(A_127),k1_tarski(A_127)) = k4_xboole_0(k1_tarski(A_127),C_128)
      | ~ r2_hidden(A_127,C_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2051,c_8])).

tff(c_2090,plain,(
    ! [A_129,C_130] :
      ( k4_xboole_0(k1_tarski(A_129),C_130) = k1_xboole_0
      | ~ r2_hidden(A_129,C_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_2063])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2118,plain,(
    ! [C_130,A_129] :
      ( k2_xboole_0(C_130,k1_tarski(A_129)) = k2_xboole_0(C_130,k1_xboole_0)
      | ~ r2_hidden(A_129,C_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2090,c_16])).

tff(c_2158,plain,(
    ! [C_132,A_133] :
      ( k2_xboole_0(C_132,k1_tarski(A_133)) = C_132
      | ~ r2_hidden(A_133,C_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2118])).

tff(c_184,plain,(
    ! [B_49,A_50] : k2_xboole_0(B_49,A_50) = k2_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_32])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_205,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_40])).

tff(c_2216,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2158,c_205])).

tff(c_2282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:02:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.49  
% 3.22/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.50  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.22/1.50  
% 3.22/1.50  %Foreground sorts:
% 3.22/1.50  
% 3.22/1.50  
% 3.22/1.50  %Background operators:
% 3.22/1.50  
% 3.22/1.50  
% 3.22/1.50  %Foreground operators:
% 3.22/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.22/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.22/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.22/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.22/1.50  
% 3.22/1.51  tff(f_70, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.22/1.51  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.22/1.51  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.22/1.51  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.22/1.51  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.22/1.51  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.22/1.51  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.22/1.51  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.22/1.51  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.22/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.22/1.51  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.22/1.51  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.22/1.51  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.22/1.51  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.22/1.51  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.51  tff(c_22, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.22/1.51  tff(c_150, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.51  tff(c_178, plain, (![B_49, A_50]: (k3_tarski(k2_tarski(B_49, A_50))=k2_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_22, c_150])).
% 3.22/1.51  tff(c_32, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.51  tff(c_206, plain, (![B_51, A_52]: (k2_xboole_0(B_51, A_52)=k2_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_178, c_32])).
% 3.22/1.51  tff(c_222, plain, (![A_52]: (k2_xboole_0(k1_xboole_0, A_52)=A_52)), inference(superposition, [status(thm), theory('equality')], [c_206, c_10])).
% 3.22/1.51  tff(c_502, plain, (![A_72, B_73]: (k2_xboole_0(A_72, k4_xboole_0(B_73, A_72))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.22/1.51  tff(c_512, plain, (![B_73]: (k4_xboole_0(B_73, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_73))), inference(superposition, [status(thm), theory('equality')], [c_502, c_222])).
% 3.22/1.51  tff(c_536, plain, (![B_74]: (k4_xboole_0(B_74, k1_xboole_0)=B_74)), inference(demodulation, [status(thm), theory('equality')], [c_222, c_512])).
% 3.22/1.51  tff(c_20, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.51  tff(c_553, plain, (![B_74]: (k5_xboole_0(k1_xboole_0, B_74)=k2_xboole_0(k1_xboole_0, B_74))), inference(superposition, [status(thm), theory('equality')], [c_536, c_20])).
% 3.22/1.51  tff(c_567, plain, (![B_74]: (k5_xboole_0(k1_xboole_0, B_74)=B_74)), inference(demodulation, [status(thm), theory('equality')], [c_222, c_553])).
% 3.22/1.51  tff(c_12, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.51  tff(c_268, plain, (![A_56]: (k2_xboole_0(k1_xboole_0, A_56)=A_56)), inference(superposition, [status(thm), theory('equality')], [c_206, c_10])).
% 3.22/1.51  tff(c_308, plain, (![B_7]: (k3_xboole_0(k1_xboole_0, B_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_268])).
% 3.22/1.51  tff(c_712, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.51  tff(c_729, plain, (![B_7]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_7))), inference(superposition, [status(thm), theory('equality')], [c_308, c_712])).
% 3.22/1.51  tff(c_737, plain, (![B_7]: (k4_xboole_0(k1_xboole_0, B_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_567, c_729])).
% 3.22/1.51  tff(c_359, plain, (![A_61, B_62]: (k4_xboole_0(k2_xboole_0(A_61, B_62), B_62)=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.22/1.51  tff(c_368, plain, (![A_52]: (k4_xboole_0(k1_xboole_0, A_52)=k4_xboole_0(A_52, A_52))), inference(superposition, [status(thm), theory('equality')], [c_222, c_359])).
% 3.22/1.51  tff(c_740, plain, (![A_52]: (k4_xboole_0(A_52, A_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_737, c_368])).
% 3.22/1.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.51  tff(c_105, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.51  tff(c_109, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_105])).
% 3.22/1.51  tff(c_732, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_109, c_712])).
% 3.22/1.51  tff(c_852, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_740, c_732])).
% 3.22/1.51  tff(c_24, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.22/1.51  tff(c_1155, plain, (![A_104, B_105, C_106]: (r1_tarski(k2_tarski(A_104, B_105), C_106) | ~r2_hidden(B_105, C_106) | ~r2_hidden(A_104, C_106))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.22/1.51  tff(c_1680, plain, (![A_119, C_120]: (r1_tarski(k1_tarski(A_119), C_120) | ~r2_hidden(A_119, C_120) | ~r2_hidden(A_119, C_120))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1155])).
% 3.22/1.51  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.51  tff(c_2051, plain, (![A_127, C_128]: (k3_xboole_0(k1_tarski(A_127), C_128)=k1_tarski(A_127) | ~r2_hidden(A_127, C_128))), inference(resolution, [status(thm)], [c_1680, c_14])).
% 3.22/1.51  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.51  tff(c_2063, plain, (![A_127, C_128]: (k5_xboole_0(k1_tarski(A_127), k1_tarski(A_127))=k4_xboole_0(k1_tarski(A_127), C_128) | ~r2_hidden(A_127, C_128))), inference(superposition, [status(thm), theory('equality')], [c_2051, c_8])).
% 3.22/1.51  tff(c_2090, plain, (![A_129, C_130]: (k4_xboole_0(k1_tarski(A_129), C_130)=k1_xboole_0 | ~r2_hidden(A_129, C_130))), inference(demodulation, [status(thm), theory('equality')], [c_852, c_2063])).
% 3.22/1.51  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.22/1.51  tff(c_2118, plain, (![C_130, A_129]: (k2_xboole_0(C_130, k1_tarski(A_129))=k2_xboole_0(C_130, k1_xboole_0) | ~r2_hidden(A_129, C_130))), inference(superposition, [status(thm), theory('equality')], [c_2090, c_16])).
% 3.22/1.51  tff(c_2158, plain, (![C_132, A_133]: (k2_xboole_0(C_132, k1_tarski(A_133))=C_132 | ~r2_hidden(A_133, C_132))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2118])).
% 3.22/1.51  tff(c_184, plain, (![B_49, A_50]: (k2_xboole_0(B_49, A_50)=k2_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_178, c_32])).
% 3.22/1.51  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.22/1.51  tff(c_205, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_40])).
% 3.22/1.51  tff(c_2216, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2158, c_205])).
% 3.22/1.51  tff(c_2282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_2216])).
% 3.22/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.51  
% 3.22/1.51  Inference rules
% 3.22/1.51  ----------------------
% 3.22/1.51  #Ref     : 0
% 3.22/1.51  #Sup     : 529
% 3.22/1.51  #Fact    : 0
% 3.22/1.51  #Define  : 0
% 3.22/1.51  #Split   : 0
% 3.22/1.51  #Chain   : 0
% 3.22/1.51  #Close   : 0
% 3.22/1.51  
% 3.22/1.51  Ordering : KBO
% 3.22/1.51  
% 3.22/1.51  Simplification rules
% 3.22/1.51  ----------------------
% 3.22/1.51  #Subsume      : 22
% 3.22/1.51  #Demod        : 501
% 3.22/1.51  #Tautology    : 425
% 3.22/1.51  #SimpNegUnit  : 0
% 3.22/1.51  #BackRed      : 6
% 3.22/1.51  
% 3.22/1.51  #Partial instantiations: 0
% 3.22/1.51  #Strategies tried      : 1
% 3.22/1.51  
% 3.22/1.51  Timing (in seconds)
% 3.22/1.51  ----------------------
% 3.22/1.51  Preprocessing        : 0.29
% 3.22/1.51  Parsing              : 0.16
% 3.22/1.51  CNF conversion       : 0.02
% 3.22/1.51  Main loop            : 0.46
% 3.22/1.51  Inferencing          : 0.16
% 3.22/1.51  Reduction            : 0.19
% 3.22/1.51  Demodulation         : 0.16
% 3.22/1.51  BG Simplification    : 0.02
% 3.22/1.51  Subsumption          : 0.06
% 3.22/1.51  Abstraction          : 0.03
% 3.22/1.51  MUC search           : 0.00
% 3.22/1.51  Cooper               : 0.00
% 3.22/1.51  Total                : 0.79
% 3.22/1.51  Index Insertion      : 0.00
% 3.22/1.51  Index Deletion       : 0.00
% 3.22/1.51  Index Matching       : 0.00
% 3.22/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
