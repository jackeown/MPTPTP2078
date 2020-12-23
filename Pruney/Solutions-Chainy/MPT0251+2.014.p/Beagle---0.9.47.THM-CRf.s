%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:48 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   75 (  96 expanded)
%              Number of leaves         :   35 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 137 expanded)
%              Number of equality atoms :   41 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_62,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_76,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_76,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_48,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1413,plain,(
    ! [A_165,B_166,C_167] :
      ( r2_hidden('#skF_3'(A_165,B_166,C_167),A_165)
      | r2_hidden('#skF_4'(A_165,B_166,C_167),C_167)
      | k4_xboole_0(A_165,B_166) = C_167 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ r2_hidden('#skF_3'(A_9,B_10,C_11),B_10)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),C_11)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1502,plain,(
    ! [A_168,C_169] :
      ( r2_hidden('#skF_4'(A_168,A_168,C_169),C_169)
      | k4_xboole_0(A_168,A_168) = C_169 ) ),
    inference(resolution,[status(thm)],[c_1413,c_36])).

tff(c_52,plain,(
    ! [A_22] : r1_tarski(k1_xboole_0,A_22) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_173,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_180,plain,(
    ! [A_22] : k3_xboole_0(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_173])).

tff(c_482,plain,(
    ! [D_79,B_80,A_81] :
      ( r2_hidden(D_79,B_80)
      | ~ r2_hidden(D_79,k3_xboole_0(A_81,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_491,plain,(
    ! [D_79,A_22] :
      ( r2_hidden(D_79,A_22)
      | ~ r2_hidden(D_79,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_482])).

tff(c_1548,plain,(
    ! [A_168,A_22] :
      ( r2_hidden('#skF_4'(A_168,A_168,k1_xboole_0),A_22)
      | k4_xboole_0(A_168,A_168) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1502,c_491])).

tff(c_1551,plain,(
    ! [A_170,A_171] :
      ( r2_hidden('#skF_4'(A_170,A_170,k1_xboole_0),A_171)
      | k4_xboole_0(A_170,A_170) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1502,c_491])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1668,plain,(
    ! [A_174,B_175] :
      ( ~ r2_hidden('#skF_4'(A_174,A_174,k1_xboole_0),B_175)
      | k4_xboole_0(A_174,A_174) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1551,c_24])).

tff(c_1701,plain,(
    ! [A_168] : k4_xboole_0(A_168,A_168) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1548,c_1668])).

tff(c_44,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_181,plain,(
    ! [B_16] : k3_xboole_0(B_16,B_16) = B_16 ),
    inference(resolution,[status(thm)],[c_44,c_173])).

tff(c_506,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_518,plain,(
    ! [B_16] : k5_xboole_0(B_16,B_16) = k4_xboole_0(B_16,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_506])).

tff(c_58,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_883,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_tarski(k2_tarski(A_122,B_123),C_124)
      | ~ r2_hidden(B_123,C_124)
      | ~ r2_hidden(A_122,C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_931,plain,(
    ! [A_128,C_129] :
      ( r1_tarski(k1_tarski(A_128),C_129)
      | ~ r2_hidden(A_128,C_129)
      | ~ r2_hidden(A_128,C_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_883])).

tff(c_50,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_948,plain,(
    ! [A_130,C_131] :
      ( k3_xboole_0(k1_tarski(A_130),C_131) = k1_tarski(A_130)
      | ~ r2_hidden(A_130,C_131) ) ),
    inference(resolution,[status(thm)],[c_931,c_50])).

tff(c_46,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_963,plain,(
    ! [A_130,C_131] :
      ( k5_xboole_0(k1_tarski(A_130),k1_tarski(A_130)) = k4_xboole_0(k1_tarski(A_130),C_131)
      | ~ r2_hidden(A_130,C_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_948,c_46])).

tff(c_1001,plain,(
    ! [A_130,C_131] :
      ( k4_xboole_0(k1_tarski(A_130),k1_tarski(A_130)) = k4_xboole_0(k1_tarski(A_130),C_131)
      | ~ r2_hidden(A_130,C_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_963])).

tff(c_1967,plain,(
    ! [A_185,C_186] :
      ( k4_xboole_0(k1_tarski(A_185),C_186) = k1_xboole_0
      | ~ r2_hidden(A_185,C_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1701,c_1001])).

tff(c_54,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1987,plain,(
    ! [C_186,A_185] :
      ( k2_xboole_0(C_186,k1_tarski(A_185)) = k2_xboole_0(C_186,k1_xboole_0)
      | ~ r2_hidden(A_185,C_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1967,c_54])).

tff(c_2011,plain,(
    ! [C_187,A_188] :
      ( k2_xboole_0(C_187,k1_tarski(A_188)) = C_187
      | ~ r2_hidden(A_188,C_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1987])).

tff(c_56,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_267,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_303,plain,(
    ! [B_60,A_61] : k3_tarski(k2_tarski(B_60,A_61)) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_267])).

tff(c_66,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_309,plain,(
    ! [B_60,A_61] : k2_xboole_0(B_60,A_61) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_66])).

tff(c_74,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_330,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_74])).

tff(c_2021,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2011,c_330])).

tff(c_2058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2021])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:57:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.58  
% 3.39/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.59  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 3.39/1.59  
% 3.39/1.59  %Foreground sorts:
% 3.39/1.59  
% 3.39/1.59  
% 3.39/1.59  %Background operators:
% 3.39/1.59  
% 3.39/1.59  
% 3.39/1.59  %Foreground operators:
% 3.39/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.39/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.39/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.39/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.39/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.39/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.39/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.39/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.39/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.39/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.39/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.39/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.39/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.39/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.39/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.39/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.39/1.59  
% 3.39/1.60  tff(f_87, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.39/1.60  tff(f_56, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.39/1.60  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.39/1.60  tff(f_62, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.39/1.60  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.39/1.60  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.39/1.60  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.39/1.60  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.39/1.60  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.39/1.60  tff(f_82, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.39/1.60  tff(f_64, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.39/1.60  tff(f_66, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.39/1.60  tff(f_76, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.39/1.60  tff(c_76, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.39/1.60  tff(c_48, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.39/1.60  tff(c_1413, plain, (![A_165, B_166, C_167]: (r2_hidden('#skF_3'(A_165, B_166, C_167), A_165) | r2_hidden('#skF_4'(A_165, B_166, C_167), C_167) | k4_xboole_0(A_165, B_166)=C_167)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.39/1.60  tff(c_36, plain, (![A_9, B_10, C_11]: (~r2_hidden('#skF_3'(A_9, B_10, C_11), B_10) | r2_hidden('#skF_4'(A_9, B_10, C_11), C_11) | k4_xboole_0(A_9, B_10)=C_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.39/1.60  tff(c_1502, plain, (![A_168, C_169]: (r2_hidden('#skF_4'(A_168, A_168, C_169), C_169) | k4_xboole_0(A_168, A_168)=C_169)), inference(resolution, [status(thm)], [c_1413, c_36])).
% 3.39/1.60  tff(c_52, plain, (![A_22]: (r1_tarski(k1_xboole_0, A_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.39/1.60  tff(c_173, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.39/1.60  tff(c_180, plain, (![A_22]: (k3_xboole_0(k1_xboole_0, A_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_173])).
% 3.39/1.60  tff(c_482, plain, (![D_79, B_80, A_81]: (r2_hidden(D_79, B_80) | ~r2_hidden(D_79, k3_xboole_0(A_81, B_80)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.39/1.60  tff(c_491, plain, (![D_79, A_22]: (r2_hidden(D_79, A_22) | ~r2_hidden(D_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_180, c_482])).
% 3.39/1.60  tff(c_1548, plain, (![A_168, A_22]: (r2_hidden('#skF_4'(A_168, A_168, k1_xboole_0), A_22) | k4_xboole_0(A_168, A_168)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1502, c_491])).
% 3.39/1.60  tff(c_1551, plain, (![A_170, A_171]: (r2_hidden('#skF_4'(A_170, A_170, k1_xboole_0), A_171) | k4_xboole_0(A_170, A_170)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1502, c_491])).
% 3.39/1.60  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.39/1.60  tff(c_1668, plain, (![A_174, B_175]: (~r2_hidden('#skF_4'(A_174, A_174, k1_xboole_0), B_175) | k4_xboole_0(A_174, A_174)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1551, c_24])).
% 3.39/1.60  tff(c_1701, plain, (![A_168]: (k4_xboole_0(A_168, A_168)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1548, c_1668])).
% 3.39/1.60  tff(c_44, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.39/1.60  tff(c_181, plain, (![B_16]: (k3_xboole_0(B_16, B_16)=B_16)), inference(resolution, [status(thm)], [c_44, c_173])).
% 3.39/1.60  tff(c_506, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.39/1.60  tff(c_518, plain, (![B_16]: (k5_xboole_0(B_16, B_16)=k4_xboole_0(B_16, B_16))), inference(superposition, [status(thm), theory('equality')], [c_181, c_506])).
% 3.39/1.60  tff(c_58, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.39/1.60  tff(c_883, plain, (![A_122, B_123, C_124]: (r1_tarski(k2_tarski(A_122, B_123), C_124) | ~r2_hidden(B_123, C_124) | ~r2_hidden(A_122, C_124))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.39/1.60  tff(c_931, plain, (![A_128, C_129]: (r1_tarski(k1_tarski(A_128), C_129) | ~r2_hidden(A_128, C_129) | ~r2_hidden(A_128, C_129))), inference(superposition, [status(thm), theory('equality')], [c_58, c_883])).
% 3.39/1.60  tff(c_50, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.39/1.60  tff(c_948, plain, (![A_130, C_131]: (k3_xboole_0(k1_tarski(A_130), C_131)=k1_tarski(A_130) | ~r2_hidden(A_130, C_131))), inference(resolution, [status(thm)], [c_931, c_50])).
% 3.39/1.60  tff(c_46, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.39/1.60  tff(c_963, plain, (![A_130, C_131]: (k5_xboole_0(k1_tarski(A_130), k1_tarski(A_130))=k4_xboole_0(k1_tarski(A_130), C_131) | ~r2_hidden(A_130, C_131))), inference(superposition, [status(thm), theory('equality')], [c_948, c_46])).
% 3.39/1.60  tff(c_1001, plain, (![A_130, C_131]: (k4_xboole_0(k1_tarski(A_130), k1_tarski(A_130))=k4_xboole_0(k1_tarski(A_130), C_131) | ~r2_hidden(A_130, C_131))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_963])).
% 3.39/1.60  tff(c_1967, plain, (![A_185, C_186]: (k4_xboole_0(k1_tarski(A_185), C_186)=k1_xboole_0 | ~r2_hidden(A_185, C_186))), inference(demodulation, [status(thm), theory('equality')], [c_1701, c_1001])).
% 3.39/1.60  tff(c_54, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.39/1.60  tff(c_1987, plain, (![C_186, A_185]: (k2_xboole_0(C_186, k1_tarski(A_185))=k2_xboole_0(C_186, k1_xboole_0) | ~r2_hidden(A_185, C_186))), inference(superposition, [status(thm), theory('equality')], [c_1967, c_54])).
% 3.39/1.60  tff(c_2011, plain, (![C_187, A_188]: (k2_xboole_0(C_187, k1_tarski(A_188))=C_187 | ~r2_hidden(A_188, C_187))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1987])).
% 3.39/1.60  tff(c_56, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.39/1.60  tff(c_267, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.39/1.60  tff(c_303, plain, (![B_60, A_61]: (k3_tarski(k2_tarski(B_60, A_61))=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_56, c_267])).
% 3.39/1.60  tff(c_66, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.39/1.60  tff(c_309, plain, (![B_60, A_61]: (k2_xboole_0(B_60, A_61)=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_303, c_66])).
% 3.39/1.60  tff(c_74, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.39/1.60  tff(c_330, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_309, c_74])).
% 3.39/1.60  tff(c_2021, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2011, c_330])).
% 3.39/1.60  tff(c_2058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_2021])).
% 3.39/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.60  
% 3.39/1.60  Inference rules
% 3.39/1.60  ----------------------
% 3.39/1.60  #Ref     : 0
% 3.39/1.60  #Sup     : 463
% 3.39/1.60  #Fact    : 0
% 3.39/1.60  #Define  : 0
% 3.39/1.60  #Split   : 1
% 3.39/1.60  #Chain   : 0
% 3.39/1.60  #Close   : 0
% 3.39/1.60  
% 3.39/1.60  Ordering : KBO
% 3.39/1.60  
% 3.39/1.60  Simplification rules
% 3.39/1.60  ----------------------
% 3.39/1.60  #Subsume      : 84
% 3.39/1.60  #Demod        : 138
% 3.39/1.60  #Tautology    : 217
% 3.39/1.60  #SimpNegUnit  : 0
% 3.39/1.60  #BackRed      : 9
% 3.39/1.60  
% 3.39/1.60  #Partial instantiations: 0
% 3.39/1.60  #Strategies tried      : 1
% 3.39/1.60  
% 3.39/1.60  Timing (in seconds)
% 3.39/1.60  ----------------------
% 3.39/1.60  Preprocessing        : 0.32
% 3.39/1.60  Parsing              : 0.16
% 3.39/1.60  CNF conversion       : 0.02
% 3.39/1.60  Main loop            : 0.51
% 3.39/1.60  Inferencing          : 0.18
% 3.39/1.60  Reduction            : 0.17
% 3.39/1.60  Demodulation         : 0.13
% 3.39/1.60  BG Simplification    : 0.03
% 3.39/1.60  Subsumption          : 0.10
% 3.39/1.60  Abstraction          : 0.03
% 3.39/1.60  MUC search           : 0.00
% 3.39/1.60  Cooper               : 0.00
% 3.39/1.60  Total                : 0.86
% 3.39/1.60  Index Insertion      : 0.00
% 3.39/1.60  Index Deletion       : 0.00
% 3.39/1.60  Index Matching       : 0.00
% 3.39/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
