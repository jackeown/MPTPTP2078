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
% DateTime   : Thu Dec  3 09:50:50 EST 2020

% Result     : Theorem 8.54s
% Output     : CNFRefutation 8.71s
% Verified   : 
% Statistics : Number of formulae       :   69 (  79 expanded)
%              Number of leaves         :   35 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 (  92 expanded)
%              Number of equality atoms :   34 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_74,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_90,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_64,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1281,plain,(
    ! [A_176,B_177,C_178] :
      ( ~ r2_hidden('#skF_2'(A_176,B_177,C_178),B_177)
      | r2_hidden('#skF_3'(A_176,B_177,C_178),C_178)
      | k4_xboole_0(A_176,B_177) = C_178 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1448,plain,(
    ! [A_197,C_198] :
      ( r2_hidden('#skF_3'(A_197,A_197,C_198),C_198)
      | k4_xboole_0(A_197,A_197) = C_198 ) ),
    inference(resolution,[status(thm)],[c_24,c_1281])).

tff(c_44,plain,(
    ! [A_26] : r1_xboole_0(A_26,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    ! [B_18] : r1_tarski(B_18,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_119,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_123,plain,(
    ! [B_18] : k3_xboole_0(B_18,B_18) = B_18 ),
    inference(resolution,[status(thm)],[c_34,c_119])).

tff(c_382,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r1_xboole_0(A_85,B_86)
      | ~ r2_hidden(C_87,k3_xboole_0(A_85,B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_412,plain,(
    ! [B_90,C_91] :
      ( ~ r1_xboole_0(B_90,B_90)
      | ~ r2_hidden(C_91,B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_382])).

tff(c_416,plain,(
    ! [C_91] : ~ r2_hidden(C_91,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_412])).

tff(c_1472,plain,(
    ! [A_197] : k4_xboole_0(A_197,A_197) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1448,c_416])).

tff(c_356,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_365,plain,(
    ! [B_18] : k5_xboole_0(B_18,B_18) = k4_xboole_0(B_18,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_356])).

tff(c_133,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_tarski(A_52),B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_780,plain,(
    ! [A_125,B_126] :
      ( k3_xboole_0(k1_tarski(A_125),B_126) = k1_tarski(A_125)
      | ~ r2_hidden(A_125,B_126) ) ),
    inference(resolution,[status(thm)],[c_133,c_40])).

tff(c_36,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_802,plain,(
    ! [A_125,B_126] :
      ( k5_xboole_0(k1_tarski(A_125),k1_tarski(A_125)) = k4_xboole_0(k1_tarski(A_125),B_126)
      | ~ r2_hidden(A_125,B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_36])).

tff(c_819,plain,(
    ! [A_125,B_126] :
      ( k4_xboole_0(k1_tarski(A_125),k1_tarski(A_125)) = k4_xboole_0(k1_tarski(A_125),B_126)
      | ~ r2_hidden(A_125,B_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_802])).

tff(c_14273,plain,(
    ! [A_656,B_657] :
      ( k4_xboole_0(k1_tarski(A_656),B_657) = k1_xboole_0
      | ~ r2_hidden(A_656,B_657) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1472,c_819])).

tff(c_42,plain,(
    ! [A_24,B_25] : k2_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14548,plain,(
    ! [B_657,A_656] :
      ( k2_xboole_0(B_657,k1_tarski(A_656)) = k2_xboole_0(B_657,k1_xboole_0)
      | ~ r2_hidden(A_656,B_657) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14273,c_42])).

tff(c_14657,plain,(
    ! [B_658,A_659] :
      ( k2_xboole_0(B_658,k1_tarski(A_659)) = B_658
      | ~ r2_hidden(A_659,B_658) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14548])).

tff(c_46,plain,(
    ! [B_28,A_27] : k2_tarski(B_28,A_27) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_147,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_202,plain,(
    ! [B_64,A_65] : k3_tarski(k2_tarski(B_64,A_65)) = k2_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_147])).

tff(c_60,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_208,plain,(
    ! [B_64,A_65] : k2_xboole_0(B_64,A_65) = k2_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_60])).

tff(c_62,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_228,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_62])).

tff(c_14683,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_14657,c_228])).

tff(c_14736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:01:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.54/3.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.54/3.16  
% 8.54/3.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.54/3.16  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.54/3.16  
% 8.54/3.16  %Foreground sorts:
% 8.54/3.16  
% 8.54/3.16  
% 8.54/3.16  %Background operators:
% 8.54/3.16  
% 8.54/3.16  
% 8.54/3.16  %Foreground operators:
% 8.54/3.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.54/3.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.54/3.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.54/3.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.54/3.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.54/3.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.54/3.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.54/3.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.54/3.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.54/3.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.54/3.16  tff('#skF_5', type, '#skF_5': $i).
% 8.54/3.16  tff('#skF_6', type, '#skF_6': $i).
% 8.54/3.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.54/3.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.54/3.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.54/3.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.54/3.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.54/3.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.54/3.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.54/3.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.54/3.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.54/3.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.54/3.16  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.54/3.16  
% 8.71/3.18  tff(f_95, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 8.71/3.18  tff(f_66, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.71/3.18  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.71/3.18  tff(f_74, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.71/3.18  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.71/3.18  tff(f_70, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.71/3.18  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.71/3.18  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.71/3.18  tff(f_88, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.71/3.18  tff(f_72, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.71/3.18  tff(f_76, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.71/3.18  tff(f_90, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.71/3.18  tff(c_64, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.71/3.18  tff(c_38, plain, (![A_21]: (k2_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.71/3.18  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.71/3.18  tff(c_1281, plain, (![A_176, B_177, C_178]: (~r2_hidden('#skF_2'(A_176, B_177, C_178), B_177) | r2_hidden('#skF_3'(A_176, B_177, C_178), C_178) | k4_xboole_0(A_176, B_177)=C_178)), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.71/3.18  tff(c_1448, plain, (![A_197, C_198]: (r2_hidden('#skF_3'(A_197, A_197, C_198), C_198) | k4_xboole_0(A_197, A_197)=C_198)), inference(resolution, [status(thm)], [c_24, c_1281])).
% 8.71/3.18  tff(c_44, plain, (![A_26]: (r1_xboole_0(A_26, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.71/3.18  tff(c_34, plain, (![B_18]: (r1_tarski(B_18, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.71/3.18  tff(c_119, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.71/3.18  tff(c_123, plain, (![B_18]: (k3_xboole_0(B_18, B_18)=B_18)), inference(resolution, [status(thm)], [c_34, c_119])).
% 8.71/3.18  tff(c_382, plain, (![A_85, B_86, C_87]: (~r1_xboole_0(A_85, B_86) | ~r2_hidden(C_87, k3_xboole_0(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.71/3.18  tff(c_412, plain, (![B_90, C_91]: (~r1_xboole_0(B_90, B_90) | ~r2_hidden(C_91, B_90))), inference(superposition, [status(thm), theory('equality')], [c_123, c_382])).
% 8.71/3.18  tff(c_416, plain, (![C_91]: (~r2_hidden(C_91, k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_412])).
% 8.71/3.18  tff(c_1472, plain, (![A_197]: (k4_xboole_0(A_197, A_197)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1448, c_416])).
% 8.71/3.18  tff(c_356, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.71/3.18  tff(c_365, plain, (![B_18]: (k5_xboole_0(B_18, B_18)=k4_xboole_0(B_18, B_18))), inference(superposition, [status(thm), theory('equality')], [c_123, c_356])).
% 8.71/3.18  tff(c_133, plain, (![A_52, B_53]: (r1_tarski(k1_tarski(A_52), B_53) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.71/3.18  tff(c_40, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.71/3.18  tff(c_780, plain, (![A_125, B_126]: (k3_xboole_0(k1_tarski(A_125), B_126)=k1_tarski(A_125) | ~r2_hidden(A_125, B_126))), inference(resolution, [status(thm)], [c_133, c_40])).
% 8.71/3.18  tff(c_36, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.71/3.18  tff(c_802, plain, (![A_125, B_126]: (k5_xboole_0(k1_tarski(A_125), k1_tarski(A_125))=k4_xboole_0(k1_tarski(A_125), B_126) | ~r2_hidden(A_125, B_126))), inference(superposition, [status(thm), theory('equality')], [c_780, c_36])).
% 8.71/3.18  tff(c_819, plain, (![A_125, B_126]: (k4_xboole_0(k1_tarski(A_125), k1_tarski(A_125))=k4_xboole_0(k1_tarski(A_125), B_126) | ~r2_hidden(A_125, B_126))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_802])).
% 8.71/3.18  tff(c_14273, plain, (![A_656, B_657]: (k4_xboole_0(k1_tarski(A_656), B_657)=k1_xboole_0 | ~r2_hidden(A_656, B_657))), inference(demodulation, [status(thm), theory('equality')], [c_1472, c_819])).
% 8.71/3.18  tff(c_42, plain, (![A_24, B_25]: (k2_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.71/3.18  tff(c_14548, plain, (![B_657, A_656]: (k2_xboole_0(B_657, k1_tarski(A_656))=k2_xboole_0(B_657, k1_xboole_0) | ~r2_hidden(A_656, B_657))), inference(superposition, [status(thm), theory('equality')], [c_14273, c_42])).
% 8.71/3.18  tff(c_14657, plain, (![B_658, A_659]: (k2_xboole_0(B_658, k1_tarski(A_659))=B_658 | ~r2_hidden(A_659, B_658))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14548])).
% 8.71/3.18  tff(c_46, plain, (![B_28, A_27]: (k2_tarski(B_28, A_27)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.71/3.18  tff(c_147, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.71/3.18  tff(c_202, plain, (![B_64, A_65]: (k3_tarski(k2_tarski(B_64, A_65))=k2_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_46, c_147])).
% 8.71/3.18  tff(c_60, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.71/3.18  tff(c_208, plain, (![B_64, A_65]: (k2_xboole_0(B_64, A_65)=k2_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_202, c_60])).
% 8.71/3.18  tff(c_62, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.71/3.18  tff(c_228, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_208, c_62])).
% 8.71/3.18  tff(c_14683, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_14657, c_228])).
% 8.71/3.18  tff(c_14736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_14683])).
% 8.71/3.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.71/3.18  
% 8.71/3.18  Inference rules
% 8.71/3.18  ----------------------
% 8.71/3.18  #Ref     : 0
% 8.71/3.18  #Sup     : 3794
% 8.71/3.18  #Fact    : 0
% 8.71/3.18  #Define  : 0
% 8.71/3.18  #Split   : 4
% 8.71/3.18  #Chain   : 0
% 8.71/3.18  #Close   : 0
% 8.71/3.18  
% 8.71/3.18  Ordering : KBO
% 8.71/3.18  
% 8.71/3.18  Simplification rules
% 8.71/3.18  ----------------------
% 8.71/3.18  #Subsume      : 1886
% 8.71/3.18  #Demod        : 1734
% 8.71/3.18  #Tautology    : 847
% 8.71/3.18  #SimpNegUnit  : 66
% 8.71/3.18  #BackRed      : 6
% 8.71/3.18  
% 8.71/3.18  #Partial instantiations: 0
% 8.71/3.18  #Strategies tried      : 1
% 8.71/3.18  
% 8.71/3.18  Timing (in seconds)
% 8.71/3.18  ----------------------
% 8.71/3.18  Preprocessing        : 0.34
% 8.71/3.18  Parsing              : 0.18
% 8.71/3.18  CNF conversion       : 0.02
% 8.71/3.18  Main loop            : 2.02
% 8.71/3.18  Inferencing          : 0.57
% 8.71/3.18  Reduction            : 0.64
% 8.71/3.18  Demodulation         : 0.47
% 8.71/3.18  BG Simplification    : 0.06
% 8.71/3.18  Subsumption          : 0.64
% 8.71/3.18  Abstraction          : 0.09
% 8.71/3.18  MUC search           : 0.00
% 8.71/3.18  Cooper               : 0.00
% 8.71/3.18  Total                : 2.39
% 8.71/3.18  Index Insertion      : 0.00
% 8.71/3.18  Index Deletion       : 0.00
% 8.71/3.18  Index Matching       : 0.00
% 8.71/3.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
