%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:15 EST 2020

% Result     : Theorem 6.63s
% Output     : CNFRefutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 115 expanded)
%              Number of leaves         :   30 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :   81 ( 130 expanded)
%              Number of equality atoms :   48 (  86 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_42,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_451,plain,(
    ! [A_71,B_72] : k4_xboole_0(k2_xboole_0(A_71,B_72),B_72) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_461,plain,(
    ! [A_71] : k4_xboole_0(A_71,k1_xboole_0) = k2_xboole_0(A_71,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_18])).

tff(c_480,plain,(
    ! [A_71] : k2_xboole_0(A_71,k1_xboole_0) = A_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_461])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_139,plain,(
    ! [A_42] : k3_xboole_0(k1_xboole_0,A_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_130])).

tff(c_157,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_139])).

tff(c_298,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_307,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k4_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_298])).

tff(c_322,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_307])).

tff(c_137,plain,(
    ! [A_9] : k3_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_130])).

tff(c_313,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_298])).

tff(c_393,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_313])).

tff(c_22,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_224,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_240,plain,(
    ! [B_47,A_48] : k3_tarski(k2_tarski(B_47,A_48)) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_224])).

tff(c_30,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_246,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_30])).

tff(c_492,plain,(
    ! [A_76] : k2_xboole_0(A_76,k1_xboole_0) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_461])).

tff(c_520,plain,(
    ! [B_77] : k2_xboole_0(k1_xboole_0,B_77) = B_77 ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_492])).

tff(c_20,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_530,plain,(
    ! [B_77] : k4_xboole_0(k1_xboole_0,B_77) = k4_xboole_0(B_77,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_20])).

tff(c_562,plain,(
    ! [B_77] : k4_xboole_0(B_77,B_77) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_530])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_138,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_130])).

tff(c_310,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_298])).

tff(c_583,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_310])).

tff(c_630,plain,(
    ! [A_84,B_85,C_86] :
      ( r1_tarski(k2_tarski(A_84,B_85),C_86)
      | ~ r2_hidden(B_85,C_86)
      | ~ r2_hidden(A_84,C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1604,plain,(
    ! [A_112,B_113,C_114] :
      ( k3_xboole_0(k2_tarski(A_112,B_113),C_114) = k2_tarski(A_112,B_113)
      | ~ r2_hidden(B_113,C_114)
      | ~ r2_hidden(A_112,C_114) ) ),
    inference(resolution,[status(thm)],[c_630,c_12])).

tff(c_4291,plain,(
    ! [C_146,A_147,B_148] :
      ( k3_xboole_0(C_146,k2_tarski(A_147,B_148)) = k2_tarski(A_147,B_148)
      | ~ r2_hidden(B_148,C_146)
      | ~ r2_hidden(A_147,C_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1604,c_2])).

tff(c_319,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_298])).

tff(c_4301,plain,(
    ! [A_147,B_148,C_146] :
      ( k5_xboole_0(k2_tarski(A_147,B_148),k2_tarski(A_147,B_148)) = k4_xboole_0(k2_tarski(A_147,B_148),C_146)
      | ~ r2_hidden(B_148,C_146)
      | ~ r2_hidden(A_147,C_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4291,c_319])).

tff(c_9200,plain,(
    ! [A_200,B_201,C_202] :
      ( k4_xboole_0(k2_tarski(A_200,B_201),C_202) = k1_xboole_0
      | ~ r2_hidden(B_201,C_202)
      | ~ r2_hidden(A_200,C_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_4301])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9316,plain,(
    ! [C_202,A_200,B_201] :
      ( k2_xboole_0(C_202,k2_tarski(A_200,B_201)) = k2_xboole_0(C_202,k1_xboole_0)
      | ~ r2_hidden(B_201,C_202)
      | ~ r2_hidden(A_200,C_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9200,c_16])).

tff(c_9841,plain,(
    ! [C_210,A_211,B_212] :
      ( k2_xboole_0(C_210,k2_tarski(A_211,B_212)) = C_210
      | ~ r2_hidden(B_212,C_210)
      | ~ r2_hidden(A_211,C_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_9316])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_263,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_38])).

tff(c_10010,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9841,c_263])).

tff(c_10113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_10010])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:45:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.63/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.63/2.72  
% 6.63/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.63/2.73  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.63/2.73  
% 6.63/2.73  %Foreground sorts:
% 6.63/2.73  
% 6.63/2.73  
% 6.63/2.73  %Background operators:
% 6.63/2.73  
% 6.63/2.73  
% 6.63/2.73  %Foreground operators:
% 6.63/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.63/2.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.63/2.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.63/2.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.63/2.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.63/2.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.63/2.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.63/2.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.63/2.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.63/2.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.63/2.73  tff('#skF_2', type, '#skF_2': $i).
% 6.63/2.73  tff('#skF_3', type, '#skF_3': $i).
% 6.63/2.73  tff('#skF_1', type, '#skF_1': $i).
% 6.63/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.63/2.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.63/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.63/2.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.63/2.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.63/2.73  
% 6.90/2.74  tff(f_70, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 6.90/2.74  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.90/2.74  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.90/2.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.90/2.74  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.90/2.74  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.90/2.74  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.90/2.74  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.90/2.74  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.90/2.74  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.90/2.74  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.90/2.74  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.90/2.74  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.90/2.74  tff(c_40, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.90/2.74  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.90/2.74  tff(c_451, plain, (![A_71, B_72]: (k4_xboole_0(k2_xboole_0(A_71, B_72), B_72)=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.90/2.74  tff(c_461, plain, (![A_71]: (k4_xboole_0(A_71, k1_xboole_0)=k2_xboole_0(A_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_451, c_18])).
% 6.90/2.74  tff(c_480, plain, (![A_71]: (k2_xboole_0(A_71, k1_xboole_0)=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_461])).
% 6.90/2.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.90/2.74  tff(c_14, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.90/2.74  tff(c_130, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.90/2.74  tff(c_139, plain, (![A_42]: (k3_xboole_0(k1_xboole_0, A_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_130])).
% 6.90/2.74  tff(c_157, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_139])).
% 6.90/2.74  tff(c_298, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.90/2.74  tff(c_307, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k4_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_157, c_298])).
% 6.90/2.74  tff(c_322, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_307])).
% 6.90/2.74  tff(c_137, plain, (![A_9]: (k3_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_130])).
% 6.90/2.74  tff(c_313, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_9))), inference(superposition, [status(thm), theory('equality')], [c_137, c_298])).
% 6.90/2.74  tff(c_393, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_322, c_313])).
% 6.90/2.74  tff(c_22, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.90/2.74  tff(c_224, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.90/2.74  tff(c_240, plain, (![B_47, A_48]: (k3_tarski(k2_tarski(B_47, A_48))=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_22, c_224])).
% 6.90/2.74  tff(c_30, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.90/2.74  tff(c_246, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_240, c_30])).
% 6.90/2.74  tff(c_492, plain, (![A_76]: (k2_xboole_0(A_76, k1_xboole_0)=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_461])).
% 6.90/2.74  tff(c_520, plain, (![B_77]: (k2_xboole_0(k1_xboole_0, B_77)=B_77)), inference(superposition, [status(thm), theory('equality')], [c_246, c_492])).
% 6.90/2.74  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.90/2.74  tff(c_530, plain, (![B_77]: (k4_xboole_0(k1_xboole_0, B_77)=k4_xboole_0(B_77, B_77))), inference(superposition, [status(thm), theory('equality')], [c_520, c_20])).
% 6.90/2.74  tff(c_562, plain, (![B_77]: (k4_xboole_0(B_77, B_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_393, c_530])).
% 6.90/2.74  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.90/2.74  tff(c_138, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_130])).
% 6.90/2.74  tff(c_310, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_138, c_298])).
% 6.90/2.74  tff(c_583, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_562, c_310])).
% 6.90/2.74  tff(c_630, plain, (![A_84, B_85, C_86]: (r1_tarski(k2_tarski(A_84, B_85), C_86) | ~r2_hidden(B_85, C_86) | ~r2_hidden(A_84, C_86))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.90/2.74  tff(c_12, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.90/2.74  tff(c_1604, plain, (![A_112, B_113, C_114]: (k3_xboole_0(k2_tarski(A_112, B_113), C_114)=k2_tarski(A_112, B_113) | ~r2_hidden(B_113, C_114) | ~r2_hidden(A_112, C_114))), inference(resolution, [status(thm)], [c_630, c_12])).
% 6.90/2.74  tff(c_4291, plain, (![C_146, A_147, B_148]: (k3_xboole_0(C_146, k2_tarski(A_147, B_148))=k2_tarski(A_147, B_148) | ~r2_hidden(B_148, C_146) | ~r2_hidden(A_147, C_146))), inference(superposition, [status(thm), theory('equality')], [c_1604, c_2])).
% 6.90/2.74  tff(c_319, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_298])).
% 6.90/2.74  tff(c_4301, plain, (![A_147, B_148, C_146]: (k5_xboole_0(k2_tarski(A_147, B_148), k2_tarski(A_147, B_148))=k4_xboole_0(k2_tarski(A_147, B_148), C_146) | ~r2_hidden(B_148, C_146) | ~r2_hidden(A_147, C_146))), inference(superposition, [status(thm), theory('equality')], [c_4291, c_319])).
% 6.90/2.74  tff(c_9200, plain, (![A_200, B_201, C_202]: (k4_xboole_0(k2_tarski(A_200, B_201), C_202)=k1_xboole_0 | ~r2_hidden(B_201, C_202) | ~r2_hidden(A_200, C_202))), inference(demodulation, [status(thm), theory('equality')], [c_583, c_4301])).
% 6.90/2.74  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.90/2.74  tff(c_9316, plain, (![C_202, A_200, B_201]: (k2_xboole_0(C_202, k2_tarski(A_200, B_201))=k2_xboole_0(C_202, k1_xboole_0) | ~r2_hidden(B_201, C_202) | ~r2_hidden(A_200, C_202))), inference(superposition, [status(thm), theory('equality')], [c_9200, c_16])).
% 6.90/2.74  tff(c_9841, plain, (![C_210, A_211, B_212]: (k2_xboole_0(C_210, k2_tarski(A_211, B_212))=C_210 | ~r2_hidden(B_212, C_210) | ~r2_hidden(A_211, C_210))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_9316])).
% 6.90/2.74  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.90/2.74  tff(c_263, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_38])).
% 6.90/2.74  tff(c_10010, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9841, c_263])).
% 6.90/2.74  tff(c_10113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_10010])).
% 6.90/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.90/2.74  
% 6.90/2.74  Inference rules
% 6.90/2.74  ----------------------
% 6.90/2.74  #Ref     : 0
% 6.90/2.74  #Sup     : 2474
% 6.90/2.74  #Fact    : 0
% 6.90/2.74  #Define  : 0
% 6.90/2.74  #Split   : 0
% 6.90/2.74  #Chain   : 0
% 6.90/2.74  #Close   : 0
% 6.90/2.74  
% 6.90/2.74  Ordering : KBO
% 6.90/2.74  
% 6.90/2.74  Simplification rules
% 6.90/2.74  ----------------------
% 6.90/2.74  #Subsume      : 301
% 6.90/2.74  #Demod        : 5590
% 6.90/2.74  #Tautology    : 1816
% 6.90/2.74  #SimpNegUnit  : 0
% 6.90/2.74  #BackRed      : 2
% 6.90/2.74  
% 6.90/2.74  #Partial instantiations: 0
% 6.90/2.74  #Strategies tried      : 1
% 6.90/2.74  
% 6.90/2.74  Timing (in seconds)
% 6.90/2.74  ----------------------
% 6.90/2.74  Preprocessing        : 0.29
% 6.90/2.74  Parsing              : 0.16
% 6.90/2.74  CNF conversion       : 0.02
% 6.90/2.74  Main loop            : 1.66
% 6.90/2.74  Inferencing          : 0.36
% 6.90/2.74  Reduction            : 1.05
% 6.90/2.74  Demodulation         : 0.96
% 6.90/2.74  BG Simplification    : 0.04
% 6.90/2.74  Subsumption          : 0.16
% 6.90/2.74  Abstraction          : 0.09
% 6.90/2.75  MUC search           : 0.00
% 6.90/2.75  Cooper               : 0.00
% 6.90/2.75  Total                : 1.98
% 6.90/2.75  Index Insertion      : 0.00
% 6.90/2.75  Index Deletion       : 0.00
% 6.90/2.75  Index Matching       : 0.00
% 6.90/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
