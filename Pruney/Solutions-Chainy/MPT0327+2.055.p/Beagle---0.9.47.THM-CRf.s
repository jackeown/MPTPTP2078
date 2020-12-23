%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:37 EST 2020

% Result     : Theorem 19.74s
% Output     : CNFRefutation 19.74s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 194 expanded)
%              Number of leaves         :   31 (  77 expanded)
%              Depth                    :   18
%              Number of atoms          :   70 ( 241 expanded)
%              Number of equality atoms :   47 ( 157 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_52,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_121,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(k1_tarski(A_49),B_50)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_125,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(k1_tarski(A_49),B_50) = B_50
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_121,c_16])).

tff(c_46,plain,(
    ! [C_37,B_36] : ~ r2_hidden(C_37,k4_xboole_0(B_36,k1_tarski(C_37))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_156,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_168,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_156])).

tff(c_202,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k4_xboole_0(B_67,A_66)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_211,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_202])).

tff(c_214,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_211])).

tff(c_224,plain,(
    ! [A_69,B_70] : k2_xboole_0(k3_xboole_0(A_69,B_70),k4_xboole_0(A_69,B_70)) = A_69 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_236,plain,(
    ! [B_71] : k2_xboole_0(k3_xboole_0(B_71,B_71),k1_xboole_0) = B_71 ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_224])).

tff(c_18,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_253,plain,(
    ! [B_72] : k3_xboole_0(B_72,B_72) = B_72 ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_18])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_262,plain,(
    ! [B_72] : k5_xboole_0(B_72,B_72) = k4_xboole_0(B_72,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_14])).

tff(c_268,plain,(
    ! [B_72] : k5_xboole_0(B_72,B_72) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_262])).

tff(c_24,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_514,plain,(
    ! [A_99,B_100,C_101] : k5_xboole_0(k5_xboole_0(A_99,B_100),C_101) = k5_xboole_0(A_99,k5_xboole_0(B_100,C_101)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1944,plain,(
    ! [A_144,B_145,C_146] : k5_xboole_0(A_144,k5_xboole_0(k4_xboole_0(B_145,A_144),C_146)) = k5_xboole_0(k2_xboole_0(A_144,B_145),C_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_514])).

tff(c_2030,plain,(
    ! [A_144,B_145] : k5_xboole_0(k2_xboole_0(A_144,B_145),k4_xboole_0(B_145,A_144)) = k5_xboole_0(A_144,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_1944])).

tff(c_2382,plain,(
    ! [A_154,B_155] : k5_xboole_0(k2_xboole_0(A_154,B_155),k4_xboole_0(B_155,A_154)) = A_154 ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_2030])).

tff(c_524,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k5_xboole_0(B_100,k5_xboole_0(A_99,B_100))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_268])).

tff(c_898,plain,(
    ! [B_113,C_114] : k5_xboole_0(B_113,k5_xboole_0(B_113,C_114)) = k5_xboole_0(k1_xboole_0,C_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_514])).

tff(c_982,plain,(
    ! [B_72] : k5_xboole_0(k1_xboole_0,B_72) = k5_xboole_0(B_72,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_898])).

tff(c_1014,plain,(
    ! [B_72] : k5_xboole_0(k1_xboole_0,B_72) = B_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_982])).

tff(c_545,plain,(
    ! [B_72,C_101] : k5_xboole_0(B_72,k5_xboole_0(B_72,C_101)) = k5_xboole_0(k1_xboole_0,C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_514])).

tff(c_1099,plain,(
    ! [B_120,C_121] : k5_xboole_0(B_120,k5_xboole_0(B_120,C_121)) = C_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1014,c_545])).

tff(c_1143,plain,(
    ! [B_100,A_99] : k5_xboole_0(B_100,k5_xboole_0(A_99,B_100)) = k5_xboole_0(A_99,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_1099])).

tff(c_1179,plain,(
    ! [B_100,A_99] : k5_xboole_0(B_100,k5_xboole_0(A_99,B_100)) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_1143])).

tff(c_3735,plain,(
    ! [B_184,A_185] : k5_xboole_0(k4_xboole_0(B_184,A_185),A_185) = k2_xboole_0(A_185,B_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_2382,c_1179])).

tff(c_440,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(k1_tarski(A_93),B_94) = k1_tarski(A_93)
      | r2_hidden(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_465,plain,(
    ! [B_94,A_93] :
      ( k5_xboole_0(B_94,k1_tarski(A_93)) = k2_xboole_0(B_94,k1_tarski(A_93))
      | r2_hidden(A_93,B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_24])).

tff(c_3755,plain,(
    ! [B_184,A_93] :
      ( k2_xboole_0(k4_xboole_0(B_184,k1_tarski(A_93)),k1_tarski(A_93)) = k2_xboole_0(k1_tarski(A_93),B_184)
      | r2_hidden(A_93,k4_xboole_0(B_184,k1_tarski(A_93))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3735,c_465])).

tff(c_3824,plain,(
    ! [B_184,A_93] : k2_xboole_0(k4_xboole_0(B_184,k1_tarski(A_93)),k1_tarski(A_93)) = k2_xboole_0(k1_tarski(A_93),B_184) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3755])).

tff(c_50,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_53113,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_50])).

tff(c_53229,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_53113])).

tff(c_53233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_53229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:33:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.74/12.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.74/12.70  
% 19.74/12.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.74/12.71  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 19.74/12.71  
% 19.74/12.71  %Foreground sorts:
% 19.74/12.71  
% 19.74/12.71  
% 19.74/12.71  %Background operators:
% 19.74/12.71  
% 19.74/12.71  
% 19.74/12.71  %Foreground operators:
% 19.74/12.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.74/12.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.74/12.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 19.74/12.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 19.74/12.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.74/12.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 19.74/12.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 19.74/12.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.74/12.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.74/12.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.74/12.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.74/12.71  tff('#skF_2', type, '#skF_2': $i).
% 19.74/12.71  tff('#skF_1', type, '#skF_1': $i).
% 19.74/12.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.74/12.71  tff(k3_tarski, type, k3_tarski: $i > $i).
% 19.74/12.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.74/12.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.74/12.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.74/12.71  
% 19.74/12.72  tff(f_82, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 19.74/12.72  tff(f_63, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 19.74/12.72  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 19.74/12.72  tff(f_77, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 19.74/12.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 19.74/12.72  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.74/12.72  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 19.74/12.72  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 19.74/12.72  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 19.74/12.72  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 19.74/12.72  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 19.74/12.72  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 19.74/12.72  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 19.74/12.72  tff(c_52, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 19.74/12.72  tff(c_121, plain, (![A_49, B_50]: (r1_tarski(k1_tarski(A_49), B_50) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 19.74/12.72  tff(c_16, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.74/12.72  tff(c_125, plain, (![A_49, B_50]: (k2_xboole_0(k1_tarski(A_49), B_50)=B_50 | ~r2_hidden(A_49, B_50))), inference(resolution, [status(thm)], [c_121, c_16])).
% 19.74/12.72  tff(c_46, plain, (![C_37, B_36]: (~r2_hidden(C_37, k4_xboole_0(B_36, k1_tarski(C_37))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 19.74/12.72  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.74/12.72  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.74/12.72  tff(c_156, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.74/12.72  tff(c_168, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_156])).
% 19.74/12.72  tff(c_202, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k4_xboole_0(B_67, A_66))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.74/12.72  tff(c_211, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_168, c_202])).
% 19.74/12.72  tff(c_214, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_211])).
% 19.74/12.72  tff(c_224, plain, (![A_69, B_70]: (k2_xboole_0(k3_xboole_0(A_69, B_70), k4_xboole_0(A_69, B_70))=A_69)), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.74/12.72  tff(c_236, plain, (![B_71]: (k2_xboole_0(k3_xboole_0(B_71, B_71), k1_xboole_0)=B_71)), inference(superposition, [status(thm), theory('equality')], [c_168, c_224])).
% 19.74/12.72  tff(c_18, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.74/12.72  tff(c_253, plain, (![B_72]: (k3_xboole_0(B_72, B_72)=B_72)), inference(superposition, [status(thm), theory('equality')], [c_236, c_18])).
% 19.74/12.72  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.74/12.72  tff(c_262, plain, (![B_72]: (k5_xboole_0(B_72, B_72)=k4_xboole_0(B_72, B_72))), inference(superposition, [status(thm), theory('equality')], [c_253, c_14])).
% 19.74/12.72  tff(c_268, plain, (![B_72]: (k5_xboole_0(B_72, B_72)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_168, c_262])).
% 19.74/12.72  tff(c_24, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.74/12.72  tff(c_514, plain, (![A_99, B_100, C_101]: (k5_xboole_0(k5_xboole_0(A_99, B_100), C_101)=k5_xboole_0(A_99, k5_xboole_0(B_100, C_101)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 19.74/12.72  tff(c_1944, plain, (![A_144, B_145, C_146]: (k5_xboole_0(A_144, k5_xboole_0(k4_xboole_0(B_145, A_144), C_146))=k5_xboole_0(k2_xboole_0(A_144, B_145), C_146))), inference(superposition, [status(thm), theory('equality')], [c_24, c_514])).
% 19.74/12.72  tff(c_2030, plain, (![A_144, B_145]: (k5_xboole_0(k2_xboole_0(A_144, B_145), k4_xboole_0(B_145, A_144))=k5_xboole_0(A_144, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_268, c_1944])).
% 19.74/12.72  tff(c_2382, plain, (![A_154, B_155]: (k5_xboole_0(k2_xboole_0(A_154, B_155), k4_xboole_0(B_155, A_154))=A_154)), inference(demodulation, [status(thm), theory('equality')], [c_214, c_2030])).
% 19.74/12.72  tff(c_524, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k5_xboole_0(B_100, k5_xboole_0(A_99, B_100)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_514, c_268])).
% 19.74/12.72  tff(c_898, plain, (![B_113, C_114]: (k5_xboole_0(B_113, k5_xboole_0(B_113, C_114))=k5_xboole_0(k1_xboole_0, C_114))), inference(superposition, [status(thm), theory('equality')], [c_268, c_514])).
% 19.74/12.72  tff(c_982, plain, (![B_72]: (k5_xboole_0(k1_xboole_0, B_72)=k5_xboole_0(B_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_268, c_898])).
% 19.74/12.72  tff(c_1014, plain, (![B_72]: (k5_xboole_0(k1_xboole_0, B_72)=B_72)), inference(demodulation, [status(thm), theory('equality')], [c_214, c_982])).
% 19.74/12.72  tff(c_545, plain, (![B_72, C_101]: (k5_xboole_0(B_72, k5_xboole_0(B_72, C_101))=k5_xboole_0(k1_xboole_0, C_101))), inference(superposition, [status(thm), theory('equality')], [c_268, c_514])).
% 19.74/12.72  tff(c_1099, plain, (![B_120, C_121]: (k5_xboole_0(B_120, k5_xboole_0(B_120, C_121))=C_121)), inference(demodulation, [status(thm), theory('equality')], [c_1014, c_545])).
% 19.74/12.72  tff(c_1143, plain, (![B_100, A_99]: (k5_xboole_0(B_100, k5_xboole_0(A_99, B_100))=k5_xboole_0(A_99, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_524, c_1099])).
% 19.74/12.72  tff(c_1179, plain, (![B_100, A_99]: (k5_xboole_0(B_100, k5_xboole_0(A_99, B_100))=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_214, c_1143])).
% 19.74/12.72  tff(c_3735, plain, (![B_184, A_185]: (k5_xboole_0(k4_xboole_0(B_184, A_185), A_185)=k2_xboole_0(A_185, B_184))), inference(superposition, [status(thm), theory('equality')], [c_2382, c_1179])).
% 19.74/12.72  tff(c_440, plain, (![A_93, B_94]: (k4_xboole_0(k1_tarski(A_93), B_94)=k1_tarski(A_93) | r2_hidden(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_68])).
% 19.74/12.72  tff(c_465, plain, (![B_94, A_93]: (k5_xboole_0(B_94, k1_tarski(A_93))=k2_xboole_0(B_94, k1_tarski(A_93)) | r2_hidden(A_93, B_94))), inference(superposition, [status(thm), theory('equality')], [c_440, c_24])).
% 19.74/12.72  tff(c_3755, plain, (![B_184, A_93]: (k2_xboole_0(k4_xboole_0(B_184, k1_tarski(A_93)), k1_tarski(A_93))=k2_xboole_0(k1_tarski(A_93), B_184) | r2_hidden(A_93, k4_xboole_0(B_184, k1_tarski(A_93))))), inference(superposition, [status(thm), theory('equality')], [c_3735, c_465])).
% 19.74/12.72  tff(c_3824, plain, (![B_184, A_93]: (k2_xboole_0(k4_xboole_0(B_184, k1_tarski(A_93)), k1_tarski(A_93))=k2_xboole_0(k1_tarski(A_93), B_184))), inference(negUnitSimplification, [status(thm)], [c_46, c_3755])).
% 19.74/12.72  tff(c_50, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 19.74/12.72  tff(c_53113, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_50])).
% 19.74/12.72  tff(c_53229, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_125, c_53113])).
% 19.74/12.72  tff(c_53233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_53229])).
% 19.74/12.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.74/12.72  
% 19.74/12.72  Inference rules
% 19.74/12.72  ----------------------
% 19.74/12.72  #Ref     : 0
% 19.74/12.72  #Sup     : 13743
% 19.74/12.72  #Fact    : 0
% 19.74/12.72  #Define  : 0
% 19.74/12.72  #Split   : 0
% 19.74/12.72  #Chain   : 0
% 19.74/12.72  #Close   : 0
% 19.74/12.72  
% 19.74/12.72  Ordering : KBO
% 19.74/12.72  
% 19.74/12.72  Simplification rules
% 19.74/12.72  ----------------------
% 19.74/12.72  #Subsume      : 1198
% 19.74/12.72  #Demod        : 20135
% 19.74/12.72  #Tautology    : 4564
% 19.74/12.72  #SimpNegUnit  : 107
% 19.74/12.72  #BackRed      : 15
% 19.74/12.72  
% 19.74/12.72  #Partial instantiations: 0
% 19.74/12.72  #Strategies tried      : 1
% 19.74/12.72  
% 19.74/12.72  Timing (in seconds)
% 19.74/12.72  ----------------------
% 19.74/12.72  Preprocessing        : 0.33
% 19.74/12.72  Parsing              : 0.18
% 19.74/12.72  CNF conversion       : 0.02
% 19.74/12.72  Main loop            : 11.56
% 19.74/12.72  Inferencing          : 1.44
% 19.74/12.72  Reduction            : 8.28
% 19.74/12.72  Demodulation         : 7.87
% 19.74/12.72  BG Simplification    : 0.26
% 19.74/12.72  Subsumption          : 1.29
% 19.74/12.72  Abstraction          : 0.42
% 19.74/12.72  MUC search           : 0.00
% 19.88/12.72  Cooper               : 0.00
% 19.88/12.73  Total                : 11.92
% 19.88/12.73  Index Insertion      : 0.00
% 19.88/12.73  Index Deletion       : 0.00
% 19.88/12.73  Index Matching       : 0.00
% 19.88/12.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
