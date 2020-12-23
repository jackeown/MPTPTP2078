%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:18 EST 2020

% Result     : Theorem 9.61s
% Output     : CNFRefutation 9.83s
% Verified   : 
% Statistics : Number of formulae       :   58 (  63 expanded)
%              Number of leaves         :   31 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  61 expanded)
%              Number of equality atoms :   31 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(c_44,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_417,plain,(
    ! [A_92,B_93,C_94] :
      ( r1_tarski(k2_tarski(A_92,B_93),C_94)
      | ~ r2_hidden(B_93,C_94)
      | ~ r2_hidden(A_92,C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5602,plain,(
    ! [A_177,B_178,C_179] :
      ( k4_xboole_0(k2_tarski(A_177,B_178),C_179) = k1_xboole_0
      | ~ r2_hidden(B_178,C_179)
      | ~ r2_hidden(A_177,C_179) ) ),
    inference(resolution,[status(thm)],[c_417,c_8])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5632,plain,(
    ! [C_179,A_177,B_178] :
      ( k2_xboole_0(C_179,k2_tarski(A_177,B_178)) = k2_xboole_0(C_179,k1_xboole_0)
      | ~ r2_hidden(B_178,C_179)
      | ~ r2_hidden(A_177,C_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5602,c_14])).

tff(c_11458,plain,(
    ! [C_216,A_217,B_218] :
      ( k2_xboole_0(C_216,k2_tarski(A_217,B_218)) = C_216
      | ~ r2_hidden(B_218,C_216)
      | ~ r2_hidden(A_217,C_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5632])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_165,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_174,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_165])).

tff(c_266,plain,(
    ! [A_85,B_86,C_87] : k5_xboole_0(k5_xboole_0(A_85,B_86),C_87) = k5_xboole_0(A_85,k5_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(k5_xboole_0(A_15,B_16),k3_xboole_0(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_279,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k5_xboole_0(B_86,k3_xboole_0(A_85,B_86))) = k2_xboole_0(A_85,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_18])).

tff(c_336,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k4_xboole_0(B_86,A_85)) = k2_xboole_0(A_85,B_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_279])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_219,plain,(
    ! [A_83,B_84] : k5_xboole_0(k5_xboole_0(A_83,B_84),k3_xboole_0(A_83,B_84)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_430,plain,(
    ! [A_95,B_96] : k5_xboole_0(k5_xboole_0(A_95,B_96),k3_xboole_0(B_96,A_95)) = k2_xboole_0(B_96,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_219])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),C_14) = k5_xboole_0(A_12,k5_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_445,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k5_xboole_0(B_96,k3_xboole_0(B_96,A_95))) = k2_xboole_0(B_96,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_16])).

tff(c_511,plain,(
    ! [B_96,A_95] : k2_xboole_0(B_96,A_95) = k2_xboole_0(A_95,B_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_10,c_445])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_523,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_40])).

tff(c_11494,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11458,c_523])).

tff(c_11538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_11494])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.61/3.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.83/3.81  
% 9.83/3.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.83/3.81  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.83/3.81  
% 9.83/3.81  %Foreground sorts:
% 9.83/3.81  
% 9.83/3.81  
% 9.83/3.81  %Background operators:
% 9.83/3.81  
% 9.83/3.81  
% 9.83/3.81  %Foreground operators:
% 9.83/3.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.83/3.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.83/3.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.83/3.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.83/3.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.83/3.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.83/3.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.83/3.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.83/3.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.83/3.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.83/3.81  tff('#skF_2', type, '#skF_2': $i).
% 9.83/3.81  tff('#skF_3', type, '#skF_3': $i).
% 9.83/3.81  tff('#skF_1', type, '#skF_1': $i).
% 9.83/3.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.83/3.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.83/3.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.83/3.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.83/3.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.83/3.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.83/3.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.83/3.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.83/3.81  
% 9.83/3.83  tff(f_70, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 9.83/3.83  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.83/3.83  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 9.83/3.83  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.83/3.83  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.83/3.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.83/3.83  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.83/3.83  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.83/3.83  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 9.83/3.83  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.83/3.83  tff(c_44, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.83/3.83  tff(c_42, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.83/3.83  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.83/3.83  tff(c_417, plain, (![A_92, B_93, C_94]: (r1_tarski(k2_tarski(A_92, B_93), C_94) | ~r2_hidden(B_93, C_94) | ~r2_hidden(A_92, C_94))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.83/3.83  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.83/3.83  tff(c_5602, plain, (![A_177, B_178, C_179]: (k4_xboole_0(k2_tarski(A_177, B_178), C_179)=k1_xboole_0 | ~r2_hidden(B_178, C_179) | ~r2_hidden(A_177, C_179))), inference(resolution, [status(thm)], [c_417, c_8])).
% 9.83/3.83  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.83/3.83  tff(c_5632, plain, (![C_179, A_177, B_178]: (k2_xboole_0(C_179, k2_tarski(A_177, B_178))=k2_xboole_0(C_179, k1_xboole_0) | ~r2_hidden(B_178, C_179) | ~r2_hidden(A_177, C_179))), inference(superposition, [status(thm), theory('equality')], [c_5602, c_14])).
% 9.83/3.83  tff(c_11458, plain, (![C_216, A_217, B_218]: (k2_xboole_0(C_216, k2_tarski(A_217, B_218))=C_216 | ~r2_hidden(B_218, C_216) | ~r2_hidden(A_217, C_216))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5632])).
% 9.83/3.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.83/3.83  tff(c_165, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.83/3.83  tff(c_174, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_165])).
% 9.83/3.83  tff(c_266, plain, (![A_85, B_86, C_87]: (k5_xboole_0(k5_xboole_0(A_85, B_86), C_87)=k5_xboole_0(A_85, k5_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.83/3.83  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(k5_xboole_0(A_15, B_16), k3_xboole_0(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.83/3.83  tff(c_279, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k5_xboole_0(B_86, k3_xboole_0(A_85, B_86)))=k2_xboole_0(A_85, B_86))), inference(superposition, [status(thm), theory('equality')], [c_266, c_18])).
% 9.83/3.83  tff(c_336, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k4_xboole_0(B_86, A_85))=k2_xboole_0(A_85, B_86))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_279])).
% 9.83/3.83  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.83/3.83  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.83/3.83  tff(c_219, plain, (![A_83, B_84]: (k5_xboole_0(k5_xboole_0(A_83, B_84), k3_xboole_0(A_83, B_84))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.83/3.83  tff(c_430, plain, (![A_95, B_96]: (k5_xboole_0(k5_xboole_0(A_95, B_96), k3_xboole_0(B_96, A_95))=k2_xboole_0(B_96, A_95))), inference(superposition, [status(thm), theory('equality')], [c_4, c_219])).
% 9.83/3.83  tff(c_16, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), C_14)=k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.83/3.83  tff(c_445, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k5_xboole_0(B_96, k3_xboole_0(B_96, A_95)))=k2_xboole_0(B_96, A_95))), inference(superposition, [status(thm), theory('equality')], [c_430, c_16])).
% 9.83/3.83  tff(c_511, plain, (![B_96, A_95]: (k2_xboole_0(B_96, A_95)=k2_xboole_0(A_95, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_10, c_445])).
% 9.83/3.83  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.83/3.83  tff(c_523, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_511, c_40])).
% 9.83/3.83  tff(c_11494, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11458, c_523])).
% 9.83/3.83  tff(c_11538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_11494])).
% 9.83/3.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.83/3.83  
% 9.83/3.83  Inference rules
% 9.83/3.83  ----------------------
% 9.83/3.83  #Ref     : 0
% 9.83/3.83  #Sup     : 2947
% 9.83/3.83  #Fact    : 0
% 9.83/3.83  #Define  : 0
% 9.83/3.83  #Split   : 0
% 9.83/3.83  #Chain   : 0
% 9.83/3.83  #Close   : 0
% 9.83/3.83  
% 9.83/3.83  Ordering : KBO
% 9.83/3.83  
% 9.83/3.83  Simplification rules
% 9.83/3.83  ----------------------
% 9.83/3.83  #Subsume      : 321
% 9.83/3.83  #Demod        : 3312
% 9.83/3.83  #Tautology    : 766
% 9.83/3.83  #SimpNegUnit  : 0
% 9.83/3.83  #BackRed      : 1
% 9.83/3.83  
% 9.83/3.83  #Partial instantiations: 0
% 9.83/3.83  #Strategies tried      : 1
% 9.83/3.83  
% 9.83/3.83  Timing (in seconds)
% 9.83/3.83  ----------------------
% 9.83/3.83  Preprocessing        : 0.33
% 9.83/3.83  Parsing              : 0.18
% 9.83/3.83  CNF conversion       : 0.02
% 9.83/3.83  Main loop            : 2.75
% 9.83/3.83  Inferencing          : 0.49
% 9.83/3.83  Reduction            : 1.84
% 9.83/3.83  Demodulation         : 1.71
% 9.83/3.83  BG Simplification    : 0.09
% 9.83/3.83  Subsumption          : 0.25
% 9.83/3.83  Abstraction          : 0.13
% 9.83/3.83  MUC search           : 0.00
% 9.83/3.83  Cooper               : 0.00
% 9.83/3.83  Total                : 3.11
% 9.83/3.83  Index Insertion      : 0.00
% 9.83/3.83  Index Deletion       : 0.00
% 9.83/3.83  Index Matching       : 0.00
% 9.83/3.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
