%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:42 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 338 expanded)
%              Number of leaves         :   27 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :   67 ( 352 expanded)
%              Number of equality atoms :   53 ( 326 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_68,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_10,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_168,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_335,plain,(
    ! [B_60,A_61] : k3_tarski(k2_tarski(B_60,A_61)) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_168])).

tff(c_34,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_384,plain,(
    ! [B_65,A_66] : k2_xboole_0(B_65,A_66) = k2_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_34])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_133,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k2_xboole_0(A_43,B_44)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_140,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_133])).

tff(c_146,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_10])).

tff(c_154,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_38])).

tff(c_405,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_154])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_462,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_14])).

tff(c_465,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_462])).

tff(c_408,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_154])).

tff(c_489,plain,(
    k2_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_465,c_408])).

tff(c_18,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_186,plain,(
    ! [A_13] : k3_tarski(k1_tarski(A_13)) = k2_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_168])).

tff(c_513,plain,(
    ! [A_70] : k4_xboole_0(A_70,'#skF_3') = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_10])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_933,plain,(
    ! [A_95,C_96] : k4_xboole_0(A_95,k2_xboole_0('#skF_3',C_96)) = k4_xboole_0(A_95,C_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_12])).

tff(c_480,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_14])).

tff(c_940,plain,(
    ! [C_96] : k4_xboole_0('#skF_3',C_96) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_933,c_480])).

tff(c_28,plain,(
    ! [C_21,B_20] : r1_tarski(k1_tarski(C_21),k2_tarski(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_162,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_28])).

tff(c_476,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_162])).

tff(c_284,plain,(
    ! [A_56,B_57] :
      ( r2_xboole_0(A_56,B_57)
      | B_57 = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k4_xboole_0(B_4,A_3) != k1_xboole_0
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_295,plain,(
    ! [B_57,A_56] :
      ( k4_xboole_0(B_57,A_56) != k1_xboole_0
      | B_57 = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_284,c_8])).

tff(c_694,plain,(
    ! [B_82,A_83] :
      ( k4_xboole_0(B_82,A_83) != '#skF_3'
      | B_82 = A_83
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_295])).

tff(c_727,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3'
    | k1_tarski('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_476,c_694])).

tff(c_832,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_727])).

tff(c_987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_940,c_832])).

tff(c_988,plain,(
    k1_tarski('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_727])).

tff(c_209,plain,(
    ! [A_47] : k3_tarski(k1_tarski(A_47)) = k2_xboole_0(A_47,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_168])).

tff(c_36,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),B_25) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_222,plain,(
    ! [A_24] : k3_tarski(k1_tarski(k1_tarski(A_24))) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_36])).

tff(c_472,plain,(
    ! [A_24] : k3_tarski(k1_tarski(k1_tarski(A_24))) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_222])).

tff(c_994,plain,(
    k3_tarski(k1_tarski('#skF_3')) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_472])).

tff(c_1020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_186,c_994])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:04:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.45  
% 2.62/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.45  %$ r2_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.45  
% 2.62/1.45  %Foreground sorts:
% 2.62/1.45  
% 2.62/1.45  
% 2.62/1.45  %Background operators:
% 2.62/1.45  
% 2.62/1.45  
% 2.62/1.45  %Foreground operators:
% 2.62/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.62/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.62/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.45  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.62/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.62/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.62/1.45  
% 2.89/1.46  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.89/1.46  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.89/1.46  tff(f_68, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.89/1.46  tff(f_75, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.89/1.46  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.89/1.46  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.89/1.46  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.89/1.46  tff(f_66, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.89/1.46  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.89/1.46  tff(f_37, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 2.89/1.46  tff(f_71, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.89/1.46  tff(c_10, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.89/1.46  tff(c_16, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.89/1.46  tff(c_168, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.89/1.46  tff(c_335, plain, (![B_60, A_61]: (k3_tarski(k2_tarski(B_60, A_61))=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_16, c_168])).
% 2.89/1.46  tff(c_34, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.89/1.46  tff(c_384, plain, (![B_65, A_66]: (k2_xboole_0(B_65, A_66)=k2_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_335, c_34])).
% 2.89/1.46  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.46  tff(c_133, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k2_xboole_0(A_43, B_44))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.46  tff(c_140, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_133])).
% 2.89/1.46  tff(c_146, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_140, c_10])).
% 2.89/1.46  tff(c_154, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_146, c_38])).
% 2.89/1.46  tff(c_405, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_384, c_154])).
% 2.89/1.46  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.46  tff(c_462, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_405, c_14])).
% 2.89/1.46  tff(c_465, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_462])).
% 2.89/1.46  tff(c_408, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_384, c_154])).
% 2.89/1.46  tff(c_489, plain, (k2_xboole_0('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_465, c_465, c_408])).
% 2.89/1.46  tff(c_18, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.89/1.46  tff(c_186, plain, (![A_13]: (k3_tarski(k1_tarski(A_13))=k2_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_18, c_168])).
% 2.89/1.46  tff(c_513, plain, (![A_70]: (k4_xboole_0(A_70, '#skF_3')=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_465, c_10])).
% 2.89/1.46  tff(c_12, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.46  tff(c_933, plain, (![A_95, C_96]: (k4_xboole_0(A_95, k2_xboole_0('#skF_3', C_96))=k4_xboole_0(A_95, C_96))), inference(superposition, [status(thm), theory('equality')], [c_513, c_12])).
% 2.89/1.46  tff(c_480, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_465, c_14])).
% 2.89/1.46  tff(c_940, plain, (![C_96]: (k4_xboole_0('#skF_3', C_96)='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_933, c_480])).
% 2.89/1.46  tff(c_28, plain, (![C_21, B_20]: (r1_tarski(k1_tarski(C_21), k2_tarski(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.89/1.46  tff(c_162, plain, (r1_tarski(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_146, c_28])).
% 2.89/1.46  tff(c_476, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_465, c_162])).
% 2.89/1.46  tff(c_284, plain, (![A_56, B_57]: (r2_xboole_0(A_56, B_57) | B_57=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.89/1.46  tff(c_8, plain, (![B_4, A_3]: (k4_xboole_0(B_4, A_3)!=k1_xboole_0 | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.46  tff(c_295, plain, (![B_57, A_56]: (k4_xboole_0(B_57, A_56)!=k1_xboole_0 | B_57=A_56 | ~r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_284, c_8])).
% 2.89/1.46  tff(c_694, plain, (![B_82, A_83]: (k4_xboole_0(B_82, A_83)!='#skF_3' | B_82=A_83 | ~r1_tarski(A_83, B_82))), inference(demodulation, [status(thm), theory('equality')], [c_465, c_295])).
% 2.89/1.46  tff(c_727, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3' | k1_tarski('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_476, c_694])).
% 2.89/1.46  tff(c_832, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_727])).
% 2.89/1.46  tff(c_987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_940, c_832])).
% 2.89/1.46  tff(c_988, plain, (k1_tarski('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_727])).
% 2.89/1.46  tff(c_209, plain, (![A_47]: (k3_tarski(k1_tarski(A_47))=k2_xboole_0(A_47, A_47))), inference(superposition, [status(thm), theory('equality')], [c_18, c_168])).
% 2.89/1.46  tff(c_36, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.89/1.46  tff(c_222, plain, (![A_24]: (k3_tarski(k1_tarski(k1_tarski(A_24)))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_209, c_36])).
% 2.89/1.46  tff(c_472, plain, (![A_24]: (k3_tarski(k1_tarski(k1_tarski(A_24)))!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_465, c_222])).
% 2.89/1.46  tff(c_994, plain, (k3_tarski(k1_tarski('#skF_3'))!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_988, c_472])).
% 2.89/1.46  tff(c_1020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_489, c_186, c_994])).
% 2.89/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.46  
% 2.89/1.46  Inference rules
% 2.89/1.46  ----------------------
% 2.89/1.46  #Ref     : 0
% 2.89/1.46  #Sup     : 255
% 2.89/1.46  #Fact    : 0
% 2.89/1.46  #Define  : 0
% 2.89/1.46  #Split   : 1
% 2.89/1.46  #Chain   : 0
% 2.89/1.46  #Close   : 0
% 2.89/1.46  
% 2.89/1.46  Ordering : KBO
% 2.89/1.46  
% 2.89/1.46  Simplification rules
% 2.89/1.46  ----------------------
% 2.89/1.46  #Subsume      : 12
% 2.89/1.46  #Demod        : 144
% 2.89/1.46  #Tautology    : 166
% 2.89/1.46  #SimpNegUnit  : 0
% 2.89/1.46  #BackRed      : 22
% 2.89/1.46  
% 2.89/1.46  #Partial instantiations: 0
% 2.89/1.46  #Strategies tried      : 1
% 2.89/1.46  
% 2.89/1.46  Timing (in seconds)
% 2.89/1.46  ----------------------
% 2.89/1.46  Preprocessing        : 0.31
% 2.89/1.46  Parsing              : 0.17
% 2.89/1.46  CNF conversion       : 0.02
% 2.89/1.46  Main loop            : 0.36
% 2.89/1.46  Inferencing          : 0.12
% 2.89/1.46  Reduction            : 0.14
% 2.89/1.47  Demodulation         : 0.11
% 2.89/1.47  BG Simplification    : 0.02
% 2.89/1.47  Subsumption          : 0.06
% 2.89/1.47  Abstraction          : 0.02
% 2.89/1.47  MUC search           : 0.00
% 2.89/1.47  Cooper               : 0.00
% 2.89/1.47  Total                : 0.69
% 2.89/1.47  Index Insertion      : 0.00
% 2.89/1.47  Index Deletion       : 0.00
% 2.89/1.47  Index Matching       : 0.00
% 2.89/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
