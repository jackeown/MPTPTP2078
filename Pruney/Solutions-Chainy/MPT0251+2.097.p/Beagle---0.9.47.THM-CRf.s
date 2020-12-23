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
% DateTime   : Thu Dec  3 09:50:59 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   52 (  54 expanded)
%              Number of leaves         :   30 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  41 expanded)
%              Number of equality atoms :   29 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_38,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_66,plain,(
    ! [B_53,A_54] : k5_xboole_0(B_53,A_54) = k5_xboole_0(A_54,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    ! [A_54] : k5_xboole_0(k1_xboole_0,A_54) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_12])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_261,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_287,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_261])).

tff(c_291,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_287])).

tff(c_676,plain,(
    ! [A_84,B_85,C_86] : k5_xboole_0(k5_xboole_0(A_84,B_85),C_86) = k5_xboole_0(A_84,k5_xboole_0(B_85,C_86)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_744,plain,(
    ! [A_7,C_86] : k5_xboole_0(A_7,k5_xboole_0(A_7,C_86)) = k5_xboole_0(k1_xboole_0,C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_676])).

tff(c_789,plain,(
    ! [A_7,C_86] : k5_xboole_0(A_7,k5_xboole_0(A_7,C_86)) = C_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_744])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_433,plain,(
    ! [B_77,A_78] :
      ( k3_xboole_0(B_77,k1_tarski(A_78)) = k1_tarski(A_78)
      | ~ r2_hidden(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1711,plain,(
    ! [A_127,B_128] :
      ( k3_xboole_0(k1_tarski(A_127),B_128) = k1_tarski(A_127)
      | ~ r2_hidden(A_127,B_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_2])).

tff(c_16,plain,(
    ! [A_15,B_16] : k5_xboole_0(k5_xboole_0(A_15,B_16),k3_xboole_0(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1725,plain,(
    ! [A_127,B_128] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_127),B_128),k1_tarski(A_127)) = k2_xboole_0(k1_tarski(A_127),B_128)
      | ~ r2_hidden(A_127,B_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1711,c_16])).

tff(c_1965,plain,(
    ! [A_132,B_133] :
      ( k2_xboole_0(k1_tarski(A_132),B_133) = B_133
      | ~ r2_hidden(A_132,B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_4,c_1725])).

tff(c_36,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1997,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1965,c_36])).

tff(c_2016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1997])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:22:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.58  
% 3.32/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.59  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.32/1.59  
% 3.32/1.59  %Foreground sorts:
% 3.32/1.59  
% 3.32/1.59  
% 3.32/1.59  %Background operators:
% 3.32/1.59  
% 3.32/1.59  
% 3.32/1.59  %Foreground operators:
% 3.32/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.32/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.32/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.32/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.59  
% 3.32/1.60  tff(f_66, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.32/1.60  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.32/1.60  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.32/1.60  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.32/1.60  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.32/1.60  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.32/1.60  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.32/1.60  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 3.32/1.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.32/1.60  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.32/1.60  tff(c_38, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.32/1.60  tff(c_66, plain, (![B_53, A_54]: (k5_xboole_0(B_53, A_54)=k5_xboole_0(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.60  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.60  tff(c_82, plain, (![A_54]: (k5_xboole_0(k1_xboole_0, A_54)=A_54)), inference(superposition, [status(thm), theory('equality')], [c_66, c_12])).
% 3.32/1.60  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.60  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/1.60  tff(c_261, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.60  tff(c_287, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k5_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_261])).
% 3.32/1.60  tff(c_291, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_287])).
% 3.32/1.60  tff(c_676, plain, (![A_84, B_85, C_86]: (k5_xboole_0(k5_xboole_0(A_84, B_85), C_86)=k5_xboole_0(A_84, k5_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.60  tff(c_744, plain, (![A_7, C_86]: (k5_xboole_0(A_7, k5_xboole_0(A_7, C_86))=k5_xboole_0(k1_xboole_0, C_86))), inference(superposition, [status(thm), theory('equality')], [c_291, c_676])).
% 3.32/1.60  tff(c_789, plain, (![A_7, C_86]: (k5_xboole_0(A_7, k5_xboole_0(A_7, C_86))=C_86)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_744])).
% 3.32/1.60  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.60  tff(c_433, plain, (![B_77, A_78]: (k3_xboole_0(B_77, k1_tarski(A_78))=k1_tarski(A_78) | ~r2_hidden(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.32/1.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.32/1.60  tff(c_1711, plain, (![A_127, B_128]: (k3_xboole_0(k1_tarski(A_127), B_128)=k1_tarski(A_127) | ~r2_hidden(A_127, B_128))), inference(superposition, [status(thm), theory('equality')], [c_433, c_2])).
% 3.32/1.60  tff(c_16, plain, (![A_15, B_16]: (k5_xboole_0(k5_xboole_0(A_15, B_16), k3_xboole_0(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.60  tff(c_1725, plain, (![A_127, B_128]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_127), B_128), k1_tarski(A_127))=k2_xboole_0(k1_tarski(A_127), B_128) | ~r2_hidden(A_127, B_128))), inference(superposition, [status(thm), theory('equality')], [c_1711, c_16])).
% 3.32/1.60  tff(c_1965, plain, (![A_132, B_133]: (k2_xboole_0(k1_tarski(A_132), B_133)=B_133 | ~r2_hidden(A_132, B_133))), inference(demodulation, [status(thm), theory('equality')], [c_789, c_4, c_1725])).
% 3.32/1.60  tff(c_36, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.32/1.60  tff(c_1997, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1965, c_36])).
% 3.32/1.60  tff(c_2016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1997])).
% 3.32/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.60  
% 3.32/1.60  Inference rules
% 3.32/1.60  ----------------------
% 3.32/1.60  #Ref     : 0
% 3.32/1.60  #Sup     : 487
% 3.32/1.60  #Fact    : 0
% 3.32/1.60  #Define  : 0
% 3.32/1.60  #Split   : 0
% 3.32/1.60  #Chain   : 0
% 3.32/1.60  #Close   : 0
% 3.32/1.60  
% 3.32/1.60  Ordering : KBO
% 3.32/1.60  
% 3.32/1.60  Simplification rules
% 3.32/1.60  ----------------------
% 3.32/1.60  #Subsume      : 18
% 3.32/1.60  #Demod        : 233
% 3.32/1.60  #Tautology    : 298
% 3.32/1.60  #SimpNegUnit  : 0
% 3.32/1.60  #BackRed      : 0
% 3.32/1.60  
% 3.32/1.60  #Partial instantiations: 0
% 3.32/1.60  #Strategies tried      : 1
% 3.32/1.60  
% 3.32/1.60  Timing (in seconds)
% 3.32/1.60  ----------------------
% 3.32/1.60  Preprocessing        : 0.34
% 3.32/1.60  Parsing              : 0.19
% 3.32/1.60  CNF conversion       : 0.02
% 3.32/1.60  Main loop            : 0.45
% 3.32/1.60  Inferencing          : 0.16
% 3.32/1.60  Reduction            : 0.19
% 3.32/1.60  Demodulation         : 0.16
% 3.32/1.60  BG Simplification    : 0.03
% 3.32/1.60  Subsumption          : 0.06
% 3.32/1.60  Abstraction          : 0.03
% 3.32/1.60  MUC search           : 0.00
% 3.32/1.60  Cooper               : 0.00
% 3.32/1.60  Total                : 0.82
% 3.32/1.60  Index Insertion      : 0.00
% 3.32/1.60  Index Deletion       : 0.00
% 3.32/1.60  Index Matching       : 0.00
% 3.32/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
