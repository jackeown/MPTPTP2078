%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:54 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   67 (  95 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :   61 (  96 expanded)
%              Number of equality atoms :   41 (  67 expanded)
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

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,A_38) = k2_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_38] : k2_xboole_0(k1_xboole_0,A_38) = A_38 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_14])).

tff(c_244,plain,(
    ! [A_52,B_53] : k2_xboole_0(A_52,k4_xboole_0(B_53,A_52)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_251,plain,(
    ! [B_53] : k4_xboole_0(B_53,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_112])).

tff(c_260,plain,(
    ! [B_53] : k4_xboole_0(B_53,k1_xboole_0) = B_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_251])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_231,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_263,plain,(
    ! [A_54] : k3_xboole_0(k1_xboole_0,A_54) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_231])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_268,plain,(
    ! [A_54] : k3_xboole_0(A_54,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_4])).

tff(c_405,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_414,plain,(
    ! [A_54] : k5_xboole_0(A_54,k1_xboole_0) = k4_xboole_0(A_54,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_405])).

tff(c_429,plain,(
    ! [A_54] : k5_xboole_0(A_54,k1_xboole_0) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_414])).

tff(c_242,plain,(
    ! [A_12] : k3_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_231])).

tff(c_420,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_405])).

tff(c_482,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_420])).

tff(c_360,plain,(
    ! [A_58,B_59] : k4_xboole_0(k2_xboole_0(A_58,B_59),B_59) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_386,plain,(
    ! [A_38] : k4_xboole_0(k1_xboole_0,A_38) = k4_xboole_0(A_38,A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_360])).

tff(c_483,plain,(
    ! [A_38] : k4_xboole_0(A_38,A_38) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_386])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_243,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_231])).

tff(c_417,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_405])).

tff(c_505,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_417])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k1_tarski(A_27),B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_986,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(k1_tarski(A_93),B_94) = k1_tarski(A_93)
      | ~ r2_hidden(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_34,c_231])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_995,plain,(
    ! [A_93,B_94] :
      ( k5_xboole_0(k1_tarski(A_93),k1_tarski(A_93)) = k4_xboole_0(k1_tarski(A_93),B_94)
      | ~ r2_hidden(A_93,B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_12])).

tff(c_1184,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(k1_tarski(A_99),B_100) = k1_xboole_0
      | ~ r2_hidden(A_99,B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_995])).

tff(c_20,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1212,plain,(
    ! [B_100,A_99] :
      ( k2_xboole_0(B_100,k1_tarski(A_99)) = k2_xboole_0(B_100,k1_xboole_0)
      | ~ r2_hidden(A_99,B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1184,c_20])).

tff(c_1350,plain,(
    ! [B_103,A_104] :
      ( k2_xboole_0(B_103,k1_tarski(A_104)) = B_103
      | ~ r2_hidden(A_104,B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1212])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_1398,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1350,c_42])).

tff(c_1437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:11:45 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.45  
% 2.53/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.45  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.53/1.45  
% 2.53/1.45  %Foreground sorts:
% 2.53/1.45  
% 2.53/1.45  
% 2.53/1.45  %Background operators:
% 2.53/1.45  
% 2.53/1.45  
% 2.53/1.45  %Foreground operators:
% 2.53/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.53/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.53/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.53/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.53/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.53/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.53/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.53/1.45  
% 2.53/1.46  tff(f_68, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.53/1.46  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.53/1.46  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.53/1.46  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.53/1.46  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.53/1.46  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.53/1.46  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.53/1.46  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.53/1.46  tff(f_49, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.53/1.46  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.53/1.46  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.53/1.46  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.53/1.46  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.53/1.46  tff(c_96, plain, (![B_37, A_38]: (k2_xboole_0(B_37, A_38)=k2_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.46  tff(c_112, plain, (![A_38]: (k2_xboole_0(k1_xboole_0, A_38)=A_38)), inference(superposition, [status(thm), theory('equality')], [c_96, c_14])).
% 2.53/1.46  tff(c_244, plain, (![A_52, B_53]: (k2_xboole_0(A_52, k4_xboole_0(B_53, A_52))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.46  tff(c_251, plain, (![B_53]: (k4_xboole_0(B_53, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_53))), inference(superposition, [status(thm), theory('equality')], [c_244, c_112])).
% 2.53/1.46  tff(c_260, plain, (![B_53]: (k4_xboole_0(B_53, k1_xboole_0)=B_53)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_251])).
% 2.53/1.46  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.53/1.46  tff(c_231, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.53/1.46  tff(c_263, plain, (![A_54]: (k3_xboole_0(k1_xboole_0, A_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_231])).
% 2.53/1.46  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.46  tff(c_268, plain, (![A_54]: (k3_xboole_0(A_54, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_263, c_4])).
% 2.53/1.46  tff(c_405, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.46  tff(c_414, plain, (![A_54]: (k5_xboole_0(A_54, k1_xboole_0)=k4_xboole_0(A_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_268, c_405])).
% 2.53/1.46  tff(c_429, plain, (![A_54]: (k5_xboole_0(A_54, k1_xboole_0)=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_260, c_414])).
% 2.53/1.46  tff(c_242, plain, (![A_12]: (k3_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_231])).
% 2.53/1.46  tff(c_420, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_12))), inference(superposition, [status(thm), theory('equality')], [c_242, c_405])).
% 2.53/1.46  tff(c_482, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_429, c_420])).
% 2.53/1.46  tff(c_360, plain, (![A_58, B_59]: (k4_xboole_0(k2_xboole_0(A_58, B_59), B_59)=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.53/1.46  tff(c_386, plain, (![A_38]: (k4_xboole_0(k1_xboole_0, A_38)=k4_xboole_0(A_38, A_38))), inference(superposition, [status(thm), theory('equality')], [c_112, c_360])).
% 2.53/1.46  tff(c_483, plain, (![A_38]: (k4_xboole_0(A_38, A_38)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_482, c_386])).
% 2.53/1.46  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.46  tff(c_243, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_231])).
% 2.53/1.46  tff(c_417, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_243, c_405])).
% 2.53/1.46  tff(c_505, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_483, c_417])).
% 2.53/1.46  tff(c_34, plain, (![A_27, B_28]: (r1_tarski(k1_tarski(A_27), B_28) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.53/1.46  tff(c_986, plain, (![A_93, B_94]: (k3_xboole_0(k1_tarski(A_93), B_94)=k1_tarski(A_93) | ~r2_hidden(A_93, B_94))), inference(resolution, [status(thm)], [c_34, c_231])).
% 2.53/1.46  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.46  tff(c_995, plain, (![A_93, B_94]: (k5_xboole_0(k1_tarski(A_93), k1_tarski(A_93))=k4_xboole_0(k1_tarski(A_93), B_94) | ~r2_hidden(A_93, B_94))), inference(superposition, [status(thm), theory('equality')], [c_986, c_12])).
% 2.53/1.46  tff(c_1184, plain, (![A_99, B_100]: (k4_xboole_0(k1_tarski(A_99), B_100)=k1_xboole_0 | ~r2_hidden(A_99, B_100))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_995])).
% 2.53/1.46  tff(c_20, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.46  tff(c_1212, plain, (![B_100, A_99]: (k2_xboole_0(B_100, k1_tarski(A_99))=k2_xboole_0(B_100, k1_xboole_0) | ~r2_hidden(A_99, B_100))), inference(superposition, [status(thm), theory('equality')], [c_1184, c_20])).
% 2.53/1.46  tff(c_1350, plain, (![B_103, A_104]: (k2_xboole_0(B_103, k1_tarski(A_104))=B_103 | ~r2_hidden(A_104, B_103))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1212])).
% 2.53/1.46  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.46  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.53/1.46  tff(c_42, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 2.53/1.46  tff(c_1398, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1350, c_42])).
% 2.53/1.46  tff(c_1437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1398])).
% 2.53/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.46  
% 2.53/1.46  Inference rules
% 2.53/1.46  ----------------------
% 2.53/1.46  #Ref     : 0
% 2.53/1.46  #Sup     : 327
% 2.53/1.46  #Fact    : 0
% 2.53/1.46  #Define  : 0
% 2.53/1.46  #Split   : 0
% 2.53/1.46  #Chain   : 0
% 2.53/1.46  #Close   : 0
% 2.53/1.46  
% 2.53/1.46  Ordering : KBO
% 2.53/1.46  
% 2.53/1.46  Simplification rules
% 2.53/1.46  ----------------------
% 2.53/1.46  #Subsume      : 13
% 2.53/1.46  #Demod        : 257
% 2.53/1.46  #Tautology    : 262
% 2.53/1.46  #SimpNegUnit  : 0
% 2.53/1.46  #BackRed      : 3
% 2.53/1.46  
% 2.53/1.46  #Partial instantiations: 0
% 2.53/1.46  #Strategies tried      : 1
% 2.53/1.46  
% 2.53/1.46  Timing (in seconds)
% 2.53/1.46  ----------------------
% 2.88/1.47  Preprocessing        : 0.30
% 2.88/1.47  Parsing              : 0.16
% 2.88/1.47  CNF conversion       : 0.02
% 2.88/1.47  Main loop            : 0.36
% 2.88/1.47  Inferencing          : 0.13
% 2.88/1.47  Reduction            : 0.14
% 2.88/1.47  Demodulation         : 0.12
% 2.88/1.47  BG Simplification    : 0.02
% 2.88/1.47  Subsumption          : 0.05
% 2.88/1.47  Abstraction          : 0.02
% 2.88/1.47  MUC search           : 0.00
% 2.88/1.47  Cooper               : 0.00
% 2.88/1.47  Total                : 0.69
% 2.88/1.47  Index Insertion      : 0.00
% 2.88/1.47  Index Deletion       : 0.00
% 2.88/1.47  Index Matching       : 0.00
% 2.88/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
