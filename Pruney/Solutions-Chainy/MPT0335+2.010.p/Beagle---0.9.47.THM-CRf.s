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
% DateTime   : Thu Dec  3 09:54:54 EST 2020

% Result     : Theorem 8.12s
% Output     : CNFRefutation 8.12s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 111 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :   58 ( 134 expanded)
%              Number of equality atoms :   40 (  91 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_32,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_138,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_127])).

tff(c_216,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_237,plain,(
    ! [B_6] : k4_xboole_0(B_6,k1_xboole_0) = k3_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_216])).

tff(c_243,plain,(
    ! [B_6] : k4_xboole_0(B_6,k1_xboole_0) = B_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_237])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(k1_tarski(A_22),B_23)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_535,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(k1_tarski(A_57),B_58) = k1_xboole_0
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_30,c_127])).

tff(c_20,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_545,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(k1_tarski(A_57),k1_xboole_0) = k3_xboole_0(k1_tarski(A_57),B_58)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_20])).

tff(c_14035,plain,(
    ! [A_171,B_172] :
      ( k3_xboole_0(k1_tarski(A_171),B_172) = k1_tarski(A_171)
      | ~ r2_hidden(A_171,B_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_545])).

tff(c_63,plain,(
    ! [B_27,A_28] : k3_xboole_0(B_27,A_28) = k3_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_78,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_36])).

tff(c_38,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_139,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_127])).

tff(c_234,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_216])).

tff(c_426,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_234])).

tff(c_451,plain,(
    ! [A_54,B_55,C_56] : k3_xboole_0(k3_xboole_0(A_54,B_55),C_56) = k3_xboole_0(A_54,k3_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_486,plain,(
    ! [C_56] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_56)) = k3_xboole_0('#skF_1',C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_451])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_231,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,k3_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_216])).

tff(c_657,plain,(
    ! [A_62,B_63] : k3_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_231])).

tff(c_721,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_657])).

tff(c_3589,plain,(
    ! [B_103,A_104,B_105] : k3_xboole_0(B_103,k3_xboole_0(A_104,B_105)) = k3_xboole_0(A_104,k3_xboole_0(B_105,B_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_451])).

tff(c_5221,plain,(
    ! [B_112] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_112)) = k3_xboole_0(B_112,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_3589])).

tff(c_5341,plain,(
    ! [A_1] : k3_xboole_0(k3_xboole_0(A_1,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_5221])).

tff(c_8552,plain,(
    ! [A_137] : k3_xboole_0(k3_xboole_0(A_137,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',A_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_5341])).

tff(c_8698,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_8552])).

tff(c_14105,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14035,c_8698])).

tff(c_14374,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14105])).

tff(c_14376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_14374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.12/3.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.12/3.04  
% 8.12/3.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.12/3.04  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.12/3.04  
% 8.12/3.04  %Foreground sorts:
% 8.12/3.04  
% 8.12/3.04  
% 8.12/3.04  %Background operators:
% 8.12/3.04  
% 8.12/3.04  
% 8.12/3.04  %Foreground operators:
% 8.12/3.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.12/3.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.12/3.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.12/3.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.12/3.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.12/3.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.12/3.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.12/3.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.12/3.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.12/3.04  tff('#skF_2', type, '#skF_2': $i).
% 8.12/3.04  tff('#skF_3', type, '#skF_3': $i).
% 8.12/3.04  tff('#skF_1', type, '#skF_1': $i).
% 8.12/3.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.12/3.04  tff('#skF_4', type, '#skF_4': $i).
% 8.12/3.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.12/3.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.12/3.04  
% 8.12/3.05  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 8.12/3.05  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.12/3.05  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.12/3.05  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.12/3.05  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.12/3.05  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.12/3.05  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.12/3.05  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 8.12/3.05  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.12/3.05  tff(c_32, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.12/3.05  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.12/3.05  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.12/3.05  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.12/3.05  tff(c_127, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.12/3.05  tff(c_138, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_127])).
% 8.12/3.05  tff(c_216, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.12/3.05  tff(c_237, plain, (![B_6]: (k4_xboole_0(B_6, k1_xboole_0)=k3_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_138, c_216])).
% 8.12/3.05  tff(c_243, plain, (![B_6]: (k4_xboole_0(B_6, k1_xboole_0)=B_6)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_237])).
% 8.12/3.05  tff(c_30, plain, (![A_22, B_23]: (r1_tarski(k1_tarski(A_22), B_23) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.12/3.05  tff(c_535, plain, (![A_57, B_58]: (k4_xboole_0(k1_tarski(A_57), B_58)=k1_xboole_0 | ~r2_hidden(A_57, B_58))), inference(resolution, [status(thm)], [c_30, c_127])).
% 8.12/3.05  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.12/3.05  tff(c_545, plain, (![A_57, B_58]: (k4_xboole_0(k1_tarski(A_57), k1_xboole_0)=k3_xboole_0(k1_tarski(A_57), B_58) | ~r2_hidden(A_57, B_58))), inference(superposition, [status(thm), theory('equality')], [c_535, c_20])).
% 8.12/3.05  tff(c_14035, plain, (![A_171, B_172]: (k3_xboole_0(k1_tarski(A_171), B_172)=k1_tarski(A_171) | ~r2_hidden(A_171, B_172))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_545])).
% 8.12/3.05  tff(c_63, plain, (![B_27, A_28]: (k3_xboole_0(B_27, A_28)=k3_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.12/3.05  tff(c_36, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.12/3.05  tff(c_78, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_63, c_36])).
% 8.12/3.05  tff(c_38, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.12/3.05  tff(c_139, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_127])).
% 8.12/3.05  tff(c_234, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_139, c_216])).
% 8.12/3.05  tff(c_426, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_243, c_234])).
% 8.12/3.05  tff(c_451, plain, (![A_54, B_55, C_56]: (k3_xboole_0(k3_xboole_0(A_54, B_55), C_56)=k3_xboole_0(A_54, k3_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.12/3.05  tff(c_486, plain, (![C_56]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_56))=k3_xboole_0('#skF_1', C_56))), inference(superposition, [status(thm), theory('equality')], [c_426, c_451])).
% 8.12/3.05  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.12/3.05  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.12/3.05  tff(c_231, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, k3_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_216])).
% 8.12/3.05  tff(c_657, plain, (![A_62, B_63]: (k3_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_231])).
% 8.12/3.05  tff(c_721, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_657])).
% 8.12/3.05  tff(c_3589, plain, (![B_103, A_104, B_105]: (k3_xboole_0(B_103, k3_xboole_0(A_104, B_105))=k3_xboole_0(A_104, k3_xboole_0(B_105, B_103)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_451])).
% 8.12/3.05  tff(c_5221, plain, (![B_112]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_112))=k3_xboole_0(B_112, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_426, c_3589])).
% 8.12/3.05  tff(c_5341, plain, (![A_1]: (k3_xboole_0(k3_xboole_0(A_1, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', A_1)))), inference(superposition, [status(thm), theory('equality')], [c_721, c_5221])).
% 8.12/3.05  tff(c_8552, plain, (![A_137]: (k3_xboole_0(k3_xboole_0(A_137, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', A_137))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_5341])).
% 8.12/3.05  tff(c_8698, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_78, c_8552])).
% 8.12/3.05  tff(c_14105, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14035, c_8698])).
% 8.12/3.05  tff(c_14374, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14105])).
% 8.12/3.05  tff(c_14376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_14374])).
% 8.12/3.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.12/3.06  
% 8.12/3.06  Inference rules
% 8.12/3.06  ----------------------
% 8.12/3.06  #Ref     : 0
% 8.12/3.06  #Sup     : 3503
% 8.12/3.06  #Fact    : 0
% 8.12/3.06  #Define  : 0
% 8.12/3.06  #Split   : 1
% 8.12/3.06  #Chain   : 0
% 8.12/3.06  #Close   : 0
% 8.12/3.06  
% 8.12/3.06  Ordering : KBO
% 8.12/3.06  
% 8.12/3.06  Simplification rules
% 8.12/3.06  ----------------------
% 8.12/3.06  #Subsume      : 123
% 8.12/3.06  #Demod        : 4509
% 8.12/3.06  #Tautology    : 2205
% 8.12/3.06  #SimpNegUnit  : 1
% 8.12/3.06  #BackRed      : 1
% 8.12/3.06  
% 8.12/3.06  #Partial instantiations: 0
% 8.12/3.06  #Strategies tried      : 1
% 8.12/3.06  
% 8.12/3.06  Timing (in seconds)
% 8.12/3.06  ----------------------
% 8.30/3.06  Preprocessing        : 0.29
% 8.30/3.06  Parsing              : 0.15
% 8.30/3.06  CNF conversion       : 0.02
% 8.30/3.06  Main loop            : 2.01
% 8.30/3.06  Inferencing          : 0.41
% 8.30/3.06  Reduction            : 1.23
% 8.30/3.06  Demodulation         : 1.10
% 8.30/3.06  BG Simplification    : 0.05
% 8.30/3.06  Subsumption          : 0.24
% 8.30/3.06  Abstraction          : 0.08
% 8.30/3.06  MUC search           : 0.00
% 8.30/3.06  Cooper               : 0.00
% 8.30/3.06  Total                : 2.32
% 8.30/3.06  Index Insertion      : 0.00
% 8.30/3.06  Index Deletion       : 0.00
% 8.30/3.06  Index Matching       : 0.00
% 8.30/3.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
