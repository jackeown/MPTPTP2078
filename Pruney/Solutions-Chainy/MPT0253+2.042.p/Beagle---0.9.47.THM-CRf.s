%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:19 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   59 (  65 expanded)
%              Number of leaves         :   32 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  64 expanded)
%              Number of equality atoms :   33 (  39 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_263,plain,(
    ! [A_80,B_81,C_82] :
      ( r1_tarski(k2_tarski(A_80,B_81),C_82)
      | ~ r2_hidden(B_81,C_82)
      | ~ r2_hidden(A_80,C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_765,plain,(
    ! [A_122,B_123,C_124] :
      ( k4_xboole_0(k2_tarski(A_122,B_123),C_124) = k1_xboole_0
      | ~ r2_hidden(B_123,C_124)
      | ~ r2_hidden(A_122,C_124) ) ),
    inference(resolution,[status(thm)],[c_263,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_781,plain,(
    ! [C_124,A_122,B_123] :
      ( k2_xboole_0(C_124,k2_tarski(A_122,B_123)) = k2_xboole_0(C_124,k1_xboole_0)
      | ~ r2_hidden(B_123,C_124)
      | ~ r2_hidden(A_122,C_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_10])).

tff(c_1108,plain,(
    ! [C_142,A_143,B_144] :
      ( k2_xboole_0(C_142,k2_tarski(A_143,B_144)) = C_142
      | ~ r2_hidden(B_144,C_142)
      | ~ r2_hidden(A_143,C_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_781])).

tff(c_103,plain,(
    ! [C_49,B_50,A_51] : k1_enumset1(C_49,B_50,A_51) = k1_enumset1(A_51,B_50,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_119,plain,(
    ! [C_49,B_50] : k1_enumset1(C_49,B_50,B_50) = k2_tarski(B_50,C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_20])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k2_tarski(A_15,B_16),k1_tarski(C_17)) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_377,plain,(
    ! [A_98,B_99,C_100,D_101] : k2_xboole_0(k2_tarski(A_98,B_99),k2_tarski(C_100,D_101)) = k2_enumset1(A_98,B_99,C_100,D_101) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_397,plain,(
    ! [A_98,B_99,A_18] : k2_xboole_0(k2_tarski(A_98,B_99),k1_tarski(A_18)) = k2_enumset1(A_98,B_99,A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_377])).

tff(c_402,plain,(
    ! [A_102,B_103,A_104] : k2_enumset1(A_102,B_103,A_104,A_104) = k1_enumset1(A_102,B_103,A_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_397])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] : k2_enumset1(A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_409,plain,(
    ! [B_103,A_104] : k1_enumset1(B_103,B_103,A_104) = k1_enumset1(B_103,A_104,A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_22])).

tff(c_421,plain,(
    ! [B_105,A_106] : k2_tarski(B_105,A_106) = k2_tarski(A_106,B_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_20,c_409])).

tff(c_28,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_517,plain,(
    ! [A_112,B_113] : k3_tarski(k2_tarski(A_112,B_113)) = k2_xboole_0(B_113,A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_28])).

tff(c_523,plain,(
    ! [B_113,A_112] : k2_xboole_0(B_113,A_112) = k2_xboole_0(A_112,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_28])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_543,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_36])).

tff(c_1114,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1108,c_543])).

tff(c_1175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:32:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.43  
% 2.72/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.44  %$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.44  
% 2.72/1.44  %Foreground sorts:
% 2.72/1.44  
% 2.72/1.44  
% 2.72/1.44  %Background operators:
% 2.72/1.44  
% 2.72/1.44  
% 2.72/1.44  %Foreground operators:
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.72/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.44  
% 2.72/1.45  tff(f_66, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 2.72/1.45  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.72/1.45  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.72/1.45  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.72/1.45  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.72/1.45  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 2.72/1.45  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.72/1.45  tff(f_41, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.72/1.45  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.72/1.45  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.72/1.45  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.72/1.45  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.72/1.45  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.72/1.45  tff(c_38, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.72/1.45  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.45  tff(c_263, plain, (![A_80, B_81, C_82]: (r1_tarski(k2_tarski(A_80, B_81), C_82) | ~r2_hidden(B_81, C_82) | ~r2_hidden(A_80, C_82))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.72/1.45  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.45  tff(c_765, plain, (![A_122, B_123, C_124]: (k4_xboole_0(k2_tarski(A_122, B_123), C_124)=k1_xboole_0 | ~r2_hidden(B_123, C_124) | ~r2_hidden(A_122, C_124))), inference(resolution, [status(thm)], [c_263, c_4])).
% 2.72/1.45  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.45  tff(c_781, plain, (![C_124, A_122, B_123]: (k2_xboole_0(C_124, k2_tarski(A_122, B_123))=k2_xboole_0(C_124, k1_xboole_0) | ~r2_hidden(B_123, C_124) | ~r2_hidden(A_122, C_124))), inference(superposition, [status(thm), theory('equality')], [c_765, c_10])).
% 2.72/1.45  tff(c_1108, plain, (![C_142, A_143, B_144]: (k2_xboole_0(C_142, k2_tarski(A_143, B_144))=C_142 | ~r2_hidden(B_144, C_142) | ~r2_hidden(A_143, C_142))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_781])).
% 2.72/1.45  tff(c_103, plain, (![C_49, B_50, A_51]: (k1_enumset1(C_49, B_50, A_51)=k1_enumset1(A_51, B_50, C_49))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.45  tff(c_20, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.45  tff(c_119, plain, (![C_49, B_50]: (k1_enumset1(C_49, B_50, B_50)=k2_tarski(B_50, C_49))), inference(superposition, [status(thm), theory('equality')], [c_103, c_20])).
% 2.72/1.45  tff(c_16, plain, (![A_15, B_16, C_17]: (k2_xboole_0(k2_tarski(A_15, B_16), k1_tarski(C_17))=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.72/1.45  tff(c_18, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.45  tff(c_377, plain, (![A_98, B_99, C_100, D_101]: (k2_xboole_0(k2_tarski(A_98, B_99), k2_tarski(C_100, D_101))=k2_enumset1(A_98, B_99, C_100, D_101))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.45  tff(c_397, plain, (![A_98, B_99, A_18]: (k2_xboole_0(k2_tarski(A_98, B_99), k1_tarski(A_18))=k2_enumset1(A_98, B_99, A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_18, c_377])).
% 2.72/1.45  tff(c_402, plain, (![A_102, B_103, A_104]: (k2_enumset1(A_102, B_103, A_104, A_104)=k1_enumset1(A_102, B_103, A_104))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_397])).
% 2.72/1.45  tff(c_22, plain, (![A_21, B_22, C_23]: (k2_enumset1(A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.45  tff(c_409, plain, (![B_103, A_104]: (k1_enumset1(B_103, B_103, A_104)=k1_enumset1(B_103, A_104, A_104))), inference(superposition, [status(thm), theory('equality')], [c_402, c_22])).
% 2.72/1.45  tff(c_421, plain, (![B_105, A_106]: (k2_tarski(B_105, A_106)=k2_tarski(A_106, B_105))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_20, c_409])).
% 2.72/1.45  tff(c_28, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.45  tff(c_517, plain, (![A_112, B_113]: (k3_tarski(k2_tarski(A_112, B_113))=k2_xboole_0(B_113, A_112))), inference(superposition, [status(thm), theory('equality')], [c_421, c_28])).
% 2.72/1.45  tff(c_523, plain, (![B_113, A_112]: (k2_xboole_0(B_113, A_112)=k2_xboole_0(A_112, B_113))), inference(superposition, [status(thm), theory('equality')], [c_517, c_28])).
% 2.72/1.45  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.72/1.45  tff(c_543, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_523, c_36])).
% 2.72/1.45  tff(c_1114, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1108, c_543])).
% 2.72/1.45  tff(c_1175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1114])).
% 2.72/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.45  
% 2.72/1.45  Inference rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Ref     : 0
% 2.72/1.45  #Sup     : 283
% 2.72/1.45  #Fact    : 0
% 2.72/1.45  #Define  : 0
% 2.72/1.45  #Split   : 0
% 2.72/1.45  #Chain   : 0
% 2.72/1.45  #Close   : 0
% 2.72/1.45  
% 2.72/1.45  Ordering : KBO
% 2.72/1.45  
% 2.72/1.45  Simplification rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Subsume      : 31
% 2.72/1.45  #Demod        : 94
% 2.72/1.45  #Tautology    : 156
% 2.72/1.45  #SimpNegUnit  : 0
% 2.72/1.45  #BackRed      : 1
% 2.72/1.45  
% 2.72/1.45  #Partial instantiations: 0
% 2.72/1.45  #Strategies tried      : 1
% 2.72/1.45  
% 2.72/1.45  Timing (in seconds)
% 2.72/1.45  ----------------------
% 2.72/1.45  Preprocessing        : 0.31
% 2.72/1.45  Parsing              : 0.17
% 2.72/1.45  CNF conversion       : 0.02
% 2.72/1.45  Main loop            : 0.38
% 2.72/1.45  Inferencing          : 0.15
% 2.72/1.45  Reduction            : 0.13
% 2.72/1.45  Demodulation         : 0.10
% 2.72/1.45  BG Simplification    : 0.02
% 2.72/1.45  Subsumption          : 0.05
% 2.72/1.45  Abstraction          : 0.02
% 2.72/1.45  MUC search           : 0.00
% 2.72/1.45  Cooper               : 0.00
% 2.72/1.45  Total                : 0.72
% 2.72/1.45  Index Insertion      : 0.00
% 2.72/1.45  Index Deletion       : 0.00
% 2.72/1.45  Index Matching       : 0.00
% 2.72/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
