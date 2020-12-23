%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:23 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   69 (  81 expanded)
%              Number of leaves         :   35 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :   55 (  68 expanded)
%              Number of equality atoms :   48 (  61 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_66,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_54,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    ! [A_33,B_34,C_35] : k2_enumset1(A_33,A_33,B_34,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1126,plain,(
    ! [A_2241,B_2242,C_2243,D_2244] : k2_xboole_0(k1_enumset1(A_2241,B_2242,C_2243),k1_tarski(D_2244)) = k2_enumset1(A_2241,B_2242,C_2243,D_2244) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1192,plain,(
    ! [A_31,B_32,D_2244] : k2_xboole_0(k2_tarski(A_31,B_32),k1_tarski(D_2244)) = k2_enumset1(A_31,A_31,B_32,D_2244) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1126])).

tff(c_1196,plain,(
    ! [A_2293,B_2294,D_2295] : k2_xboole_0(k2_tarski(A_2293,B_2294),k1_tarski(D_2295)) = k1_enumset1(A_2293,B_2294,D_2295) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1192])).

tff(c_1253,plain,(
    ! [A_30,D_2295] : k2_xboole_0(k1_tarski(A_30),k1_tarski(D_2295)) = k1_enumset1(A_30,A_30,D_2295) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1196])).

tff(c_1257,plain,(
    ! [A_2344,D_2345] : k2_xboole_0(k1_tarski(A_2344),k1_tarski(D_2345)) = k2_tarski(A_2344,D_2345) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1253])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_303,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k4_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_318,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_303])).

tff(c_322,plain,(
    ! [A_84] : k4_xboole_0(A_84,k1_xboole_0) = A_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_318])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_331,plain,(
    ! [A_84] : k4_xboole_0(A_84,A_84) = k3_xboole_0(A_84,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_8])).

tff(c_336,plain,(
    ! [A_84] : k4_xboole_0(A_84,A_84) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_331])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_315,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_303])).

tff(c_372,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_315])).

tff(c_68,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_312,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_303])).

tff(c_449,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_312])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_453,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_12])).

tff(c_459,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_453])).

tff(c_1263,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_459])).

tff(c_127,plain,(
    ! [A_67,B_68] : k1_enumset1(A_67,A_67,B_68) = k2_tarski(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [E_17,A_11,B_12] : r2_hidden(E_17,k1_enumset1(A_11,B_12,E_17)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,(
    ! [B_68,A_67] : r2_hidden(B_68,k2_tarski(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_16])).

tff(c_1425,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1263,c_139])).

tff(c_38,plain,(
    ! [C_22,A_18] :
      ( C_22 = A_18
      | ~ r2_hidden(C_22,k1_tarski(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1455,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1425,c_38])).

tff(c_1495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1455])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:34:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.58  
% 3.20/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.58  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 3.20/1.58  
% 3.20/1.58  %Foreground sorts:
% 3.20/1.58  
% 3.20/1.58  
% 3.20/1.58  %Background operators:
% 3.20/1.58  
% 3.20/1.58  
% 3.20/1.58  %Foreground operators:
% 3.20/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.20/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.20/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.20/1.58  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.20/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.20/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.20/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.20/1.58  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.20/1.58  
% 3.20/1.59  tff(f_80, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.20/1.59  tff(f_67, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.20/1.59  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.20/1.59  tff(f_69, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.20/1.59  tff(f_63, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.20/1.59  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.20/1.59  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.20/1.59  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.20/1.59  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.20/1.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.20/1.59  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.20/1.59  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.20/1.59  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.20/1.59  tff(c_66, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.59  tff(c_56, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.59  tff(c_54, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.20/1.59  tff(c_58, plain, (![A_33, B_34, C_35]: (k2_enumset1(A_33, A_33, B_34, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.59  tff(c_1126, plain, (![A_2241, B_2242, C_2243, D_2244]: (k2_xboole_0(k1_enumset1(A_2241, B_2242, C_2243), k1_tarski(D_2244))=k2_enumset1(A_2241, B_2242, C_2243, D_2244))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.59  tff(c_1192, plain, (![A_31, B_32, D_2244]: (k2_xboole_0(k2_tarski(A_31, B_32), k1_tarski(D_2244))=k2_enumset1(A_31, A_31, B_32, D_2244))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1126])).
% 3.20/1.59  tff(c_1196, plain, (![A_2293, B_2294, D_2295]: (k2_xboole_0(k2_tarski(A_2293, B_2294), k1_tarski(D_2295))=k1_enumset1(A_2293, B_2294, D_2295))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1192])).
% 3.20/1.59  tff(c_1253, plain, (![A_30, D_2295]: (k2_xboole_0(k1_tarski(A_30), k1_tarski(D_2295))=k1_enumset1(A_30, A_30, D_2295))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1196])).
% 3.20/1.59  tff(c_1257, plain, (![A_2344, D_2345]: (k2_xboole_0(k1_tarski(A_2344), k1_tarski(D_2345))=k2_tarski(A_2344, D_2345))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1253])).
% 3.20/1.59  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.59  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.59  tff(c_303, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k4_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.59  tff(c_318, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_303])).
% 3.20/1.59  tff(c_322, plain, (![A_84]: (k4_xboole_0(A_84, k1_xboole_0)=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_318])).
% 3.20/1.59  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.20/1.59  tff(c_331, plain, (![A_84]: (k4_xboole_0(A_84, A_84)=k3_xboole_0(A_84, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_322, c_8])).
% 3.20/1.59  tff(c_336, plain, (![A_84]: (k4_xboole_0(A_84, A_84)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_331])).
% 3.20/1.59  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.59  tff(c_315, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_303])).
% 3.20/1.59  tff(c_372, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_336, c_315])).
% 3.20/1.59  tff(c_68, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.59  tff(c_312, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_303])).
% 3.20/1.59  tff(c_449, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_372, c_312])).
% 3.20/1.59  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.20/1.59  tff(c_453, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_449, c_12])).
% 3.20/1.59  tff(c_459, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_453])).
% 3.20/1.59  tff(c_1263, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1257, c_459])).
% 3.20/1.59  tff(c_127, plain, (![A_67, B_68]: (k1_enumset1(A_67, A_67, B_68)=k2_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.59  tff(c_16, plain, (![E_17, A_11, B_12]: (r2_hidden(E_17, k1_enumset1(A_11, B_12, E_17)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.20/1.59  tff(c_139, plain, (![B_68, A_67]: (r2_hidden(B_68, k2_tarski(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_16])).
% 3.20/1.59  tff(c_1425, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1263, c_139])).
% 3.20/1.59  tff(c_38, plain, (![C_22, A_18]: (C_22=A_18 | ~r2_hidden(C_22, k1_tarski(A_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.59  tff(c_1455, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1425, c_38])).
% 3.20/1.59  tff(c_1495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1455])).
% 3.20/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.59  
% 3.20/1.59  Inference rules
% 3.20/1.59  ----------------------
% 3.20/1.59  #Ref     : 0
% 3.20/1.59  #Sup     : 201
% 3.20/1.59  #Fact    : 0
% 3.20/1.59  #Define  : 0
% 3.20/1.59  #Split   : 3
% 3.20/1.59  #Chain   : 0
% 3.20/1.59  #Close   : 0
% 3.20/1.59  
% 3.20/1.59  Ordering : KBO
% 3.20/1.59  
% 3.20/1.59  Simplification rules
% 3.20/1.59  ----------------------
% 3.20/1.59  #Subsume      : 5
% 3.20/1.59  #Demod        : 62
% 3.20/1.59  #Tautology    : 113
% 3.20/1.59  #SimpNegUnit  : 1
% 3.20/1.59  #BackRed      : 0
% 3.20/1.59  
% 3.20/1.59  #Partial instantiations: 882
% 3.20/1.59  #Strategies tried      : 1
% 3.20/1.59  
% 3.20/1.59  Timing (in seconds)
% 3.20/1.59  ----------------------
% 3.20/1.60  Preprocessing        : 0.40
% 3.20/1.60  Parsing              : 0.20
% 3.20/1.60  CNF conversion       : 0.03
% 3.20/1.60  Main loop            : 0.43
% 3.20/1.60  Inferencing          : 0.20
% 3.20/1.60  Reduction            : 0.12
% 3.20/1.60  Demodulation         : 0.09
% 3.20/1.60  BG Simplification    : 0.03
% 3.20/1.60  Subsumption          : 0.06
% 3.20/1.60  Abstraction          : 0.02
% 3.20/1.60  MUC search           : 0.00
% 3.20/1.60  Cooper               : 0.00
% 3.20/1.60  Total                : 0.86
% 3.20/1.60  Index Insertion      : 0.00
% 3.20/1.60  Index Deletion       : 0.00
% 3.20/1.60  Index Matching       : 0.00
% 3.20/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
