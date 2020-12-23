%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:09 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   62 (  79 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 (  77 expanded)
%              Number of equality atoms :   40 (  58 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_103,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_93])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_207,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k4_xboole_0(B_49,A_48)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_225,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k2_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_207])).

tff(c_228,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_225])).

tff(c_274,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_310,plain,(
    ! [B_55] : k3_xboole_0(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_337,plain,(
    ! [B_56] : k3_xboole_0(B_56,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_345,plain,(
    ! [B_56] : k5_xboole_0(B_56,k1_xboole_0) = k4_xboole_0(B_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_4])).

tff(c_367,plain,(
    ! [B_56] : k4_xboole_0(B_56,k1_xboole_0) = B_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_345])).

tff(c_296,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = k3_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_274])).

tff(c_457,plain,(
    ! [A_63] : k3_xboole_0(A_63,A_63) = A_63 ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_296])).

tff(c_475,plain,(
    ! [A_63] : k5_xboole_0(A_63,A_63) = k4_xboole_0(A_63,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_4])).

tff(c_495,plain,(
    ! [A_63] : k5_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_475])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( k3_xboole_0(B_22,k1_tarski(A_21)) = k1_tarski(A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_192,plain,(
    ! [A_46,B_47] : k5_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_575,plain,(
    ! [B_70,A_71] : k5_xboole_0(B_70,k3_xboole_0(A_71,B_70)) = k4_xboole_0(B_70,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_192])).

tff(c_599,plain,(
    ! [A_21,B_22] :
      ( k5_xboole_0(k1_tarski(A_21),k1_tarski(A_21)) = k4_xboole_0(k1_tarski(A_21),B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_575])).

tff(c_730,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(k1_tarski(A_76),B_77) = k1_xboole_0
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_599])).

tff(c_34,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_786,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_34])).

tff(c_20,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_567,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_xboole_0(k2_tarski(A_67,C_68),B_69)
      | r2_hidden(C_68,B_69)
      | r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_880,plain,(
    ! [A_82,B_83] :
      ( r1_xboole_0(k1_tarski(A_82),B_83)
      | r2_hidden(A_82,B_83)
      | r2_hidden(A_82,B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_567])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_885,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(k1_tarski(A_84),B_85) = k1_tarski(A_84)
      | r2_hidden(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_880,c_14])).

tff(c_32,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_920,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_885,c_32])).

tff(c_956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_786,c_920])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:27:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.36  
% 2.81/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.37  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.81/1.37  
% 2.81/1.37  %Foreground sorts:
% 2.81/1.37  
% 2.81/1.37  
% 2.81/1.37  %Background operators:
% 2.81/1.37  
% 2.81/1.37  
% 2.81/1.37  %Foreground operators:
% 2.81/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.81/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.81/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.81/1.37  
% 2.81/1.38  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.81/1.38  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.81/1.38  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.81/1.38  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.81/1.38  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.81/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.81/1.38  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.81/1.38  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 2.81/1.38  tff(f_70, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 2.81/1.38  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.81/1.38  tff(f_65, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.81/1.38  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.81/1.38  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.38  tff(c_93, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(A_33, B_34))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.38  tff(c_103, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_93])).
% 2.81/1.38  tff(c_12, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.38  tff(c_207, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k4_xboole_0(B_49, A_48))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.38  tff(c_225, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k2_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_207])).
% 2.81/1.38  tff(c_228, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_225])).
% 2.81/1.38  tff(c_274, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.38  tff(c_310, plain, (![B_55]: (k3_xboole_0(k1_xboole_0, B_55)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_274, c_12])).
% 2.81/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.38  tff(c_337, plain, (![B_56]: (k3_xboole_0(B_56, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_310, c_2])).
% 2.81/1.38  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.38  tff(c_345, plain, (![B_56]: (k5_xboole_0(B_56, k1_xboole_0)=k4_xboole_0(B_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_337, c_4])).
% 2.81/1.38  tff(c_367, plain, (![B_56]: (k4_xboole_0(B_56, k1_xboole_0)=B_56)), inference(demodulation, [status(thm), theory('equality')], [c_228, c_345])).
% 2.81/1.38  tff(c_296, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=k3_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_103, c_274])).
% 2.81/1.38  tff(c_457, plain, (![A_63]: (k3_xboole_0(A_63, A_63)=A_63)), inference(demodulation, [status(thm), theory('equality')], [c_367, c_296])).
% 2.81/1.38  tff(c_475, plain, (![A_63]: (k5_xboole_0(A_63, A_63)=k4_xboole_0(A_63, A_63))), inference(superposition, [status(thm), theory('equality')], [c_457, c_4])).
% 2.81/1.38  tff(c_495, plain, (![A_63]: (k5_xboole_0(A_63, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_475])).
% 2.81/1.38  tff(c_26, plain, (![B_22, A_21]: (k3_xboole_0(B_22, k1_tarski(A_21))=k1_tarski(A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.81/1.38  tff(c_192, plain, (![A_46, B_47]: (k5_xboole_0(A_46, k3_xboole_0(A_46, B_47))=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.38  tff(c_575, plain, (![B_70, A_71]: (k5_xboole_0(B_70, k3_xboole_0(A_71, B_70))=k4_xboole_0(B_70, A_71))), inference(superposition, [status(thm), theory('equality')], [c_2, c_192])).
% 2.81/1.38  tff(c_599, plain, (![A_21, B_22]: (k5_xboole_0(k1_tarski(A_21), k1_tarski(A_21))=k4_xboole_0(k1_tarski(A_21), B_22) | ~r2_hidden(A_21, B_22))), inference(superposition, [status(thm), theory('equality')], [c_26, c_575])).
% 2.81/1.38  tff(c_730, plain, (![A_76, B_77]: (k4_xboole_0(k1_tarski(A_76), B_77)=k1_xboole_0 | ~r2_hidden(A_76, B_77))), inference(demodulation, [status(thm), theory('equality')], [c_495, c_599])).
% 2.81/1.38  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.38  tff(c_786, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_730, c_34])).
% 2.81/1.38  tff(c_20, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.38  tff(c_567, plain, (![A_67, C_68, B_69]: (r1_xboole_0(k2_tarski(A_67, C_68), B_69) | r2_hidden(C_68, B_69) | r2_hidden(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.81/1.38  tff(c_880, plain, (![A_82, B_83]: (r1_xboole_0(k1_tarski(A_82), B_83) | r2_hidden(A_82, B_83) | r2_hidden(A_82, B_83))), inference(superposition, [status(thm), theory('equality')], [c_20, c_567])).
% 2.81/1.38  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.38  tff(c_885, plain, (![A_84, B_85]: (k4_xboole_0(k1_tarski(A_84), B_85)=k1_tarski(A_84) | r2_hidden(A_84, B_85))), inference(resolution, [status(thm)], [c_880, c_14])).
% 2.81/1.38  tff(c_32, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.38  tff(c_920, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_885, c_32])).
% 2.81/1.38  tff(c_956, plain, $false, inference(negUnitSimplification, [status(thm)], [c_786, c_920])).
% 2.81/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.38  
% 2.81/1.38  Inference rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Ref     : 0
% 2.81/1.38  #Sup     : 219
% 2.81/1.38  #Fact    : 0
% 2.81/1.38  #Define  : 0
% 2.81/1.38  #Split   : 0
% 2.81/1.38  #Chain   : 0
% 2.81/1.38  #Close   : 0
% 2.81/1.38  
% 2.81/1.38  Ordering : KBO
% 2.81/1.38  
% 2.81/1.38  Simplification rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Subsume      : 15
% 2.81/1.38  #Demod        : 85
% 2.81/1.38  #Tautology    : 150
% 2.81/1.38  #SimpNegUnit  : 1
% 2.81/1.38  #BackRed      : 2
% 2.81/1.38  
% 2.81/1.38  #Partial instantiations: 0
% 2.81/1.38  #Strategies tried      : 1
% 2.81/1.38  
% 2.81/1.38  Timing (in seconds)
% 2.81/1.38  ----------------------
% 2.81/1.38  Preprocessing        : 0.30
% 2.81/1.38  Parsing              : 0.17
% 2.81/1.38  CNF conversion       : 0.02
% 2.81/1.38  Main loop            : 0.30
% 2.81/1.38  Inferencing          : 0.12
% 2.81/1.38  Reduction            : 0.10
% 2.81/1.38  Demodulation         : 0.08
% 2.81/1.38  BG Simplification    : 0.02
% 2.81/1.38  Subsumption          : 0.04
% 2.81/1.38  Abstraction          : 0.02
% 2.81/1.38  MUC search           : 0.00
% 2.81/1.38  Cooper               : 0.00
% 2.81/1.38  Total                : 0.64
% 2.81/1.38  Index Insertion      : 0.00
% 2.81/1.38  Index Deletion       : 0.00
% 2.81/1.38  Index Matching       : 0.00
% 2.81/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
