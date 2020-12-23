%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:46 EST 2020

% Result     : Theorem 15.91s
% Output     : CNFRefutation 15.97s
% Verified   : 
% Statistics : Number of formulae       :   60 (  72 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 (  88 expanded)
%              Number of equality atoms :   33 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(c_38,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_418,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_xboole_0(k2_tarski(A_86,C_87),B_88)
      | r2_hidden(C_87,B_88)
      | r2_hidden(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_134,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,k3_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_145,plain,(
    ! [A_58,B_59] :
      ( ~ r1_xboole_0(A_58,B_59)
      | k3_xboole_0(A_58,B_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_134])).

tff(c_13779,plain,(
    ! [A_269,C_270,B_271] :
      ( k3_xboole_0(k2_tarski(A_269,C_270),B_271) = k1_xboole_0
      | r2_hidden(C_270,B_271)
      | r2_hidden(A_269,B_271) ) ),
    inference(resolution,[status(thm)],[c_418,c_145])).

tff(c_54039,plain,(
    ! [A_620,A_621,C_622] :
      ( k3_xboole_0(A_620,k2_tarski(A_621,C_622)) = k1_xboole_0
      | r2_hidden(C_622,A_620)
      | r2_hidden(A_621,A_620) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_13779])).

tff(c_22,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_101,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1658,plain,(
    ! [A_131,B_132] : k3_xboole_0(k4_xboole_0(A_131,B_132),A_131) = k4_xboole_0(A_131,B_132) ),
    inference(resolution,[status(thm)],[c_20,c_101])).

tff(c_24,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_168,plain,(
    ! [A_63,B_64] :
      ( ~ r1_xboole_0(A_63,B_64)
      | k3_xboole_0(A_63,B_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_134])).

tff(c_173,plain,(
    ! [A_65,B_66] : k3_xboole_0(k4_xboole_0(A_65,B_66),B_66) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_168])).

tff(c_202,plain,(
    ! [B_2,A_65] : k3_xboole_0(B_2,k4_xboole_0(A_65,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_173])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_473,plain,(
    ! [A_90,B_91,C_92] : k5_xboole_0(k3_xboole_0(A_90,B_91),k3_xboole_0(C_92,B_91)) = k3_xboole_0(k5_xboole_0(A_90,C_92),B_91) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_480,plain,(
    ! [A_90,B_91] : k3_xboole_0(k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)),B_91) = k4_xboole_0(k3_xboole_0(A_90,B_91),B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_10])).

tff(c_525,plain,(
    ! [A_90,B_91] : k4_xboole_0(k3_xboole_0(A_90,B_91),B_91) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_2,c_10,c_480])).

tff(c_2033,plain,(
    ! [A_135,B_136] : k4_xboole_0(k4_xboole_0(A_135,B_136),A_135) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1658,c_525])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( B_20 = A_19
      | k4_xboole_0(B_20,A_19) != k4_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2075,plain,(
    ! [A_135,B_136] :
      ( k4_xboole_0(A_135,B_136) = A_135
      | k4_xboole_0(A_135,k4_xboole_0(A_135,B_136)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2033,c_18])).

tff(c_14429,plain,(
    ! [A_273,B_274] :
      ( k4_xboole_0(A_273,B_274) = A_273
      | k3_xboole_0(A_273,B_274) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2075])).

tff(c_34,plain,(
    k4_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_14809,plain,(
    k3_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14429,c_34])).

tff(c_54381,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_54039,c_14809])).

tff(c_54736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_54381])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.91/8.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.91/8.07  
% 15.91/8.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.91/8.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 15.91/8.07  
% 15.91/8.07  %Foreground sorts:
% 15.91/8.07  
% 15.91/8.07  
% 15.91/8.07  %Background operators:
% 15.91/8.07  
% 15.91/8.07  
% 15.91/8.07  %Foreground operators:
% 15.91/8.07  tff('#skF_2', type, '#skF_2': $i > $i).
% 15.91/8.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.91/8.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.91/8.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.91/8.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.91/8.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.91/8.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.91/8.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.91/8.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.91/8.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.91/8.07  tff('#skF_5', type, '#skF_5': $i).
% 15.91/8.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.91/8.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.91/8.07  tff('#skF_3', type, '#skF_3': $i).
% 15.91/8.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.91/8.07  tff('#skF_4', type, '#skF_4': $i).
% 15.91/8.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.91/8.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.91/8.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.91/8.07  
% 15.97/8.08  tff(f_96, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 15.97/8.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.97/8.08  tff(f_85, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 15.97/8.08  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 15.97/8.08  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 15.97/8.08  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.97/8.08  tff(f_65, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 15.97/8.08  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 15.97/8.08  tff(f_69, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 15.97/8.08  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.97/8.08  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 15.97/8.08  tff(f_63, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 15.97/8.08  tff(c_38, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.97/8.08  tff(c_36, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.97/8.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.97/8.08  tff(c_418, plain, (![A_86, C_87, B_88]: (r1_xboole_0(k2_tarski(A_86, C_87), B_88) | r2_hidden(C_87, B_88) | r2_hidden(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.97/8.08  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.97/8.08  tff(c_134, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.97/8.08  tff(c_145, plain, (![A_58, B_59]: (~r1_xboole_0(A_58, B_59) | k3_xboole_0(A_58, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_134])).
% 15.97/8.08  tff(c_13779, plain, (![A_269, C_270, B_271]: (k3_xboole_0(k2_tarski(A_269, C_270), B_271)=k1_xboole_0 | r2_hidden(C_270, B_271) | r2_hidden(A_269, B_271))), inference(resolution, [status(thm)], [c_418, c_145])).
% 15.97/8.08  tff(c_54039, plain, (![A_620, A_621, C_622]: (k3_xboole_0(A_620, k2_tarski(A_621, C_622))=k1_xboole_0 | r2_hidden(C_622, A_620) | r2_hidden(A_621, A_620))), inference(superposition, [status(thm), theory('equality')], [c_2, c_13779])).
% 15.97/8.08  tff(c_22, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.97/8.08  tff(c_20, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.97/8.08  tff(c_101, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.97/8.08  tff(c_1658, plain, (![A_131, B_132]: (k3_xboole_0(k4_xboole_0(A_131, B_132), A_131)=k4_xboole_0(A_131, B_132))), inference(resolution, [status(thm)], [c_20, c_101])).
% 15.97/8.08  tff(c_24, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.97/8.08  tff(c_168, plain, (![A_63, B_64]: (~r1_xboole_0(A_63, B_64) | k3_xboole_0(A_63, B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_134])).
% 15.97/8.08  tff(c_173, plain, (![A_65, B_66]: (k3_xboole_0(k4_xboole_0(A_65, B_66), B_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_168])).
% 15.97/8.08  tff(c_202, plain, (![B_2, A_65]: (k3_xboole_0(B_2, k4_xboole_0(A_65, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_173])).
% 15.97/8.08  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.97/8.08  tff(c_473, plain, (![A_90, B_91, C_92]: (k5_xboole_0(k3_xboole_0(A_90, B_91), k3_xboole_0(C_92, B_91))=k3_xboole_0(k5_xboole_0(A_90, C_92), B_91))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.97/8.08  tff(c_480, plain, (![A_90, B_91]: (k3_xboole_0(k5_xboole_0(A_90, k3_xboole_0(A_90, B_91)), B_91)=k4_xboole_0(k3_xboole_0(A_90, B_91), B_91))), inference(superposition, [status(thm), theory('equality')], [c_473, c_10])).
% 15.97/8.08  tff(c_525, plain, (![A_90, B_91]: (k4_xboole_0(k3_xboole_0(A_90, B_91), B_91)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_202, c_2, c_10, c_480])).
% 15.97/8.08  tff(c_2033, plain, (![A_135, B_136]: (k4_xboole_0(k4_xboole_0(A_135, B_136), A_135)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1658, c_525])).
% 15.97/8.08  tff(c_18, plain, (![B_20, A_19]: (B_20=A_19 | k4_xboole_0(B_20, A_19)!=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.97/8.08  tff(c_2075, plain, (![A_135, B_136]: (k4_xboole_0(A_135, B_136)=A_135 | k4_xboole_0(A_135, k4_xboole_0(A_135, B_136))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2033, c_18])).
% 15.97/8.08  tff(c_14429, plain, (![A_273, B_274]: (k4_xboole_0(A_273, B_274)=A_273 | k3_xboole_0(A_273, B_274)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2075])).
% 15.97/8.08  tff(c_34, plain, (k4_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.97/8.08  tff(c_14809, plain, (k3_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14429, c_34])).
% 15.97/8.08  tff(c_54381, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_54039, c_14809])).
% 15.97/8.08  tff(c_54736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_54381])).
% 15.97/8.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.97/8.08  
% 15.97/8.08  Inference rules
% 15.97/8.08  ----------------------
% 15.97/8.08  #Ref     : 1
% 15.97/8.08  #Sup     : 13924
% 15.97/8.08  #Fact    : 0
% 15.97/8.08  #Define  : 0
% 15.97/8.08  #Split   : 0
% 15.97/8.08  #Chain   : 0
% 15.97/8.08  #Close   : 0
% 15.97/8.08  
% 15.97/8.08  Ordering : KBO
% 15.97/8.08  
% 15.97/8.08  Simplification rules
% 15.97/8.08  ----------------------
% 15.97/8.08  #Subsume      : 981
% 15.97/8.08  #Demod        : 19295
% 15.97/8.08  #Tautology    : 8150
% 15.97/8.08  #SimpNegUnit  : 176
% 15.97/8.08  #BackRed      : 34
% 15.97/8.08  
% 15.97/8.08  #Partial instantiations: 0
% 15.97/8.08  #Strategies tried      : 1
% 15.97/8.08  
% 15.97/8.08  Timing (in seconds)
% 15.97/8.08  ----------------------
% 15.97/8.08  Preprocessing        : 0.30
% 15.97/8.09  Parsing              : 0.16
% 15.97/8.09  CNF conversion       : 0.02
% 15.97/8.09  Main loop            : 6.96
% 15.97/8.09  Inferencing          : 0.99
% 15.97/8.09  Reduction            : 4.30
% 15.97/8.09  Demodulation         : 3.89
% 15.97/8.09  BG Simplification    : 0.12
% 15.97/8.09  Subsumption          : 1.19
% 15.97/8.09  Abstraction          : 0.21
% 15.97/8.09  MUC search           : 0.00
% 15.97/8.09  Cooper               : 0.00
% 15.97/8.09  Total                : 7.29
% 15.97/8.09  Index Insertion      : 0.00
% 15.97/8.09  Index Deletion       : 0.00
% 15.97/8.09  Index Matching       : 0.00
% 15.97/8.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
