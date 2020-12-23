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
% DateTime   : Thu Dec  3 09:48:58 EST 2020

% Result     : Theorem 10.10s
% Output     : CNFRefutation 10.10s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 104 expanded)
%              Number of leaves         :   32 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 147 expanded)
%              Number of equality atoms :   40 (  82 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_81,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_72,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_70,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_62,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_216,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [E_26,A_20,C_22] : r2_hidden(E_26,k1_enumset1(A_20,E_26,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_234,plain,(
    ! [A_60,B_61] : r2_hidden(A_60,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_40])).

tff(c_237,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_234])).

tff(c_42,plain,(
    ! [E_26,B_21,C_22] : r2_hidden(E_26,k1_enumset1(E_26,B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_60,plain,(
    ! [A_27,B_28,C_29] : k2_xboole_0(k1_tarski(A_27),k2_tarski(B_28,C_29)) = k1_enumset1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_238,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = A_62
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_249,plain,(
    ! [B_11] : k3_xboole_0(B_11,B_11) = B_11 ),
    inference(resolution,[status(thm)],[c_24,c_238])).

tff(c_319,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_331,plain,(
    ! [B_11] : k5_xboole_0(B_11,B_11) = k4_xboole_0(B_11,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_319])).

tff(c_74,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_248,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_238])).

tff(c_26,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_337,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k4_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_26])).

tff(c_625,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) = k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_337])).

tff(c_34,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_629,plain,(
    k5_xboole_0(k2_tarski('#skF_5','#skF_6'),k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4'))) = k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_34])).

tff(c_632,plain,(
    k5_xboole_0(k2_tarski('#skF_5','#skF_6'),k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4'))) = k1_enumset1('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2,c_629])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden(A_5,B_6)
      | r2_hidden(A_5,C_7)
      | ~ r2_hidden(A_5,k5_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_866,plain,(
    ! [A_5] :
      ( r2_hidden(A_5,k2_tarski('#skF_5','#skF_6'))
      | r2_hidden(A_5,k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')))
      | ~ r2_hidden(A_5,k1_enumset1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_12])).

tff(c_508,plain,(
    ! [A_89,C_90,B_91] :
      ( ~ r2_hidden(A_89,C_90)
      | ~ r2_hidden(A_89,B_91)
      | ~ r2_hidden(A_89,k5_xboole_0(B_91,C_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14954,plain,(
    ! [A_21765,A_21766,B_21767] :
      ( ~ r2_hidden(A_21765,k3_xboole_0(A_21766,B_21767))
      | ~ r2_hidden(A_21765,A_21766)
      | ~ r2_hidden(A_21765,k4_xboole_0(A_21766,B_21767)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_508])).

tff(c_14977,plain,(
    ! [A_21765] :
      ( ~ r2_hidden(A_21765,k3_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')))
      | ~ r2_hidden(A_21765,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_21765,k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_14954])).

tff(c_14993,plain,(
    ! [A_21864] :
      ( ~ r2_hidden(A_21864,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_21864,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_21864,k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_14977])).

tff(c_15088,plain,(
    ! [A_22060] :
      ( ~ r2_hidden(A_22060,k1_tarski('#skF_4'))
      | r2_hidden(A_22060,k2_tarski('#skF_5','#skF_6'))
      | ~ r2_hidden(A_22060,k1_enumset1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_866,c_14993])).

tff(c_15136,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | r2_hidden('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_42,c_15088])).

tff(c_15150,plain,(
    r2_hidden('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_15136])).

tff(c_64,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1472,plain,(
    ! [E_139,C_140,B_141,A_142] :
      ( E_139 = C_140
      | E_139 = B_141
      | E_139 = A_142
      | ~ r2_hidden(E_139,k1_enumset1(A_142,B_141,C_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1490,plain,(
    ! [E_139,B_32,A_31] :
      ( E_139 = B_32
      | E_139 = A_31
      | E_139 = A_31
      | ~ r2_hidden(E_139,k2_tarski(A_31,B_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1472])).

tff(c_15153,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15150,c_1490])).

tff(c_15157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_72,c_70,c_15153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:43:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.10/3.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.10/3.36  
% 10.10/3.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.10/3.36  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 10.10/3.36  
% 10.10/3.36  %Foreground sorts:
% 10.10/3.36  
% 10.10/3.36  
% 10.10/3.36  %Background operators:
% 10.10/3.36  
% 10.10/3.36  
% 10.10/3.36  %Foreground operators:
% 10.10/3.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.10/3.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.10/3.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.10/3.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.10/3.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.10/3.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.10/3.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.10/3.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.10/3.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.10/3.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.10/3.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.10/3.36  tff('#skF_5', type, '#skF_5': $i).
% 10.10/3.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 10.10/3.36  tff('#skF_6', type, '#skF_6': $i).
% 10.10/3.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.10/3.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.10/3.36  tff('#skF_4', type, '#skF_4': $i).
% 10.10/3.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.10/3.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.10/3.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 10.10/3.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.10/3.36  
% 10.10/3.37  tff(f_97, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 10.10/3.37  tff(f_81, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.10/3.37  tff(f_83, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 10.10/3.37  tff(f_77, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 10.10/3.37  tff(f_79, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 10.10/3.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.10/3.37  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.10/3.37  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.10/3.37  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.10/3.37  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.10/3.37  tff(f_36, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 10.10/3.37  tff(c_72, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.10/3.37  tff(c_70, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.10/3.37  tff(c_62, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.10/3.37  tff(c_216, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.10/3.37  tff(c_40, plain, (![E_26, A_20, C_22]: (r2_hidden(E_26, k1_enumset1(A_20, E_26, C_22)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.10/3.37  tff(c_234, plain, (![A_60, B_61]: (r2_hidden(A_60, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_216, c_40])).
% 10.10/3.37  tff(c_237, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_234])).
% 10.10/3.37  tff(c_42, plain, (![E_26, B_21, C_22]: (r2_hidden(E_26, k1_enumset1(E_26, B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.10/3.37  tff(c_60, plain, (![A_27, B_28, C_29]: (k2_xboole_0(k1_tarski(A_27), k2_tarski(B_28, C_29))=k1_enumset1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.10/3.37  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.10/3.37  tff(c_24, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.10/3.37  tff(c_238, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=A_62 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.10/3.37  tff(c_249, plain, (![B_11]: (k3_xboole_0(B_11, B_11)=B_11)), inference(resolution, [status(thm)], [c_24, c_238])).
% 10.10/3.37  tff(c_319, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.10/3.37  tff(c_331, plain, (![B_11]: (k5_xboole_0(B_11, B_11)=k4_xboole_0(B_11, B_11))), inference(superposition, [status(thm), theory('equality')], [c_249, c_319])).
% 10.10/3.37  tff(c_74, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.10/3.37  tff(c_248, plain, (k3_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_74, c_238])).
% 10.10/3.37  tff(c_26, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.10/3.37  tff(c_337, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k4_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_26])).
% 10.10/3.37  tff(c_625, plain, (k4_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_337])).
% 10.10/3.37  tff(c_34, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.10/3.37  tff(c_629, plain, (k5_xboole_0(k2_tarski('#skF_5', '#skF_6'), k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4')))=k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_625, c_34])).
% 10.10/3.37  tff(c_632, plain, (k5_xboole_0(k2_tarski('#skF_5', '#skF_6'), k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4')))=k1_enumset1('#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2, c_629])).
% 10.10/3.37  tff(c_12, plain, (![A_5, B_6, C_7]: (r2_hidden(A_5, B_6) | r2_hidden(A_5, C_7) | ~r2_hidden(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.10/3.37  tff(c_866, plain, (![A_5]: (r2_hidden(A_5, k2_tarski('#skF_5', '#skF_6')) | r2_hidden(A_5, k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))) | ~r2_hidden(A_5, k1_enumset1('#skF_4', '#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_632, c_12])).
% 10.10/3.37  tff(c_508, plain, (![A_89, C_90, B_91]: (~r2_hidden(A_89, C_90) | ~r2_hidden(A_89, B_91) | ~r2_hidden(A_89, k5_xboole_0(B_91, C_90)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.10/3.37  tff(c_14954, plain, (![A_21765, A_21766, B_21767]: (~r2_hidden(A_21765, k3_xboole_0(A_21766, B_21767)) | ~r2_hidden(A_21765, A_21766) | ~r2_hidden(A_21765, k4_xboole_0(A_21766, B_21767)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_508])).
% 10.10/3.37  tff(c_14977, plain, (![A_21765]: (~r2_hidden(A_21765, k3_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))) | ~r2_hidden(A_21765, k1_tarski('#skF_4')) | ~r2_hidden(A_21765, k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_625, c_14954])).
% 10.10/3.37  tff(c_14993, plain, (![A_21864]: (~r2_hidden(A_21864, k1_tarski('#skF_4')) | ~r2_hidden(A_21864, k1_tarski('#skF_4')) | ~r2_hidden(A_21864, k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_14977])).
% 10.10/3.37  tff(c_15088, plain, (![A_22060]: (~r2_hidden(A_22060, k1_tarski('#skF_4')) | r2_hidden(A_22060, k2_tarski('#skF_5', '#skF_6')) | ~r2_hidden(A_22060, k1_enumset1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_866, c_14993])).
% 10.10/3.37  tff(c_15136, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | r2_hidden('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_15088])).
% 10.10/3.37  tff(c_15150, plain, (r2_hidden('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_15136])).
% 10.10/3.37  tff(c_64, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.10/3.37  tff(c_1472, plain, (![E_139, C_140, B_141, A_142]: (E_139=C_140 | E_139=B_141 | E_139=A_142 | ~r2_hidden(E_139, k1_enumset1(A_142, B_141, C_140)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.10/3.37  tff(c_1490, plain, (![E_139, B_32, A_31]: (E_139=B_32 | E_139=A_31 | E_139=A_31 | ~r2_hidden(E_139, k2_tarski(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1472])).
% 10.10/3.37  tff(c_15153, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_15150, c_1490])).
% 10.10/3.37  tff(c_15157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_72, c_70, c_15153])).
% 10.10/3.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.10/3.37  
% 10.10/3.37  Inference rules
% 10.10/3.37  ----------------------
% 10.10/3.37  #Ref     : 0
% 10.10/3.37  #Sup     : 2211
% 10.10/3.37  #Fact    : 48
% 10.10/3.37  #Define  : 0
% 10.10/3.37  #Split   : 6
% 10.10/3.37  #Chain   : 0
% 10.10/3.37  #Close   : 0
% 10.10/3.37  
% 10.10/3.37  Ordering : KBO
% 10.10/3.37  
% 10.10/3.37  Simplification rules
% 10.10/3.37  ----------------------
% 10.10/3.37  #Subsume      : 623
% 10.10/3.37  #Demod        : 629
% 10.10/3.37  #Tautology    : 575
% 10.10/3.37  #SimpNegUnit  : 9
% 10.10/3.37  #BackRed      : 29
% 10.10/3.37  
% 10.10/3.37  #Partial instantiations: 10944
% 10.10/3.37  #Strategies tried      : 1
% 10.10/3.37  
% 10.10/3.37  Timing (in seconds)
% 10.10/3.37  ----------------------
% 10.10/3.38  Preprocessing        : 0.33
% 10.10/3.38  Parsing              : 0.17
% 10.10/3.38  CNF conversion       : 0.02
% 10.10/3.38  Main loop            : 2.27
% 10.10/3.38  Inferencing          : 1.10
% 10.10/3.38  Reduction            : 0.65
% 10.10/3.38  Demodulation         : 0.52
% 10.10/3.38  BG Simplification    : 0.09
% 10.10/3.38  Subsumption          : 0.33
% 10.10/3.38  Abstraction          : 0.10
% 10.10/3.38  MUC search           : 0.00
% 10.10/3.38  Cooper               : 0.00
% 10.10/3.38  Total                : 2.64
% 10.10/3.38  Index Insertion      : 0.00
% 10.10/3.38  Index Deletion       : 0.00
% 10.10/3.38  Index Matching       : 0.00
% 10.10/3.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
