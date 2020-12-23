%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:40 EST 2020

% Result     : Theorem 6.42s
% Output     : CNFRefutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 107 expanded)
%              Number of leaves         :   38 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 108 expanded)
%              Number of equality atoms :   28 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_88,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_72,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_208,plain,(
    ! [A_88,B_89] : k1_enumset1(A_88,A_88,B_89) = k2_tarski(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    ! [E_36,A_30,C_32] : r2_hidden(E_36,k1_enumset1(A_30,E_36,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_226,plain,(
    ! [A_90,B_91] : r2_hidden(A_90,k2_tarski(A_90,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_52])).

tff(c_229,plain,(
    ! [A_37] : r2_hidden(A_37,k1_tarski(A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_226])).

tff(c_40,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    ! [A_28,B_29] : k5_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_983,plain,(
    ! [A_136,B_137,C_138] : k5_xboole_0(k5_xboole_0(A_136,B_137),C_138) = k5_xboole_0(A_136,k5_xboole_0(B_137,C_138)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1009,plain,(
    ! [C_138,A_136,B_137] : k5_xboole_0(C_138,k5_xboole_0(A_136,B_137)) = k5_xboole_0(A_136,k5_xboole_0(B_137,C_138)) ),
    inference(superposition,[status(thm),theory(equality)],[c_983,c_2])).

tff(c_864,plain,(
    ! [A_132,B_133] : k2_xboole_0(k5_xboole_0(A_132,B_133),k3_xboole_0(A_132,B_133)) = k2_xboole_0(A_132,B_133) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7347,plain,(
    ! [B_311,A_312] : k2_xboole_0(k5_xboole_0(B_311,A_312),k3_xboole_0(A_312,B_311)) = k2_xboole_0(A_312,B_311) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_864])).

tff(c_876,plain,(
    ! [A_132,B_133] : r1_tarski(k5_xboole_0(A_132,B_133),k2_xboole_0(A_132,B_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_40])).

tff(c_7368,plain,(
    ! [B_311,A_312] : r1_tarski(k5_xboole_0(k5_xboole_0(B_311,A_312),k3_xboole_0(A_312,B_311)),k2_xboole_0(A_312,B_311)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7347,c_876])).

tff(c_7491,plain,(
    ! [B_311,A_312] : r1_tarski(k2_xboole_0(B_311,A_312),k2_xboole_0(A_312,B_311)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_34,c_1009,c_2,c_7368])).

tff(c_7524,plain,(
    ! [B_313,A_314] : r1_tarski(k2_xboole_0(B_313,A_314),k2_xboole_0(A_314,B_313)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_34,c_1009,c_2,c_7368])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7526,plain,(
    ! [B_313,A_314] :
      ( k2_xboole_0(B_313,A_314) = k2_xboole_0(A_314,B_313)
      | ~ r1_tarski(k2_xboole_0(A_314,B_313),k2_xboole_0(B_313,A_314)) ) ),
    inference(resolution,[status(thm)],[c_7524,c_26])).

tff(c_7625,plain,(
    ! [B_313,A_314] : k2_xboole_0(B_313,A_314) = k2_xboole_0(A_314,B_313) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7491,c_7526])).

tff(c_90,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_486,plain,(
    ! [B_111,A_112] :
      ( B_111 = A_112
      | ~ r1_tarski(B_111,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_496,plain,
    ( k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_90,c_486])).

tff(c_573,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_7652,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7625,c_573])).

tff(c_7658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7652])).

tff(c_7659,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_7681,plain,(
    ! [D_315,A_316,B_317] :
      ( ~ r2_hidden(D_315,A_316)
      | r2_hidden(D_315,k2_xboole_0(A_316,B_317)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_7736,plain,(
    ! [D_320] :
      ( ~ r2_hidden(D_320,k1_tarski('#skF_5'))
      | r2_hidden(D_320,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7659,c_7681])).

tff(c_7740,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_229,c_7736])).

tff(c_7744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_7740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.42/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.42/2.34  
% 6.42/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.42/2.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 6.42/2.34  
% 6.42/2.34  %Foreground sorts:
% 6.42/2.34  
% 6.42/2.34  
% 6.42/2.34  %Background operators:
% 6.42/2.34  
% 6.42/2.34  
% 6.42/2.34  %Foreground operators:
% 6.42/2.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.42/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.42/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.42/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.42/2.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.42/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.42/2.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.42/2.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.42/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.42/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.42/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.42/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.42/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.42/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.42/2.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.42/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.42/2.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.42/2.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.42/2.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.42/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.42/2.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.42/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.42/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.42/2.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.42/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.42/2.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.42/2.34  
% 6.42/2.35  tff(f_98, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 6.42/2.35  tff(f_79, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.42/2.35  tff(f_81, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.42/2.35  tff(f_77, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.42/2.35  tff(f_56, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.42/2.35  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.42/2.35  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.42/2.35  tff(f_58, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.42/2.35  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.42/2.35  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 6.42/2.35  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.42/2.35  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.42/2.35  tff(c_88, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.42/2.35  tff(c_72, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.42/2.35  tff(c_208, plain, (![A_88, B_89]: (k1_enumset1(A_88, A_88, B_89)=k2_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.42/2.35  tff(c_52, plain, (![E_36, A_30, C_32]: (r2_hidden(E_36, k1_enumset1(A_30, E_36, C_32)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.42/2.35  tff(c_226, plain, (![A_90, B_91]: (r2_hidden(A_90, k2_tarski(A_90, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_208, c_52])).
% 6.42/2.35  tff(c_229, plain, (![A_37]: (r2_hidden(A_37, k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_226])).
% 6.42/2.35  tff(c_40, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.42/2.35  tff(c_46, plain, (![A_28, B_29]: (k5_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.42/2.35  tff(c_34, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.42/2.35  tff(c_983, plain, (![A_136, B_137, C_138]: (k5_xboole_0(k5_xboole_0(A_136, B_137), C_138)=k5_xboole_0(A_136, k5_xboole_0(B_137, C_138)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.42/2.35  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.42/2.35  tff(c_1009, plain, (![C_138, A_136, B_137]: (k5_xboole_0(C_138, k5_xboole_0(A_136, B_137))=k5_xboole_0(A_136, k5_xboole_0(B_137, C_138)))), inference(superposition, [status(thm), theory('equality')], [c_983, c_2])).
% 6.42/2.35  tff(c_864, plain, (![A_132, B_133]: (k2_xboole_0(k5_xboole_0(A_132, B_133), k3_xboole_0(A_132, B_133))=k2_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.42/2.35  tff(c_7347, plain, (![B_311, A_312]: (k2_xboole_0(k5_xboole_0(B_311, A_312), k3_xboole_0(A_312, B_311))=k2_xboole_0(A_312, B_311))), inference(superposition, [status(thm), theory('equality')], [c_2, c_864])).
% 6.42/2.35  tff(c_876, plain, (![A_132, B_133]: (r1_tarski(k5_xboole_0(A_132, B_133), k2_xboole_0(A_132, B_133)))), inference(superposition, [status(thm), theory('equality')], [c_864, c_40])).
% 6.42/2.35  tff(c_7368, plain, (![B_311, A_312]: (r1_tarski(k5_xboole_0(k5_xboole_0(B_311, A_312), k3_xboole_0(A_312, B_311)), k2_xboole_0(A_312, B_311)))), inference(superposition, [status(thm), theory('equality')], [c_7347, c_876])).
% 6.42/2.35  tff(c_7491, plain, (![B_311, A_312]: (r1_tarski(k2_xboole_0(B_311, A_312), k2_xboole_0(A_312, B_311)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_34, c_1009, c_2, c_7368])).
% 6.42/2.35  tff(c_7524, plain, (![B_313, A_314]: (r1_tarski(k2_xboole_0(B_313, A_314), k2_xboole_0(A_314, B_313)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_34, c_1009, c_2, c_7368])).
% 6.42/2.35  tff(c_26, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.42/2.35  tff(c_7526, plain, (![B_313, A_314]: (k2_xboole_0(B_313, A_314)=k2_xboole_0(A_314, B_313) | ~r1_tarski(k2_xboole_0(A_314, B_313), k2_xboole_0(B_313, A_314)))), inference(resolution, [status(thm)], [c_7524, c_26])).
% 6.42/2.35  tff(c_7625, plain, (![B_313, A_314]: (k2_xboole_0(B_313, A_314)=k2_xboole_0(A_314, B_313))), inference(demodulation, [status(thm), theory('equality')], [c_7491, c_7526])).
% 6.42/2.35  tff(c_90, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.42/2.35  tff(c_486, plain, (![B_111, A_112]: (B_111=A_112 | ~r1_tarski(B_111, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.42/2.35  tff(c_496, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_90, c_486])).
% 6.42/2.35  tff(c_573, plain, (~r1_tarski('#skF_6', k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_496])).
% 6.42/2.35  tff(c_7652, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_7625, c_573])).
% 6.42/2.35  tff(c_7658, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_7652])).
% 6.42/2.35  tff(c_7659, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_496])).
% 6.42/2.35  tff(c_7681, plain, (![D_315, A_316, B_317]: (~r2_hidden(D_315, A_316) | r2_hidden(D_315, k2_xboole_0(A_316, B_317)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.42/2.35  tff(c_7736, plain, (![D_320]: (~r2_hidden(D_320, k1_tarski('#skF_5')) | r2_hidden(D_320, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7659, c_7681])).
% 6.42/2.35  tff(c_7740, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_229, c_7736])).
% 6.42/2.35  tff(c_7744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_7740])).
% 6.42/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.42/2.35  
% 6.42/2.35  Inference rules
% 6.42/2.35  ----------------------
% 6.42/2.35  #Ref     : 0
% 6.42/2.35  #Sup     : 1893
% 6.42/2.35  #Fact    : 6
% 6.42/2.35  #Define  : 0
% 6.42/2.35  #Split   : 1
% 6.42/2.35  #Chain   : 0
% 6.42/2.35  #Close   : 0
% 6.42/2.35  
% 6.42/2.35  Ordering : KBO
% 6.42/2.35  
% 6.42/2.35  Simplification rules
% 6.42/2.35  ----------------------
% 6.42/2.35  #Subsume      : 86
% 6.42/2.35  #Demod        : 2054
% 6.42/2.35  #Tautology    : 1232
% 6.42/2.35  #SimpNegUnit  : 1
% 6.42/2.35  #BackRed      : 12
% 6.42/2.35  
% 6.42/2.35  #Partial instantiations: 0
% 6.42/2.35  #Strategies tried      : 1
% 6.42/2.35  
% 6.42/2.35  Timing (in seconds)
% 6.42/2.35  ----------------------
% 6.42/2.36  Preprocessing        : 0.34
% 6.42/2.36  Parsing              : 0.17
% 6.42/2.36  CNF conversion       : 0.03
% 6.42/2.36  Main loop            : 1.22
% 6.42/2.36  Inferencing          : 0.33
% 6.42/2.36  Reduction            : 0.55
% 6.42/2.36  Demodulation         : 0.46
% 6.42/2.36  BG Simplification    : 0.04
% 6.42/2.36  Subsumption          : 0.22
% 6.42/2.36  Abstraction          : 0.06
% 6.42/2.36  MUC search           : 0.00
% 6.42/2.36  Cooper               : 0.00
% 6.42/2.36  Total                : 1.58
% 6.42/2.36  Index Insertion      : 0.00
% 6.42/2.36  Index Deletion       : 0.00
% 6.42/2.36  Index Matching       : 0.00
% 6.42/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
