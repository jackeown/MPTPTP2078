%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:17 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   62 (  77 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :   55 (  77 expanded)
%              Number of equality atoms :   47 (  68 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_56,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),k1_tarski(B_21)) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_201,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_186])).

tff(c_204,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_201])).

tff(c_245,plain,(
    ! [A_76,B_77] : k4_xboole_0(A_76,k4_xboole_0(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_260,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_245])).

tff(c_263,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_260])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_198,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_186])).

tff(c_264,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_198])).

tff(c_58,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_195,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_186])).

tff(c_286,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_195])).

tff(c_321,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k4_xboole_0(B_83,A_82)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_330,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_321])).

tff(c_342,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10,c_330])).

tff(c_143,plain,(
    ! [A_65,B_66] : k1_enumset1(A_65,A_65,B_66) = k2_tarski(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_152,plain,(
    ! [B_66,A_65] : r2_hidden(B_66,k2_tarski(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_18])).

tff(c_366,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_152])).

tff(c_42,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_489,plain,(
    ! [E_96,C_97,B_98,A_99] :
      ( E_96 = C_97
      | E_96 = B_98
      | E_96 = A_99
      | ~ r2_hidden(E_96,k1_enumset1(A_99,B_98,C_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_508,plain,(
    ! [E_100,B_101,A_102] :
      ( E_100 = B_101
      | E_100 = A_102
      | E_100 = A_102
      | ~ r2_hidden(E_100,k2_tarski(A_102,B_101)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_489])).

tff(c_531,plain,(
    ! [E_103,A_104] :
      ( E_103 = A_104
      | E_103 = A_104
      | E_103 = A_104
      | ~ r2_hidden(E_103,k1_tarski(A_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_508])).

tff(c_534,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_366,c_531])).

tff(c_541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_56,c_534])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:55:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.33  
% 2.32/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.33  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.32/1.33  
% 2.32/1.33  %Foreground sorts:
% 2.32/1.33  
% 2.32/1.33  
% 2.32/1.33  %Background operators:
% 2.32/1.33  
% 2.32/1.33  
% 2.32/1.33  %Foreground operators:
% 2.32/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.32/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.32/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.32/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.32/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.32/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.32/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.32/1.33  
% 2.65/1.35  tff(f_75, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.65/1.35  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.65/1.35  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.65/1.35  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.65/1.35  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.65/1.35  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.65/1.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.65/1.35  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.65/1.35  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.65/1.35  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.65/1.35  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.65/1.35  tff(c_56, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.35  tff(c_40, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(B_21))=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.65/1.35  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.35  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.35  tff(c_186, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.65/1.35  tff(c_201, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_186])).
% 2.65/1.35  tff(c_204, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_201])).
% 2.65/1.35  tff(c_245, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k4_xboole_0(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.35  tff(c_260, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_204, c_245])).
% 2.65/1.35  tff(c_263, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_260])).
% 2.65/1.35  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.35  tff(c_198, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_186])).
% 2.65/1.35  tff(c_264, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_263, c_198])).
% 2.65/1.35  tff(c_58, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.35  tff(c_195, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_186])).
% 2.65/1.35  tff(c_286, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_264, c_195])).
% 2.65/1.35  tff(c_321, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k4_xboole_0(B_83, A_82))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.35  tff(c_330, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_286, c_321])).
% 2.65/1.35  tff(c_342, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10, c_330])).
% 2.65/1.35  tff(c_143, plain, (![A_65, B_66]: (k1_enumset1(A_65, A_65, B_66)=k2_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.65/1.35  tff(c_18, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.65/1.35  tff(c_152, plain, (![B_66, A_65]: (r2_hidden(B_66, k2_tarski(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_18])).
% 2.65/1.35  tff(c_366, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_152])).
% 2.65/1.35  tff(c_42, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.65/1.35  tff(c_44, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.65/1.35  tff(c_489, plain, (![E_96, C_97, B_98, A_99]: (E_96=C_97 | E_96=B_98 | E_96=A_99 | ~r2_hidden(E_96, k1_enumset1(A_99, B_98, C_97)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.65/1.35  tff(c_508, plain, (![E_100, B_101, A_102]: (E_100=B_101 | E_100=A_102 | E_100=A_102 | ~r2_hidden(E_100, k2_tarski(A_102, B_101)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_489])).
% 2.65/1.35  tff(c_531, plain, (![E_103, A_104]: (E_103=A_104 | E_103=A_104 | E_103=A_104 | ~r2_hidden(E_103, k1_tarski(A_104)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_508])).
% 2.65/1.35  tff(c_534, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_366, c_531])).
% 2.65/1.35  tff(c_541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_56, c_534])).
% 2.65/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  
% 2.65/1.35  Inference rules
% 2.65/1.35  ----------------------
% 2.65/1.35  #Ref     : 0
% 2.65/1.35  #Sup     : 116
% 2.65/1.35  #Fact    : 0
% 2.65/1.35  #Define  : 0
% 2.65/1.35  #Split   : 0
% 2.65/1.35  #Chain   : 0
% 2.65/1.35  #Close   : 0
% 2.65/1.35  
% 2.65/1.35  Ordering : KBO
% 2.65/1.35  
% 2.65/1.35  Simplification rules
% 2.65/1.35  ----------------------
% 2.65/1.35  #Subsume      : 0
% 2.65/1.35  #Demod        : 47
% 2.65/1.35  #Tautology    : 93
% 2.65/1.35  #SimpNegUnit  : 1
% 2.65/1.35  #BackRed      : 2
% 2.65/1.35  
% 2.65/1.35  #Partial instantiations: 0
% 2.65/1.35  #Strategies tried      : 1
% 2.65/1.35  
% 2.65/1.35  Timing (in seconds)
% 2.65/1.35  ----------------------
% 2.65/1.35  Preprocessing        : 0.32
% 2.65/1.35  Parsing              : 0.16
% 2.65/1.35  CNF conversion       : 0.02
% 2.65/1.35  Main loop            : 0.24
% 2.65/1.35  Inferencing          : 0.08
% 2.65/1.35  Reduction            : 0.09
% 2.65/1.35  Demodulation         : 0.07
% 2.65/1.35  BG Simplification    : 0.02
% 2.65/1.35  Subsumption          : 0.04
% 2.65/1.35  Abstraction          : 0.01
% 2.65/1.35  MUC search           : 0.00
% 2.65/1.35  Cooper               : 0.00
% 2.65/1.35  Total                : 0.58
% 2.65/1.35  Index Insertion      : 0.00
% 2.65/1.35  Index Deletion       : 0.00
% 2.65/1.35  Index Matching       : 0.00
% 2.65/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
