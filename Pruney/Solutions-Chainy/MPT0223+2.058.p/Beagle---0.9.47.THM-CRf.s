%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:24 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   66 (  99 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :   63 ( 105 expanded)
%              Number of equality atoms :   50 (  86 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),k1_tarski(B_25)) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_252,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_273,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_252])).

tff(c_126,plain,(
    ! [A_59,B_60] : r1_xboole_0(k3_xboole_0(A_59,B_60),k5_xboole_0(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,(
    ! [A_61] : r1_xboole_0(A_61,k5_xboole_0(A_61,A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_126])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_148,plain,(
    ! [A_61] : k3_xboole_0(A_61,k5_xboole_0(A_61,A_61)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_279,plain,(
    ! [A_61] : k3_xboole_0(A_61,k4_xboole_0(A_61,A_61)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_148])).

tff(c_267,plain,(
    ! [A_61] : k4_xboole_0(A_61,k5_xboole_0(A_61,A_61)) = k5_xboole_0(A_61,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_252])).

tff(c_277,plain,(
    ! [A_61] : k4_xboole_0(A_61,k5_xboole_0(A_61,A_61)) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_267])).

tff(c_350,plain,(
    ! [A_61] : k4_xboole_0(A_61,k4_xboole_0(A_61,A_61)) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_277])).

tff(c_484,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k4_xboole_0(A_83,B_84)) = k3_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_512,plain,(
    ! [A_61] : k3_xboole_0(A_61,k4_xboole_0(A_61,A_61)) = k4_xboole_0(A_61,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_484])).

tff(c_524,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_512])).

tff(c_56,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_270,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_252])).

tff(c_310,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_273])).

tff(c_579,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_310])).

tff(c_16,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_587,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_16])).

tff(c_591,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_14,c_587])).

tff(c_97,plain,(
    ! [A_52,B_53] : k1_enumset1(A_52,A_52,B_53) = k2_tarski(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_106,plain,(
    ! [B_53,A_52] : r2_hidden(B_53,k2_tarski(A_52,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_20])).

tff(c_858,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_106])).

tff(c_46,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ! [A_27,B_28] : k1_enumset1(A_27,A_27,B_28) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1051,plain,(
    ! [E_110,C_111,B_112,A_113] :
      ( E_110 = C_111
      | E_110 = B_112
      | E_110 = A_113
      | ~ r2_hidden(E_110,k1_enumset1(A_113,B_112,C_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1495,plain,(
    ! [E_130,B_131,A_132] :
      ( E_130 = B_131
      | E_130 = A_132
      | E_130 = A_132
      | ~ r2_hidden(E_130,k2_tarski(A_132,B_131)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1051])).

tff(c_1512,plain,(
    ! [E_133,A_134] :
      ( E_133 = A_134
      | E_133 = A_134
      | E_133 = A_134
      | ~ r2_hidden(E_133,k1_tarski(A_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1495])).

tff(c_1515,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_858,c_1512])).

tff(c_1522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_54,c_1515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:51:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.47  
% 2.93/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.47  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.93/1.47  
% 2.93/1.47  %Foreground sorts:
% 2.93/1.47  
% 2.93/1.47  
% 2.93/1.47  %Background operators:
% 2.93/1.47  
% 2.93/1.47  
% 2.93/1.47  %Foreground operators:
% 2.93/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.93/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.93/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.93/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.93/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.93/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.93/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.93/1.47  
% 3.06/1.48  tff(f_73, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.06/1.48  tff(f_60, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.06/1.48  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.06/1.48  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.06/1.48  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.06/1.48  tff(f_33, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.06/1.48  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.06/1.48  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.06/1.48  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.06/1.48  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.06/1.48  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.06/1.48  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.06/1.48  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.06/1.48  tff(c_44, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), k1_tarski(B_25))=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.06/1.48  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.06/1.48  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.48  tff(c_252, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.48  tff(c_273, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_252])).
% 3.06/1.48  tff(c_126, plain, (![A_59, B_60]: (r1_xboole_0(k3_xboole_0(A_59, B_60), k5_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.48  tff(c_140, plain, (![A_61]: (r1_xboole_0(A_61, k5_xboole_0(A_61, A_61)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_126])).
% 3.06/1.48  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.48  tff(c_148, plain, (![A_61]: (k3_xboole_0(A_61, k5_xboole_0(A_61, A_61))=k1_xboole_0)), inference(resolution, [status(thm)], [c_140, c_2])).
% 3.06/1.48  tff(c_279, plain, (![A_61]: (k3_xboole_0(A_61, k4_xboole_0(A_61, A_61))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_273, c_148])).
% 3.06/1.48  tff(c_267, plain, (![A_61]: (k4_xboole_0(A_61, k5_xboole_0(A_61, A_61))=k5_xboole_0(A_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_148, c_252])).
% 3.06/1.48  tff(c_277, plain, (![A_61]: (k4_xboole_0(A_61, k5_xboole_0(A_61, A_61))=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_267])).
% 3.06/1.48  tff(c_350, plain, (![A_61]: (k4_xboole_0(A_61, k4_xboole_0(A_61, A_61))=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_273, c_277])).
% 3.06/1.48  tff(c_484, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k4_xboole_0(A_83, B_84))=k3_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.06/1.48  tff(c_512, plain, (![A_61]: (k3_xboole_0(A_61, k4_xboole_0(A_61, A_61))=k4_xboole_0(A_61, A_61))), inference(superposition, [status(thm), theory('equality')], [c_350, c_484])).
% 3.06/1.48  tff(c_524, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_279, c_512])).
% 3.06/1.48  tff(c_56, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.06/1.48  tff(c_270, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_252])).
% 3.06/1.48  tff(c_310, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_273])).
% 3.06/1.48  tff(c_579, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_524, c_310])).
% 3.06/1.48  tff(c_16, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.06/1.48  tff(c_587, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_579, c_16])).
% 3.06/1.48  tff(c_591, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_14, c_587])).
% 3.06/1.48  tff(c_97, plain, (![A_52, B_53]: (k1_enumset1(A_52, A_52, B_53)=k2_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.06/1.48  tff(c_20, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.06/1.48  tff(c_106, plain, (![B_53, A_52]: (r2_hidden(B_53, k2_tarski(A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_20])).
% 3.06/1.48  tff(c_858, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_591, c_106])).
% 3.06/1.48  tff(c_46, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.48  tff(c_48, plain, (![A_27, B_28]: (k1_enumset1(A_27, A_27, B_28)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.06/1.48  tff(c_1051, plain, (![E_110, C_111, B_112, A_113]: (E_110=C_111 | E_110=B_112 | E_110=A_113 | ~r2_hidden(E_110, k1_enumset1(A_113, B_112, C_111)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.06/1.48  tff(c_1495, plain, (![E_130, B_131, A_132]: (E_130=B_131 | E_130=A_132 | E_130=A_132 | ~r2_hidden(E_130, k2_tarski(A_132, B_131)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1051])).
% 3.06/1.48  tff(c_1512, plain, (![E_133, A_134]: (E_133=A_134 | E_133=A_134 | E_133=A_134 | ~r2_hidden(E_133, k1_tarski(A_134)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1495])).
% 3.06/1.48  tff(c_1515, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_858, c_1512])).
% 3.06/1.48  tff(c_1522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_54, c_1515])).
% 3.06/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.48  
% 3.06/1.48  Inference rules
% 3.06/1.48  ----------------------
% 3.06/1.48  #Ref     : 0
% 3.06/1.48  #Sup     : 354
% 3.06/1.48  #Fact    : 0
% 3.06/1.48  #Define  : 0
% 3.06/1.48  #Split   : 0
% 3.06/1.48  #Chain   : 0
% 3.06/1.48  #Close   : 0
% 3.06/1.48  
% 3.06/1.48  Ordering : KBO
% 3.06/1.48  
% 3.06/1.48  Simplification rules
% 3.06/1.48  ----------------------
% 3.06/1.48  #Subsume      : 0
% 3.06/1.48  #Demod        : 348
% 3.06/1.48  #Tautology    : 292
% 3.06/1.48  #SimpNegUnit  : 1
% 3.06/1.48  #BackRed      : 11
% 3.06/1.48  
% 3.06/1.48  #Partial instantiations: 0
% 3.06/1.48  #Strategies tried      : 1
% 3.06/1.48  
% 3.06/1.48  Timing (in seconds)
% 3.06/1.48  ----------------------
% 3.06/1.49  Preprocessing        : 0.31
% 3.06/1.49  Parsing              : 0.16
% 3.06/1.49  CNF conversion       : 0.02
% 3.06/1.49  Main loop            : 0.39
% 3.06/1.49  Inferencing          : 0.13
% 3.06/1.49  Reduction            : 0.15
% 3.06/1.49  Demodulation         : 0.12
% 3.06/1.49  BG Simplification    : 0.02
% 3.06/1.49  Subsumption          : 0.06
% 3.06/1.49  Abstraction          : 0.02
% 3.06/1.49  MUC search           : 0.00
% 3.06/1.49  Cooper               : 0.00
% 3.06/1.49  Total                : 0.72
% 3.06/1.49  Index Insertion      : 0.00
% 3.06/1.49  Index Deletion       : 0.00
% 3.06/1.49  Index Matching       : 0.00
% 3.06/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
