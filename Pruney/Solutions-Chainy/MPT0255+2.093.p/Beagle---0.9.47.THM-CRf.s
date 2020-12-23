%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:51 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 496 expanded)
%              Number of leaves         :   38 ( 184 expanded)
%              Depth                    :   14
%              Number of atoms          :   54 ( 473 expanded)
%              Number of equality atoms :   53 ( 472 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_52,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_270,plain,(
    ! [A_73,B_74] : k3_xboole_0(A_73,k2_xboole_0(A_73,B_74)) = A_73 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_279,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_xboole_0) = k2_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_270])).

tff(c_282,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_279])).

tff(c_353,plain,(
    ! [A_77,B_78] : k3_tarski(k2_tarski(A_77,B_78)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_362,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_353])).

tff(c_368,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_362])).

tff(c_18,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_372,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_18])).

tff(c_387,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_20])).

tff(c_22,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_402,plain,(
    ! [A_19] : k5_xboole_0(A_19,'#skF_3') = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_22])).

tff(c_121,plain,(
    ! [B_67,A_68] : k5_xboole_0(B_67,A_68) = k5_xboole_0(A_68,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [A_68] : k5_xboole_0(k1_xboole_0,A_68) = A_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_22])).

tff(c_399,plain,(
    ! [A_68] : k5_xboole_0('#skF_3',A_68) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_137])).

tff(c_223,plain,(
    ! [B_71,A_72] : k3_xboole_0(B_71,A_72) = k3_xboole_0(A_72,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_239,plain,(
    ! [A_72] : k3_xboole_0(k1_xboole_0,A_72) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_20])).

tff(c_397,plain,(
    ! [A_72] : k3_xboole_0('#skF_3',A_72) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_387,c_239])).

tff(c_872,plain,(
    ! [A_112,B_113] : k5_xboole_0(k5_xboole_0(A_112,B_113),k3_xboole_0(A_112,B_113)) = k2_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_905,plain,(
    ! [A_72] : k5_xboole_0(k5_xboole_0('#skF_3',A_72),'#skF_3') = k2_xboole_0('#skF_3',A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_872])).

tff(c_942,plain,(
    ! [A_72] : k2_xboole_0('#skF_3',A_72) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_399,c_905])).

tff(c_394,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_368])).

tff(c_977,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_394])).

tff(c_28,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_400,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_28])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_511,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_540,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_511])).

tff(c_547,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_540])).

tff(c_48,plain,(
    ! [B_59] : k4_xboole_0(k1_tarski(B_59),k1_tarski(B_59)) != k1_tarski(B_59) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_650,plain,(
    ! [B_59] : k1_tarski(B_59) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_48])).

tff(c_1025,plain,(
    ! [B_59] : k1_tarski(B_59) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_977,c_650])).

tff(c_396,plain,(
    k2_tarski('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_282])).

tff(c_1027,plain,(
    k2_tarski('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_977,c_977,c_396])).

tff(c_32,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1129,plain,(
    k1_tarski('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_32])).

tff(c_1137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1025,c_1129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.39  
% 2.84/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.39  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.84/1.39  
% 2.84/1.39  %Foreground sorts:
% 2.84/1.39  
% 2.84/1.39  
% 2.84/1.39  %Background operators:
% 2.84/1.39  
% 2.84/1.39  
% 2.84/1.39  %Foreground operators:
% 2.84/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.84/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.84/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.84/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.84/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.84/1.39  
% 2.84/1.41  tff(f_95, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.84/1.41  tff(f_63, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.84/1.41  tff(f_99, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.84/1.41  tff(f_61, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.84/1.41  tff(f_89, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.84/1.41  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.84/1.41  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.84/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.84/1.41  tff(f_73, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 2.84/1.41  tff(f_71, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.84/1.41  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.84/1.41  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.84/1.41  tff(f_94, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.84/1.41  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.84/1.41  tff(c_52, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.84/1.41  tff(c_20, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.84/1.41  tff(c_54, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.84/1.41  tff(c_270, plain, (![A_73, B_74]: (k3_xboole_0(A_73, k2_xboole_0(A_73, B_74))=A_73)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.41  tff(c_279, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_xboole_0)=k2_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_54, c_270])).
% 2.84/1.41  tff(c_282, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_279])).
% 2.84/1.41  tff(c_353, plain, (![A_77, B_78]: (k3_tarski(k2_tarski(A_77, B_78))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.84/1.41  tff(c_362, plain, (k2_xboole_0('#skF_3', '#skF_4')=k3_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_282, c_353])).
% 2.84/1.41  tff(c_368, plain, (k2_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_362])).
% 2.84/1.41  tff(c_18, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k2_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.41  tff(c_372, plain, (k3_xboole_0('#skF_3', k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_368, c_18])).
% 2.84/1.41  tff(c_387, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_372, c_20])).
% 2.84/1.41  tff(c_22, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.84/1.41  tff(c_402, plain, (![A_19]: (k5_xboole_0(A_19, '#skF_3')=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_387, c_22])).
% 2.84/1.41  tff(c_121, plain, (![B_67, A_68]: (k5_xboole_0(B_67, A_68)=k5_xboole_0(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.84/1.41  tff(c_137, plain, (![A_68]: (k5_xboole_0(k1_xboole_0, A_68)=A_68)), inference(superposition, [status(thm), theory('equality')], [c_121, c_22])).
% 2.84/1.41  tff(c_399, plain, (![A_68]: (k5_xboole_0('#skF_3', A_68)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_387, c_137])).
% 2.84/1.41  tff(c_223, plain, (![B_71, A_72]: (k3_xboole_0(B_71, A_72)=k3_xboole_0(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.84/1.41  tff(c_239, plain, (![A_72]: (k3_xboole_0(k1_xboole_0, A_72)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_223, c_20])).
% 2.84/1.41  tff(c_397, plain, (![A_72]: (k3_xboole_0('#skF_3', A_72)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_387, c_387, c_239])).
% 2.84/1.41  tff(c_872, plain, (![A_112, B_113]: (k5_xboole_0(k5_xboole_0(A_112, B_113), k3_xboole_0(A_112, B_113))=k2_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.41  tff(c_905, plain, (![A_72]: (k5_xboole_0(k5_xboole_0('#skF_3', A_72), '#skF_3')=k2_xboole_0('#skF_3', A_72))), inference(superposition, [status(thm), theory('equality')], [c_397, c_872])).
% 2.84/1.41  tff(c_942, plain, (![A_72]: (k2_xboole_0('#skF_3', A_72)=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_402, c_399, c_905])).
% 2.84/1.41  tff(c_394, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_387, c_368])).
% 2.84/1.41  tff(c_977, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_942, c_394])).
% 2.84/1.41  tff(c_28, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.84/1.41  tff(c_400, plain, (![A_25]: (k5_xboole_0(A_25, A_25)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_387, c_28])).
% 2.84/1.41  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.41  tff(c_511, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.84/1.41  tff(c_540, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_511])).
% 2.84/1.41  tff(c_547, plain, (![A_5]: (k4_xboole_0(A_5, A_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_540])).
% 2.84/1.41  tff(c_48, plain, (![B_59]: (k4_xboole_0(k1_tarski(B_59), k1_tarski(B_59))!=k1_tarski(B_59))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.84/1.41  tff(c_650, plain, (![B_59]: (k1_tarski(B_59)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_547, c_48])).
% 2.84/1.41  tff(c_1025, plain, (![B_59]: (k1_tarski(B_59)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_977, c_650])).
% 2.84/1.41  tff(c_396, plain, (k2_tarski('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_387, c_282])).
% 2.84/1.41  tff(c_1027, plain, (k2_tarski('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_977, c_977, c_396])).
% 2.84/1.41  tff(c_32, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.84/1.41  tff(c_1129, plain, (k1_tarski('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1027, c_32])).
% 2.84/1.41  tff(c_1137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1025, c_1129])).
% 2.84/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.41  
% 2.84/1.41  Inference rules
% 2.84/1.41  ----------------------
% 2.84/1.41  #Ref     : 0
% 2.84/1.41  #Sup     : 267
% 2.84/1.41  #Fact    : 0
% 2.84/1.41  #Define  : 0
% 2.84/1.41  #Split   : 0
% 2.84/1.41  #Chain   : 0
% 2.84/1.41  #Close   : 0
% 2.84/1.41  
% 2.84/1.41  Ordering : KBO
% 2.84/1.41  
% 2.84/1.41  Simplification rules
% 2.84/1.41  ----------------------
% 2.84/1.41  #Subsume      : 0
% 2.84/1.41  #Demod        : 131
% 2.84/1.41  #Tautology    : 211
% 2.84/1.41  #SimpNegUnit  : 3
% 2.84/1.41  #BackRed      : 36
% 2.84/1.41  
% 2.84/1.41  #Partial instantiations: 0
% 2.84/1.41  #Strategies tried      : 1
% 2.84/1.41  
% 2.84/1.41  Timing (in seconds)
% 2.84/1.41  ----------------------
% 2.84/1.41  Preprocessing        : 0.32
% 2.84/1.41  Parsing              : 0.17
% 2.84/1.41  CNF conversion       : 0.02
% 2.84/1.41  Main loop            : 0.32
% 2.84/1.41  Inferencing          : 0.11
% 2.84/1.41  Reduction            : 0.12
% 2.84/1.41  Demodulation         : 0.09
% 2.84/1.41  BG Simplification    : 0.02
% 2.84/1.41  Subsumption          : 0.04
% 2.84/1.41  Abstraction          : 0.02
% 2.84/1.41  MUC search           : 0.00
% 2.84/1.41  Cooper               : 0.00
% 2.84/1.41  Total                : 0.67
% 2.84/1.41  Index Insertion      : 0.00
% 2.84/1.41  Index Deletion       : 0.00
% 2.84/1.41  Index Matching       : 0.00
% 2.84/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
