%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:29 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 142 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 ( 131 expanded)
%              Number of equality atoms :   41 ( 110 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_68,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_623,plain,(
    ! [A_152,B_153] : k5_xboole_0(k5_xboole_0(A_152,B_153),k2_xboole_0(A_152,B_153)) = k3_xboole_0(A_152,B_153) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_675,plain,(
    ! [A_10] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_10,A_10)) = k3_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_623])).

tff(c_683,plain,(
    ! [A_154] : k5_xboole_0(k1_xboole_0,A_154) = A_154 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_675])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_706,plain,(
    ! [A_154] : k5_xboole_0(A_154,k1_xboole_0) = A_154 ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_2])).

tff(c_490,plain,(
    ! [A_141,B_142,C_143] : k5_xboole_0(k5_xboole_0(A_141,B_142),C_143) = k5_xboole_0(A_141,k5_xboole_0(B_142,C_143)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_506,plain,(
    ! [A_141,B_142] : k5_xboole_0(A_141,k5_xboole_0(B_142,k5_xboole_0(A_141,B_142))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_10])).

tff(c_681,plain,(
    ! [A_10] : k5_xboole_0(k1_xboole_0,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_675])).

tff(c_529,plain,(
    ! [A_10,C_143] : k5_xboole_0(A_10,k5_xboole_0(A_10,C_143)) = k5_xboole_0(k1_xboole_0,C_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_490])).

tff(c_838,plain,(
    ! [A_163,C_164] : k5_xboole_0(A_163,k5_xboole_0(A_163,C_164)) = C_164 ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_529])).

tff(c_891,plain,(
    ! [B_142,A_141] : k5_xboole_0(B_142,k5_xboole_0(A_141,B_142)) = k5_xboole_0(A_141,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_838])).

tff(c_925,plain,(
    ! [B_142,A_141] : k5_xboole_0(B_142,k5_xboole_0(A_141,B_142)) = A_141 ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_891])).

tff(c_70,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k5_xboole_0(k5_xboole_0(A_7,B_8),C_9) = k5_xboole_0(A_7,k5_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4648,plain,(
    ! [A_330,B_331] : k5_xboole_0(A_330,k5_xboole_0(B_331,k2_xboole_0(A_330,B_331))) = k3_xboole_0(A_330,B_331) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_623])).

tff(c_837,plain,(
    ! [A_10,C_143] : k5_xboole_0(A_10,k5_xboole_0(A_10,C_143)) = C_143 ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_529])).

tff(c_8725,plain,(
    ! [B_368,A_369] : k5_xboole_0(B_368,k2_xboole_0(A_369,B_368)) = k5_xboole_0(A_369,k3_xboole_0(A_369,B_368)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4648,c_837])).

tff(c_8993,plain,(
    k5_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_3','#skF_4')) = k5_xboole_0('#skF_5',k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_8725])).

tff(c_9021,plain,(
    k5_xboole_0('#skF_5',k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8993])).

tff(c_902,plain,(
    ! [A_7,B_8,C_164] : k5_xboole_0(A_7,k5_xboole_0(B_8,k5_xboole_0(k5_xboole_0(A_7,B_8),C_164))) = C_164 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_838])).

tff(c_927,plain,(
    ! [A_7,B_8,C_164] : k5_xboole_0(A_7,k5_xboole_0(B_8,k5_xboole_0(A_7,k5_xboole_0(B_8,C_164)))) = C_164 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_902])).

tff(c_9035,plain,(
    ! [A_7] : k5_xboole_0(A_7,k5_xboole_0('#skF_5',k5_xboole_0(A_7,k1_xboole_0))) = k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9021,c_927])).

tff(c_9107,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_706,c_9035])).

tff(c_60,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_174,plain,(
    ! [A_94,B_95] : k1_enumset1(A_94,A_94,B_95) = k2_tarski(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [E_19,B_14,C_15] : r2_hidden(E_19,k1_enumset1(E_19,B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_180,plain,(
    ! [A_94,B_95] : r2_hidden(A_94,k2_tarski(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_20])).

tff(c_58,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,k3_tarski(B_68))
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_196,plain,(
    ! [A_98,C_99,B_100] :
      ( r2_hidden(A_98,C_99)
      | ~ r1_tarski(k2_tarski(A_98,B_100),C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_418,plain,(
    ! [A_138,B_139,B_140] :
      ( r2_hidden(A_138,k3_tarski(B_139))
      | ~ r2_hidden(k2_tarski(A_138,B_140),B_139) ) ),
    inference(resolution,[status(thm)],[c_58,c_196])).

tff(c_458,plain,(
    ! [A_138,B_140,B_95] : r2_hidden(A_138,k3_tarski(k2_tarski(k2_tarski(A_138,B_140),B_95))) ),
    inference(resolution,[status(thm)],[c_180,c_418])).

tff(c_486,plain,(
    ! [A_138,B_140,B_95] : r2_hidden(A_138,k2_xboole_0(k2_tarski(A_138,B_140),B_95)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_458])).

tff(c_9265,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9107,c_486])).

tff(c_9277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_9265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.61/2.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/2.92  
% 7.61/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/2.92  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.61/2.92  
% 7.61/2.92  %Foreground sorts:
% 7.61/2.92  
% 7.61/2.92  
% 7.61/2.92  %Background operators:
% 7.61/2.92  
% 7.61/2.92  
% 7.61/2.92  %Foreground operators:
% 7.61/2.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.61/2.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.61/2.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.61/2.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.61/2.92  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.61/2.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.61/2.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.61/2.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.61/2.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.61/2.92  tff('#skF_5', type, '#skF_5': $i).
% 7.61/2.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.61/2.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.61/2.92  tff('#skF_3', type, '#skF_3': $i).
% 7.61/2.92  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.61/2.93  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.61/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.61/2.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.61/2.93  tff('#skF_4', type, '#skF_4': $i).
% 7.61/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.61/2.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.61/2.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.61/2.93  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.61/2.93  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.61/2.93  
% 7.61/2.94  tff(f_89, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 7.61/2.94  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.61/2.94  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.61/2.94  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.61/2.94  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.61/2.94  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.61/2.94  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.61/2.94  tff(f_78, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.61/2.94  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.61/2.94  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 7.61/2.94  tff(f_76, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 7.61/2.94  tff(f_84, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 7.61/2.94  tff(c_68, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.61/2.94  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.61/2.94  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.61/2.94  tff(c_10, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.61/2.94  tff(c_623, plain, (![A_152, B_153]: (k5_xboole_0(k5_xboole_0(A_152, B_153), k2_xboole_0(A_152, B_153))=k3_xboole_0(A_152, B_153))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.61/2.94  tff(c_675, plain, (![A_10]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_10, A_10))=k3_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_623])).
% 7.61/2.94  tff(c_683, plain, (![A_154]: (k5_xboole_0(k1_xboole_0, A_154)=A_154)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_675])).
% 7.61/2.94  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.61/2.94  tff(c_706, plain, (![A_154]: (k5_xboole_0(A_154, k1_xboole_0)=A_154)), inference(superposition, [status(thm), theory('equality')], [c_683, c_2])).
% 7.61/2.94  tff(c_490, plain, (![A_141, B_142, C_143]: (k5_xboole_0(k5_xboole_0(A_141, B_142), C_143)=k5_xboole_0(A_141, k5_xboole_0(B_142, C_143)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.61/2.94  tff(c_506, plain, (![A_141, B_142]: (k5_xboole_0(A_141, k5_xboole_0(B_142, k5_xboole_0(A_141, B_142)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_490, c_10])).
% 7.61/2.94  tff(c_681, plain, (![A_10]: (k5_xboole_0(k1_xboole_0, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_675])).
% 7.61/2.94  tff(c_529, plain, (![A_10, C_143]: (k5_xboole_0(A_10, k5_xboole_0(A_10, C_143))=k5_xboole_0(k1_xboole_0, C_143))), inference(superposition, [status(thm), theory('equality')], [c_10, c_490])).
% 7.61/2.94  tff(c_838, plain, (![A_163, C_164]: (k5_xboole_0(A_163, k5_xboole_0(A_163, C_164))=C_164)), inference(demodulation, [status(thm), theory('equality')], [c_681, c_529])).
% 7.61/2.94  tff(c_891, plain, (![B_142, A_141]: (k5_xboole_0(B_142, k5_xboole_0(A_141, B_142))=k5_xboole_0(A_141, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_506, c_838])).
% 7.61/2.94  tff(c_925, plain, (![B_142, A_141]: (k5_xboole_0(B_142, k5_xboole_0(A_141, B_142))=A_141)), inference(demodulation, [status(thm), theory('equality')], [c_706, c_891])).
% 7.61/2.94  tff(c_70, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.61/2.94  tff(c_8, plain, (![A_7, B_8, C_9]: (k5_xboole_0(k5_xboole_0(A_7, B_8), C_9)=k5_xboole_0(A_7, k5_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.61/2.94  tff(c_4648, plain, (![A_330, B_331]: (k5_xboole_0(A_330, k5_xboole_0(B_331, k2_xboole_0(A_330, B_331)))=k3_xboole_0(A_330, B_331))), inference(superposition, [status(thm), theory('equality')], [c_8, c_623])).
% 7.61/2.94  tff(c_837, plain, (![A_10, C_143]: (k5_xboole_0(A_10, k5_xboole_0(A_10, C_143))=C_143)), inference(demodulation, [status(thm), theory('equality')], [c_681, c_529])).
% 7.61/2.94  tff(c_8725, plain, (![B_368, A_369]: (k5_xboole_0(B_368, k2_xboole_0(A_369, B_368))=k5_xboole_0(A_369, k3_xboole_0(A_369, B_368)))), inference(superposition, [status(thm), theory('equality')], [c_4648, c_837])).
% 7.61/2.94  tff(c_8993, plain, (k5_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_3', '#skF_4'))=k5_xboole_0('#skF_5', k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_8725])).
% 7.61/2.94  tff(c_9021, plain, (k5_xboole_0('#skF_5', k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8993])).
% 7.61/2.94  tff(c_902, plain, (![A_7, B_8, C_164]: (k5_xboole_0(A_7, k5_xboole_0(B_8, k5_xboole_0(k5_xboole_0(A_7, B_8), C_164)))=C_164)), inference(superposition, [status(thm), theory('equality')], [c_8, c_838])).
% 7.61/2.94  tff(c_927, plain, (![A_7, B_8, C_164]: (k5_xboole_0(A_7, k5_xboole_0(B_8, k5_xboole_0(A_7, k5_xboole_0(B_8, C_164))))=C_164)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_902])).
% 7.61/2.94  tff(c_9035, plain, (![A_7]: (k5_xboole_0(A_7, k5_xboole_0('#skF_5', k5_xboole_0(A_7, k1_xboole_0)))=k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9021, c_927])).
% 7.61/2.94  tff(c_9107, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_925, c_706, c_9035])).
% 7.61/2.94  tff(c_60, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.61/2.94  tff(c_174, plain, (![A_94, B_95]: (k1_enumset1(A_94, A_94, B_95)=k2_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.61/2.94  tff(c_20, plain, (![E_19, B_14, C_15]: (r2_hidden(E_19, k1_enumset1(E_19, B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.61/2.94  tff(c_180, plain, (![A_94, B_95]: (r2_hidden(A_94, k2_tarski(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_174, c_20])).
% 7.61/2.94  tff(c_58, plain, (![A_67, B_68]: (r1_tarski(A_67, k3_tarski(B_68)) | ~r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.61/2.94  tff(c_196, plain, (![A_98, C_99, B_100]: (r2_hidden(A_98, C_99) | ~r1_tarski(k2_tarski(A_98, B_100), C_99))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.61/2.94  tff(c_418, plain, (![A_138, B_139, B_140]: (r2_hidden(A_138, k3_tarski(B_139)) | ~r2_hidden(k2_tarski(A_138, B_140), B_139))), inference(resolution, [status(thm)], [c_58, c_196])).
% 7.61/2.94  tff(c_458, plain, (![A_138, B_140, B_95]: (r2_hidden(A_138, k3_tarski(k2_tarski(k2_tarski(A_138, B_140), B_95))))), inference(resolution, [status(thm)], [c_180, c_418])).
% 7.61/2.94  tff(c_486, plain, (![A_138, B_140, B_95]: (r2_hidden(A_138, k2_xboole_0(k2_tarski(A_138, B_140), B_95)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_458])).
% 7.61/2.94  tff(c_9265, plain, (r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9107, c_486])).
% 7.61/2.94  tff(c_9277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_9265])).
% 7.61/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/2.94  
% 7.61/2.94  Inference rules
% 7.61/2.94  ----------------------
% 7.61/2.94  #Ref     : 0
% 7.61/2.94  #Sup     : 2340
% 7.61/2.94  #Fact    : 0
% 7.61/2.94  #Define  : 0
% 7.61/2.94  #Split   : 0
% 7.61/2.94  #Chain   : 0
% 7.61/2.94  #Close   : 0
% 7.61/2.94  
% 7.61/2.94  Ordering : KBO
% 7.61/2.94  
% 7.61/2.94  Simplification rules
% 7.61/2.94  ----------------------
% 7.61/2.94  #Subsume      : 112
% 7.61/2.94  #Demod        : 1907
% 7.61/2.94  #Tautology    : 899
% 7.61/2.94  #SimpNegUnit  : 1
% 7.61/2.94  #BackRed      : 3
% 7.61/2.94  
% 7.61/2.94  #Partial instantiations: 0
% 7.61/2.94  #Strategies tried      : 1
% 7.61/2.94  
% 7.61/2.94  Timing (in seconds)
% 7.61/2.94  ----------------------
% 7.61/2.94  Preprocessing        : 0.36
% 7.61/2.94  Parsing              : 0.19
% 7.61/2.94  CNF conversion       : 0.03
% 7.61/2.94  Main loop            : 1.78
% 7.61/2.94  Inferencing          : 0.43
% 7.61/2.94  Reduction            : 0.99
% 7.61/2.94  Demodulation         : 0.89
% 7.61/2.94  BG Simplification    : 0.07
% 7.61/2.94  Subsumption          : 0.23
% 7.61/2.94  Abstraction          : 0.08
% 7.61/2.94  MUC search           : 0.00
% 7.61/2.94  Cooper               : 0.00
% 7.61/2.94  Total                : 2.18
% 7.61/2.94  Index Insertion      : 0.00
% 7.61/2.94  Index Deletion       : 0.00
% 7.61/2.94  Index Matching       : 0.00
% 7.61/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
