%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:51 EST 2020

% Result     : Theorem 28.97s
% Output     : CNFRefutation 28.97s
% Verified   : 
% Statistics : Number of formulae       :   65 (  83 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :   75 ( 102 expanded)
%              Number of equality atoms :   29 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_30,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_589,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_1'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_599,plain,(
    ! [A_63] : r1_tarski(A_63,A_63) ),
    inference(resolution,[status(thm)],[c_589,c_6])).

tff(c_34,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1025,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_tarski(A_84,C_85)
      | ~ r1_tarski(B_86,C_85)
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1037,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,k2_xboole_0('#skF_4','#skF_5'))
      | ~ r1_tarski(A_84,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_1025])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_620,plain,(
    ! [A_68,B_69,B_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | r1_tarski(k3_xboole_0(A_68,B_69),B_70) ) ),
    inference(resolution,[status(thm)],[c_589,c_12])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20350,plain,(
    ! [A_312,B_313,B_314] :
      ( k2_xboole_0(k3_xboole_0(A_312,B_313),B_314) = B_314
      | ~ r1_xboole_0(A_312,B_313) ) ),
    inference(resolution,[status(thm)],[c_620,c_14])).

tff(c_16,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20820,plain,(
    ! [A_315,B_316] :
      ( k3_xboole_0(A_315,B_316) = k1_xboole_0
      | ~ r1_xboole_0(A_315,B_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20350,c_16])).

tff(c_20879,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_20820])).

tff(c_91,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k2_xboole_0(A_34,B_35)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_98,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_91])).

tff(c_2198,plain,(
    ! [A_118,B_119,C_120] : k4_xboole_0(k4_xboole_0(A_118,B_119),C_120) = k4_xboole_0(A_118,k2_xboole_0(B_119,C_120)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8275,plain,(
    ! [C_199,A_200,B_201] : k2_xboole_0(C_199,k4_xboole_0(A_200,k2_xboole_0(B_201,C_199))) = k2_xboole_0(C_199,k4_xboole_0(A_200,B_201)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2198,c_20])).

tff(c_8559,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_8275])).

tff(c_8655,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8559])).

tff(c_358,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_367,plain,(
    ! [A_49,B_50] : k2_xboole_0(k4_xboole_0(A_49,B_50),k3_xboole_0(A_49,B_50)) = k2_xboole_0(k4_xboole_0(A_49,B_50),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_20])).

tff(c_401,plain,(
    ! [A_49,B_50] : k2_xboole_0(k4_xboole_0(A_49,B_50),k3_xboole_0(A_49,B_50)) = k2_xboole_0(A_49,k4_xboole_0(A_49,B_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_367])).

tff(c_9486,plain,(
    ! [A_208,B_209] : k2_xboole_0(k4_xboole_0(A_208,B_209),k3_xboole_0(A_208,B_209)) = A_208 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8655,c_401])).

tff(c_9734,plain,(
    ! [A_208,B_209] : k2_xboole_0(k3_xboole_0(A_208,B_209),k4_xboole_0(A_208,B_209)) = A_208 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9486])).

tff(c_20912,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_20879,c_9734])).

tff(c_44,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [A_33] : k2_xboole_0(k1_xboole_0,A_33) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_21104,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_20912,c_60])).

tff(c_24,plain,(
    ! [A_24,B_25,C_26] :
      ( r1_tarski(k4_xboole_0(A_24,B_25),C_26)
      | ~ r1_tarski(A_24,k2_xboole_0(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_88328,plain,(
    ! [C_707] :
      ( r1_tarski('#skF_3',C_707)
      | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_707)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21104,c_24])).

tff(c_129978,plain,(
    ! [A_833] :
      ( r1_tarski('#skF_3',A_833)
      | ~ r1_tarski('#skF_3',k2_xboole_0(A_833,'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_88328])).

tff(c_130053,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1037,c_129978])).

tff(c_130085,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_130053])).

tff(c_130087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_130085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:34:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.97/20.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.97/20.87  
% 28.97/20.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.97/20.87  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 28.97/20.87  
% 28.97/20.87  %Foreground sorts:
% 28.97/20.87  
% 28.97/20.87  
% 28.97/20.87  %Background operators:
% 28.97/20.87  
% 28.97/20.87  
% 28.97/20.87  %Foreground operators:
% 28.97/20.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.97/20.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 28.97/20.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 28.97/20.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 28.97/20.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 28.97/20.87  tff('#skF_5', type, '#skF_5': $i).
% 28.97/20.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 28.97/20.87  tff('#skF_3', type, '#skF_3': $i).
% 28.97/20.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.97/20.87  tff('#skF_4', type, '#skF_4': $i).
% 28.97/20.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.97/20.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 28.97/20.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 28.97/20.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 28.97/20.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 28.97/20.87  
% 28.97/20.88  tff(f_79, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 28.97/20.88  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 28.97/20.88  tff(f_60, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 28.97/20.88  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 28.97/20.88  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 28.97/20.88  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 28.97/20.88  tff(f_54, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 28.97/20.88  tff(f_70, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 28.97/20.88  tff(f_64, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 28.97/20.88  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 28.97/20.88  tff(f_72, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 28.97/20.88  tff(f_68, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 28.97/20.88  tff(c_30, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 28.97/20.88  tff(c_589, plain, (![A_63, B_64]: (r2_hidden('#skF_1'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_34])).
% 28.97/20.88  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 28.97/20.88  tff(c_599, plain, (![A_63]: (r1_tarski(A_63, A_63))), inference(resolution, [status(thm)], [c_589, c_6])).
% 28.97/20.88  tff(c_34, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 28.97/20.88  tff(c_1025, plain, (![A_84, C_85, B_86]: (r1_tarski(A_84, C_85) | ~r1_tarski(B_86, C_85) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_60])).
% 28.97/20.88  tff(c_1037, plain, (![A_84]: (r1_tarski(A_84, k2_xboole_0('#skF_4', '#skF_5')) | ~r1_tarski(A_84, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_1025])).
% 28.97/20.88  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 28.97/20.88  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 28.97/20.88  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 28.97/20.88  tff(c_620, plain, (![A_68, B_69, B_70]: (~r1_xboole_0(A_68, B_69) | r1_tarski(k3_xboole_0(A_68, B_69), B_70))), inference(resolution, [status(thm)], [c_589, c_12])).
% 28.97/20.88  tff(c_14, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 28.97/20.88  tff(c_20350, plain, (![A_312, B_313, B_314]: (k2_xboole_0(k3_xboole_0(A_312, B_313), B_314)=B_314 | ~r1_xboole_0(A_312, B_313))), inference(resolution, [status(thm)], [c_620, c_14])).
% 28.97/20.88  tff(c_16, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_54])).
% 28.97/20.88  tff(c_20820, plain, (![A_315, B_316]: (k3_xboole_0(A_315, B_316)=k1_xboole_0 | ~r1_xboole_0(A_315, B_316))), inference(superposition, [status(thm), theory('equality')], [c_20350, c_16])).
% 28.97/20.88  tff(c_20879, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_20820])).
% 28.97/20.88  tff(c_91, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k2_xboole_0(A_34, B_35))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 28.97/20.88  tff(c_98, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_91])).
% 28.97/20.88  tff(c_2198, plain, (![A_118, B_119, C_120]: (k4_xboole_0(k4_xboole_0(A_118, B_119), C_120)=k4_xboole_0(A_118, k2_xboole_0(B_119, C_120)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 28.97/20.88  tff(c_20, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 28.97/20.88  tff(c_8275, plain, (![C_199, A_200, B_201]: (k2_xboole_0(C_199, k4_xboole_0(A_200, k2_xboole_0(B_201, C_199)))=k2_xboole_0(C_199, k4_xboole_0(A_200, B_201)))), inference(superposition, [status(thm), theory('equality')], [c_2198, c_20])).
% 28.97/20.88  tff(c_8559, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k2_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_98, c_8275])).
% 28.97/20.88  tff(c_8655, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_2))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8559])).
% 28.97/20.88  tff(c_358, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_72])).
% 28.97/20.88  tff(c_367, plain, (![A_49, B_50]: (k2_xboole_0(k4_xboole_0(A_49, B_50), k3_xboole_0(A_49, B_50))=k2_xboole_0(k4_xboole_0(A_49, B_50), A_49))), inference(superposition, [status(thm), theory('equality')], [c_358, c_20])).
% 28.97/20.88  tff(c_401, plain, (![A_49, B_50]: (k2_xboole_0(k4_xboole_0(A_49, B_50), k3_xboole_0(A_49, B_50))=k2_xboole_0(A_49, k4_xboole_0(A_49, B_50)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_367])).
% 28.97/20.88  tff(c_9486, plain, (![A_208, B_209]: (k2_xboole_0(k4_xboole_0(A_208, B_209), k3_xboole_0(A_208, B_209))=A_208)), inference(demodulation, [status(thm), theory('equality')], [c_8655, c_401])).
% 28.97/20.88  tff(c_9734, plain, (![A_208, B_209]: (k2_xboole_0(k3_xboole_0(A_208, B_209), k4_xboole_0(A_208, B_209))=A_208)), inference(superposition, [status(thm), theory('equality')], [c_2, c_9486])).
% 28.97/20.88  tff(c_20912, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_20879, c_9734])).
% 28.97/20.88  tff(c_44, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 28.97/20.88  tff(c_60, plain, (![A_33]: (k2_xboole_0(k1_xboole_0, A_33)=A_33)), inference(superposition, [status(thm), theory('equality')], [c_44, c_16])).
% 28.97/20.88  tff(c_21104, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_20912, c_60])).
% 28.97/20.88  tff(c_24, plain, (![A_24, B_25, C_26]: (r1_tarski(k4_xboole_0(A_24, B_25), C_26) | ~r1_tarski(A_24, k2_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 28.97/20.88  tff(c_88328, plain, (![C_707]: (r1_tarski('#skF_3', C_707) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_707)))), inference(superposition, [status(thm), theory('equality')], [c_21104, c_24])).
% 28.97/20.88  tff(c_129978, plain, (![A_833]: (r1_tarski('#skF_3', A_833) | ~r1_tarski('#skF_3', k2_xboole_0(A_833, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_88328])).
% 28.97/20.88  tff(c_130053, plain, (r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1037, c_129978])).
% 28.97/20.88  tff(c_130085, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_599, c_130053])).
% 28.97/20.88  tff(c_130087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_130085])).
% 28.97/20.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.97/20.88  
% 28.97/20.88  Inference rules
% 28.97/20.88  ----------------------
% 28.97/20.88  #Ref     : 0
% 28.97/20.88  #Sup     : 32389
% 28.97/20.88  #Fact    : 0
% 28.97/20.88  #Define  : 0
% 28.97/20.88  #Split   : 8
% 28.97/20.88  #Chain   : 0
% 28.97/20.88  #Close   : 0
% 28.97/20.88  
% 28.97/20.88  Ordering : KBO
% 28.97/20.88  
% 28.97/20.88  Simplification rules
% 28.97/20.88  ----------------------
% 28.97/20.88  #Subsume      : 1236
% 28.97/20.88  #Demod        : 37040
% 28.97/20.88  #Tautology    : 21401
% 28.97/20.88  #SimpNegUnit  : 44
% 28.97/20.88  #BackRed      : 56
% 28.97/20.88  
% 28.97/20.88  #Partial instantiations: 0
% 28.97/20.88  #Strategies tried      : 1
% 28.97/20.88  
% 28.97/20.88  Timing (in seconds)
% 28.97/20.88  ----------------------
% 28.97/20.89  Preprocessing        : 0.29
% 28.97/20.89  Parsing              : 0.17
% 28.97/20.89  CNF conversion       : 0.02
% 28.97/20.89  Main loop            : 19.83
% 28.97/20.89  Inferencing          : 1.90
% 28.97/20.89  Reduction            : 13.54
% 28.97/20.89  Demodulation         : 12.60
% 28.97/20.89  BG Simplification    : 0.23
% 28.97/20.89  Subsumption          : 3.47
% 28.97/20.89  Abstraction          : 0.40
% 28.97/20.89  MUC search           : 0.00
% 28.97/20.89  Cooper               : 0.00
% 28.97/20.89  Total                : 20.16
% 28.97/20.89  Index Insertion      : 0.00
% 28.97/20.89  Index Deletion       : 0.00
% 28.97/20.89  Index Matching       : 0.00
% 28.97/20.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
