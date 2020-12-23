%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:29 EST 2020

% Result     : Theorem 8.64s
% Output     : CNFRefutation 8.82s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 128 expanded)
%              Number of leaves         :   36 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 ( 122 expanded)
%              Number of equality atoms :   37 (  95 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_68,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_614,plain,(
    ! [A_141,B_142] : k5_xboole_0(k5_xboole_0(A_141,B_142),k2_xboole_0(A_141,B_142)) = k3_xboole_0(A_141,B_142) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_672,plain,(
    ! [A_8] : k5_xboole_0(k5_xboole_0(A_8,A_8),A_8) = k3_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_614])).

tff(c_678,plain,(
    ! [A_8] : k5_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16,c_672])).

tff(c_376,plain,(
    ! [A_130,B_131,C_132] : k5_xboole_0(k5_xboole_0(A_130,B_131),C_132) = k5_xboole_0(A_130,k5_xboole_0(B_131,C_132)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_415,plain,(
    ! [A_15,C_132] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_132)) = k5_xboole_0(k1_xboole_0,C_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_376])).

tff(c_840,plain,(
    ! [A_15,C_132] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_132)) = C_132 ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_415])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_682,plain,(
    ! [A_143] : k5_xboole_0(k1_xboole_0,A_143) = A_143 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16,c_672])).

tff(c_713,plain,(
    ! [A_143] : k5_xboole_0(A_143,k1_xboole_0) = A_143 ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_2])).

tff(c_70,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),C_14) = k5_xboole_0(A_12,k5_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11682,plain,(
    ! [A_19227,B_19228] : k5_xboole_0(A_19227,k5_xboole_0(B_19228,k2_xboole_0(A_19227,B_19228))) = k3_xboole_0(A_19227,B_19228) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_14])).

tff(c_14081,plain,(
    ! [B_20519,A_20520] : k5_xboole_0(B_20519,k2_xboole_0(A_20520,B_20519)) = k5_xboole_0(A_20520,k3_xboole_0(A_20520,B_20519)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11682,c_840])).

tff(c_14329,plain,(
    k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k2_tarski('#skF_4','#skF_5')) = k5_xboole_0('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_14081])).

tff(c_14357,plain,(
    k5_xboole_0('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14329])).

tff(c_841,plain,(
    ! [A_149,C_150] : k5_xboole_0(A_149,k5_xboole_0(A_149,C_150)) = C_150 ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_415])).

tff(c_901,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),k5_xboole_0(A_12,k5_xboole_0(B_13,C_14))) = C_14 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_841])).

tff(c_14377,plain,(
    ! [A_12] : k5_xboole_0(k5_xboole_0(A_12,'#skF_6'),k5_xboole_0(A_12,k1_xboole_0)) = k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_14357,c_901])).

tff(c_14438,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_2,c_713,c_14377])).

tff(c_66,plain,(
    ! [A_74,B_75] : k3_tarski(k2_tarski(A_74,B_75)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_145,plain,(
    ! [A_91,B_92] : k1_enumset1(A_91,A_91,B_92) = k2_tarski(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [E_24,B_19,C_20] : r2_hidden(E_24,k1_enumset1(E_24,B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_151,plain,(
    ! [A_91,B_92] : r2_hidden(A_91,k2_tarski(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_26])).

tff(c_64,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,k3_tarski(B_73))
      | ~ r2_hidden(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_231,plain,(
    ! [C_113,B_114,A_115] :
      ( r2_hidden(C_113,B_114)
      | ~ r2_hidden(C_113,A_115)
      | ~ r1_tarski(A_115,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_327,plain,(
    ! [A_125,B_126,B_127] :
      ( r2_hidden(A_125,B_126)
      | ~ r1_tarski(k2_tarski(A_125,B_127),B_126) ) ),
    inference(resolution,[status(thm)],[c_151,c_231])).

tff(c_6086,plain,(
    ! [A_12418,B_12419,B_12420] :
      ( r2_hidden(A_12418,k3_tarski(B_12419))
      | ~ r2_hidden(k2_tarski(A_12418,B_12420),B_12419) ) ),
    inference(resolution,[status(thm)],[c_64,c_327])).

tff(c_6129,plain,(
    ! [A_12418,B_12420,B_92] : r2_hidden(A_12418,k3_tarski(k2_tarski(k2_tarski(A_12418,B_12420),B_92))) ),
    inference(resolution,[status(thm)],[c_151,c_6086])).

tff(c_6157,plain,(
    ! [A_12418,B_12420,B_92] : r2_hidden(A_12418,k2_xboole_0(k2_tarski(A_12418,B_12420),B_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6129])).

tff(c_14486,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_14438,c_6157])).

tff(c_14503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_14486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:40:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.64/3.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.64/3.10  
% 8.64/3.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.82/3.10  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 8.82/3.10  
% 8.82/3.10  %Foreground sorts:
% 8.82/3.10  
% 8.82/3.10  
% 8.82/3.10  %Background operators:
% 8.82/3.10  
% 8.82/3.10  
% 8.82/3.10  %Foreground operators:
% 8.82/3.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.82/3.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.82/3.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.82/3.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.82/3.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.82/3.10  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.82/3.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.82/3.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.82/3.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.82/3.10  tff('#skF_5', type, '#skF_5': $i).
% 8.82/3.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 8.82/3.10  tff('#skF_6', type, '#skF_6': $i).
% 8.82/3.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.82/3.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.82/3.10  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.82/3.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.82/3.10  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.82/3.10  tff('#skF_4', type, '#skF_4': $i).
% 8.82/3.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.82/3.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.82/3.10  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 8.82/3.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.82/3.10  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.82/3.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.82/3.10  
% 8.82/3.11  tff(f_90, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 8.82/3.11  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.82/3.11  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.82/3.11  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 8.82/3.11  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 8.82/3.11  tff(f_40, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.82/3.11  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.82/3.11  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.82/3.11  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.82/3.11  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 8.82/3.11  tff(f_83, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 8.82/3.11  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.82/3.11  tff(c_68, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.82/3.11  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.82/3.11  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.82/3.11  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.82/3.11  tff(c_614, plain, (![A_141, B_142]: (k5_xboole_0(k5_xboole_0(A_141, B_142), k2_xboole_0(A_141, B_142))=k3_xboole_0(A_141, B_142))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.82/3.11  tff(c_672, plain, (![A_8]: (k5_xboole_0(k5_xboole_0(A_8, A_8), A_8)=k3_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_614])).
% 8.82/3.11  tff(c_678, plain, (![A_8]: (k5_xboole_0(k1_xboole_0, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16, c_672])).
% 8.82/3.11  tff(c_376, plain, (![A_130, B_131, C_132]: (k5_xboole_0(k5_xboole_0(A_130, B_131), C_132)=k5_xboole_0(A_130, k5_xboole_0(B_131, C_132)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.82/3.11  tff(c_415, plain, (![A_15, C_132]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_132))=k5_xboole_0(k1_xboole_0, C_132))), inference(superposition, [status(thm), theory('equality')], [c_16, c_376])).
% 8.82/3.11  tff(c_840, plain, (![A_15, C_132]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_132))=C_132)), inference(demodulation, [status(thm), theory('equality')], [c_678, c_415])).
% 8.82/3.11  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.82/3.11  tff(c_682, plain, (![A_143]: (k5_xboole_0(k1_xboole_0, A_143)=A_143)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16, c_672])).
% 8.82/3.11  tff(c_713, plain, (![A_143]: (k5_xboole_0(A_143, k1_xboole_0)=A_143)), inference(superposition, [status(thm), theory('equality')], [c_682, c_2])).
% 8.82/3.11  tff(c_70, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.82/3.11  tff(c_14, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), C_14)=k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.82/3.11  tff(c_11682, plain, (![A_19227, B_19228]: (k5_xboole_0(A_19227, k5_xboole_0(B_19228, k2_xboole_0(A_19227, B_19228)))=k3_xboole_0(A_19227, B_19228))), inference(superposition, [status(thm), theory('equality')], [c_614, c_14])).
% 8.82/3.11  tff(c_14081, plain, (![B_20519, A_20520]: (k5_xboole_0(B_20519, k2_xboole_0(A_20520, B_20519))=k5_xboole_0(A_20520, k3_xboole_0(A_20520, B_20519)))), inference(superposition, [status(thm), theory('equality')], [c_11682, c_840])).
% 8.82/3.11  tff(c_14329, plain, (k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k2_tarski('#skF_4', '#skF_5'))=k5_xboole_0('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_14081])).
% 8.82/3.11  tff(c_14357, plain, (k5_xboole_0('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14329])).
% 8.82/3.11  tff(c_841, plain, (![A_149, C_150]: (k5_xboole_0(A_149, k5_xboole_0(A_149, C_150))=C_150)), inference(demodulation, [status(thm), theory('equality')], [c_678, c_415])).
% 8.82/3.11  tff(c_901, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))=C_14)), inference(superposition, [status(thm), theory('equality')], [c_14, c_841])).
% 8.82/3.11  tff(c_14377, plain, (![A_12]: (k5_xboole_0(k5_xboole_0(A_12, '#skF_6'), k5_xboole_0(A_12, k1_xboole_0))=k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_14357, c_901])).
% 8.82/3.11  tff(c_14438, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_840, c_2, c_713, c_14377])).
% 8.82/3.11  tff(c_66, plain, (![A_74, B_75]: (k3_tarski(k2_tarski(A_74, B_75))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.82/3.11  tff(c_145, plain, (![A_91, B_92]: (k1_enumset1(A_91, A_91, B_92)=k2_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.82/3.11  tff(c_26, plain, (![E_24, B_19, C_20]: (r2_hidden(E_24, k1_enumset1(E_24, B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.82/3.11  tff(c_151, plain, (![A_91, B_92]: (r2_hidden(A_91, k2_tarski(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_26])).
% 8.82/3.11  tff(c_64, plain, (![A_72, B_73]: (r1_tarski(A_72, k3_tarski(B_73)) | ~r2_hidden(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.82/3.11  tff(c_231, plain, (![C_113, B_114, A_115]: (r2_hidden(C_113, B_114) | ~r2_hidden(C_113, A_115) | ~r1_tarski(A_115, B_114))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.82/3.11  tff(c_327, plain, (![A_125, B_126, B_127]: (r2_hidden(A_125, B_126) | ~r1_tarski(k2_tarski(A_125, B_127), B_126))), inference(resolution, [status(thm)], [c_151, c_231])).
% 8.82/3.11  tff(c_6086, plain, (![A_12418, B_12419, B_12420]: (r2_hidden(A_12418, k3_tarski(B_12419)) | ~r2_hidden(k2_tarski(A_12418, B_12420), B_12419))), inference(resolution, [status(thm)], [c_64, c_327])).
% 8.82/3.11  tff(c_6129, plain, (![A_12418, B_12420, B_92]: (r2_hidden(A_12418, k3_tarski(k2_tarski(k2_tarski(A_12418, B_12420), B_92))))), inference(resolution, [status(thm)], [c_151, c_6086])).
% 8.82/3.11  tff(c_6157, plain, (![A_12418, B_12420, B_92]: (r2_hidden(A_12418, k2_xboole_0(k2_tarski(A_12418, B_12420), B_92)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6129])).
% 8.82/3.11  tff(c_14486, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_14438, c_6157])).
% 8.82/3.11  tff(c_14503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_14486])).
% 8.82/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.82/3.11  
% 8.82/3.11  Inference rules
% 8.82/3.11  ----------------------
% 8.82/3.11  #Ref     : 0
% 8.82/3.11  #Sup     : 2489
% 8.82/3.11  #Fact    : 18
% 8.82/3.11  #Define  : 0
% 8.82/3.11  #Split   : 0
% 8.82/3.11  #Chain   : 0
% 8.82/3.11  #Close   : 0
% 8.82/3.11  
% 8.82/3.11  Ordering : KBO
% 8.82/3.11  
% 8.82/3.11  Simplification rules
% 8.82/3.11  ----------------------
% 8.82/3.11  #Subsume      : 151
% 8.82/3.11  #Demod        : 1773
% 8.82/3.11  #Tautology    : 922
% 8.82/3.11  #SimpNegUnit  : 1
% 8.82/3.11  #BackRed      : 4
% 8.82/3.11  
% 8.82/3.11  #Partial instantiations: 7353
% 8.82/3.11  #Strategies tried      : 1
% 8.82/3.11  
% 8.82/3.11  Timing (in seconds)
% 8.82/3.11  ----------------------
% 8.82/3.12  Preprocessing        : 0.34
% 8.82/3.12  Parsing              : 0.17
% 8.82/3.12  CNF conversion       : 0.03
% 8.82/3.12  Main loop            : 2.02
% 8.82/3.12  Inferencing          : 0.81
% 8.82/3.12  Reduction            : 0.80
% 8.82/3.12  Demodulation         : 0.70
% 8.82/3.12  BG Simplification    : 0.08
% 8.82/3.12  Subsumption          : 0.25
% 8.82/3.12  Abstraction          : 0.09
% 8.82/3.12  MUC search           : 0.00
% 8.82/3.12  Cooper               : 0.00
% 8.82/3.12  Total                : 2.39
% 8.82/3.12  Index Insertion      : 0.00
% 8.82/3.12  Index Deletion       : 0.00
% 8.82/3.12  Index Matching       : 0.00
% 8.82/3.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
