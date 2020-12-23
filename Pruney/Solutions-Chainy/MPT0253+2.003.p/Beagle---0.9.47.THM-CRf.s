%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:14 EST 2020

% Result     : Theorem 13.12s
% Output     : CNFRefutation 13.12s
% Verified   : 
% Statistics : Number of formulae       :   61 (  74 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 (  82 expanded)
%              Number of equality atoms :   35 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_60,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_62,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_649,plain,(
    ! [A_83,B_84] : k2_xboole_0(A_83,k4_xboole_0(B_84,A_83)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_174,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_178,plain,(
    ! [B_12] : k3_xboole_0(B_12,B_12) = B_12 ),
    inference(resolution,[status(thm)],[c_26,c_174])).

tff(c_328,plain,(
    ! [A_65,B_66] : k2_xboole_0(k3_xboole_0(A_65,B_66),k4_xboole_0(A_65,B_66)) = A_65 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_337,plain,(
    ! [B_12] : k2_xboole_0(B_12,k4_xboole_0(B_12,B_12)) = B_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_328])).

tff(c_656,plain,(
    ! [B_84] : k2_xboole_0(B_84,B_84) = B_84 ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_337])).

tff(c_34,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1541,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_tarski(k2_tarski(A_122,B_123),C_124)
      | ~ r2_hidden(B_123,C_124)
      | ~ r2_hidden(A_122,C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7621,plain,(
    ! [A_263,B_264,C_265] :
      ( k3_xboole_0(k2_tarski(A_263,B_264),C_265) = k2_tarski(A_263,B_264)
      | ~ r2_hidden(B_264,C_265)
      | ~ r2_hidden(A_263,C_265) ) ),
    inference(resolution,[status(thm)],[c_1541,c_32])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_340,plain,(
    ! [B_2,A_1] : k2_xboole_0(k3_xboole_0(B_2,A_1),k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_328])).

tff(c_7728,plain,(
    ! [A_263,B_264,C_265] :
      ( k2_xboole_0(k2_tarski(A_263,B_264),k4_xboole_0(C_265,k2_tarski(A_263,B_264))) = C_265
      | ~ r2_hidden(B_264,C_265)
      | ~ r2_hidden(A_263,C_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7621,c_340])).

tff(c_22757,plain,(
    ! [A_397,B_398,C_399] :
      ( k2_xboole_0(k2_tarski(A_397,B_398),C_399) = C_399
      | ~ r2_hidden(B_398,C_399)
      | ~ r2_hidden(A_397,C_399) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7728])).

tff(c_38,plain,(
    ! [A_21,B_22] : k4_xboole_0(k2_xboole_0(A_21,B_22),B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_672,plain,(
    ! [B_22,A_21] : k2_xboole_0(B_22,k4_xboole_0(A_21,B_22)) = k2_xboole_0(B_22,k2_xboole_0(A_21,B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_649])).

tff(c_683,plain,(
    ! [B_22,A_21] : k2_xboole_0(B_22,k2_xboole_0(A_21,B_22)) = k2_xboole_0(B_22,A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_672])).

tff(c_22933,plain,(
    ! [C_399,A_397,B_398] :
      ( k2_xboole_0(C_399,k2_tarski(A_397,B_398)) = k2_xboole_0(C_399,C_399)
      | ~ r2_hidden(B_398,C_399)
      | ~ r2_hidden(A_397,C_399) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22757,c_683])).

tff(c_37704,plain,(
    ! [C_529,A_530,B_531] :
      ( k2_xboole_0(C_529,k2_tarski(A_530,B_531)) = C_529
      | ~ r2_hidden(B_531,C_529)
      | ~ r2_hidden(A_530,C_529) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_22933])).

tff(c_42,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_150,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_188,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(B_56,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_150])).

tff(c_50,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_194,plain,(
    ! [B_56,A_55] : k2_xboole_0(B_56,A_55) = k2_xboole_0(A_55,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_50])).

tff(c_58,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_4'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_63,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_2'),'#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_58])).

tff(c_211,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_63])).

tff(c_37933,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_37704,c_211])).

tff(c_38057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_37933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:05:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.12/6.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.12/6.45  
% 13.12/6.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.12/6.45  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 13.12/6.45  
% 13.12/6.45  %Foreground sorts:
% 13.12/6.45  
% 13.12/6.45  
% 13.12/6.45  %Background operators:
% 13.12/6.45  
% 13.12/6.45  
% 13.12/6.45  %Foreground operators:
% 13.12/6.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.12/6.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.12/6.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.12/6.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.12/6.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.12/6.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.12/6.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.12/6.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.12/6.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.12/6.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.12/6.45  tff('#skF_2', type, '#skF_2': $i).
% 13.12/6.45  tff('#skF_3', type, '#skF_3': $i).
% 13.12/6.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.12/6.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.12/6.45  tff('#skF_4', type, '#skF_4': $i).
% 13.12/6.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.12/6.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.12/6.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.12/6.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.12/6.45  
% 13.12/6.47  tff(f_86, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 13.12/6.47  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.12/6.47  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.12/6.47  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.12/6.47  tff(f_63, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 13.12/6.47  tff(f_79, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 13.12/6.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.12/6.47  tff(f_61, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 13.12/6.47  tff(f_65, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.12/6.47  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 13.12/6.47  tff(c_60, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.12/6.47  tff(c_62, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.12/6.47  tff(c_649, plain, (![A_83, B_84]: (k2_xboole_0(A_83, k4_xboole_0(B_84, A_83))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.12/6.47  tff(c_26, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.12/6.47  tff(c_174, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.12/6.47  tff(c_178, plain, (![B_12]: (k3_xboole_0(B_12, B_12)=B_12)), inference(resolution, [status(thm)], [c_26, c_174])).
% 13.12/6.47  tff(c_328, plain, (![A_65, B_66]: (k2_xboole_0(k3_xboole_0(A_65, B_66), k4_xboole_0(A_65, B_66))=A_65)), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.12/6.47  tff(c_337, plain, (![B_12]: (k2_xboole_0(B_12, k4_xboole_0(B_12, B_12))=B_12)), inference(superposition, [status(thm), theory('equality')], [c_178, c_328])).
% 13.12/6.47  tff(c_656, plain, (![B_84]: (k2_xboole_0(B_84, B_84)=B_84)), inference(superposition, [status(thm), theory('equality')], [c_649, c_337])).
% 13.12/6.47  tff(c_34, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.12/6.47  tff(c_1541, plain, (![A_122, B_123, C_124]: (r1_tarski(k2_tarski(A_122, B_123), C_124) | ~r2_hidden(B_123, C_124) | ~r2_hidden(A_122, C_124))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.12/6.47  tff(c_32, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.12/6.47  tff(c_7621, plain, (![A_263, B_264, C_265]: (k3_xboole_0(k2_tarski(A_263, B_264), C_265)=k2_tarski(A_263, B_264) | ~r2_hidden(B_264, C_265) | ~r2_hidden(A_263, C_265))), inference(resolution, [status(thm)], [c_1541, c_32])).
% 13.12/6.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.12/6.47  tff(c_340, plain, (![B_2, A_1]: (k2_xboole_0(k3_xboole_0(B_2, A_1), k4_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_328])).
% 13.12/6.47  tff(c_7728, plain, (![A_263, B_264, C_265]: (k2_xboole_0(k2_tarski(A_263, B_264), k4_xboole_0(C_265, k2_tarski(A_263, B_264)))=C_265 | ~r2_hidden(B_264, C_265) | ~r2_hidden(A_263, C_265))), inference(superposition, [status(thm), theory('equality')], [c_7621, c_340])).
% 13.12/6.47  tff(c_22757, plain, (![A_397, B_398, C_399]: (k2_xboole_0(k2_tarski(A_397, B_398), C_399)=C_399 | ~r2_hidden(B_398, C_399) | ~r2_hidden(A_397, C_399))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_7728])).
% 13.12/6.47  tff(c_38, plain, (![A_21, B_22]: (k4_xboole_0(k2_xboole_0(A_21, B_22), B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.12/6.47  tff(c_672, plain, (![B_22, A_21]: (k2_xboole_0(B_22, k4_xboole_0(A_21, B_22))=k2_xboole_0(B_22, k2_xboole_0(A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_649])).
% 13.12/6.47  tff(c_683, plain, (![B_22, A_21]: (k2_xboole_0(B_22, k2_xboole_0(A_21, B_22))=k2_xboole_0(B_22, A_21))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_672])).
% 13.12/6.47  tff(c_22933, plain, (![C_399, A_397, B_398]: (k2_xboole_0(C_399, k2_tarski(A_397, B_398))=k2_xboole_0(C_399, C_399) | ~r2_hidden(B_398, C_399) | ~r2_hidden(A_397, C_399))), inference(superposition, [status(thm), theory('equality')], [c_22757, c_683])).
% 13.12/6.47  tff(c_37704, plain, (![C_529, A_530, B_531]: (k2_xboole_0(C_529, k2_tarski(A_530, B_531))=C_529 | ~r2_hidden(B_531, C_529) | ~r2_hidden(A_530, C_529))), inference(demodulation, [status(thm), theory('equality')], [c_656, c_22933])).
% 13.12/6.47  tff(c_42, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.12/6.47  tff(c_150, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.12/6.47  tff(c_188, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(B_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_42, c_150])).
% 13.12/6.47  tff(c_50, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.12/6.47  tff(c_194, plain, (![B_56, A_55]: (k2_xboole_0(B_56, A_55)=k2_xboole_0(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_188, c_50])).
% 13.12/6.47  tff(c_58, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_4'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.12/6.47  tff(c_63, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_2'), '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_58])).
% 13.12/6.47  tff(c_211, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_63])).
% 13.12/6.47  tff(c_37933, plain, (~r2_hidden('#skF_2', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37704, c_211])).
% 13.12/6.47  tff(c_38057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_37933])).
% 13.12/6.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.12/6.47  
% 13.12/6.47  Inference rules
% 13.12/6.47  ----------------------
% 13.12/6.47  #Ref     : 0
% 13.12/6.47  #Sup     : 9479
% 13.12/6.47  #Fact    : 2
% 13.12/6.47  #Define  : 0
% 13.12/6.47  #Split   : 3
% 13.12/6.47  #Chain   : 0
% 13.12/6.47  #Close   : 0
% 13.12/6.47  
% 13.12/6.47  Ordering : KBO
% 13.12/6.47  
% 13.12/6.47  Simplification rules
% 13.12/6.47  ----------------------
% 13.12/6.47  #Subsume      : 1451
% 13.12/6.47  #Demod        : 17841
% 13.12/6.47  #Tautology    : 6194
% 13.12/6.47  #SimpNegUnit  : 60
% 13.12/6.47  #BackRed      : 24
% 13.12/6.47  
% 13.12/6.47  #Partial instantiations: 0
% 13.12/6.47  #Strategies tried      : 1
% 13.12/6.47  
% 13.12/6.47  Timing (in seconds)
% 13.12/6.47  ----------------------
% 13.29/6.47  Preprocessing        : 0.33
% 13.29/6.47  Parsing              : 0.18
% 13.29/6.47  CNF conversion       : 0.02
% 13.29/6.47  Main loop            : 5.34
% 13.29/6.47  Inferencing          : 0.90
% 13.29/6.47  Reduction            : 3.40
% 13.29/6.47  Demodulation         : 3.13
% 13.29/6.47  BG Simplification    : 0.08
% 13.29/6.47  Subsumption          : 0.75
% 13.29/6.47  Abstraction          : 0.22
% 13.29/6.47  MUC search           : 0.00
% 13.29/6.47  Cooper               : 0.00
% 13.29/6.47  Total                : 5.69
% 13.29/6.47  Index Insertion      : 0.00
% 13.29/6.47  Index Deletion       : 0.00
% 13.29/6.47  Index Matching       : 0.00
% 13.29/6.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
