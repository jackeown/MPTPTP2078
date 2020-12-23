%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:51 EST 2020

% Result     : Theorem 19.44s
% Output     : CNFRefutation 19.44s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 155 expanded)
%              Number of leaves         :   29 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 219 expanded)
%              Number of equality atoms :   33 ( 119 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_117,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_110,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_252,plain,(
    ! [A_96,B_97] :
      ( k2_xboole_0(k1_tarski(A_96),B_97) = B_97
      | ~ r2_hidden(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_438,plain,(
    ! [A_120,A_121] :
      ( k2_xboole_0(A_120,k1_tarski(A_121)) = A_120
      | ~ r2_hidden(A_121,A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_252])).

tff(c_108,plain,(
    k4_xboole_0(k2_xboole_0('#skF_11',k1_tarski('#skF_9')),k1_tarski('#skF_10')) != k2_xboole_0(k4_xboole_0('#skF_11',k1_tarski('#skF_10')),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_112,plain,(
    k4_xboole_0(k2_xboole_0('#skF_11',k1_tarski('#skF_9')),k1_tarski('#skF_10')) != k2_xboole_0(k1_tarski('#skF_9'),k4_xboole_0('#skF_11',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_108])).

tff(c_470,plain,
    ( k2_xboole_0(k1_tarski('#skF_9'),k4_xboole_0('#skF_11',k1_tarski('#skF_10'))) != k4_xboole_0('#skF_11',k1_tarski('#skF_10'))
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_112])).

tff(c_538,plain,(
    ~ r2_hidden('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | r2_hidden(D_8,k2_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_62,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1854,plain,(
    ! [D_194,B_195,A_196] :
      ( r2_hidden(D_194,B_195)
      | r2_hidden(D_194,A_196)
      | ~ r2_hidden(D_194,k2_xboole_0(A_196,B_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_41618,plain,(
    ! [D_629,B_630,A_631] :
      ( r2_hidden(D_629,k4_xboole_0(B_630,A_631))
      | r2_hidden(D_629,A_631)
      | ~ r2_hidden(D_629,k2_xboole_0(A_631,B_630)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1854])).

tff(c_96,plain,(
    ! [A_59,B_60] :
      ( k2_xboole_0(k1_tarski(A_59),B_60) = B_60
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_230,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,k1_tarski(B_95)) = A_94
      | r2_hidden(B_95,A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_242,plain,
    ( k2_xboole_0(k1_tarski('#skF_9'),k4_xboole_0('#skF_11',k1_tarski('#skF_10'))) != k2_xboole_0('#skF_11',k1_tarski('#skF_9'))
    | r2_hidden('#skF_10',k2_xboole_0('#skF_11',k1_tarski('#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_112])).

tff(c_393,plain,(
    k2_xboole_0(k1_tarski('#skF_9'),k4_xboole_0('#skF_11',k1_tarski('#skF_10'))) != k2_xboole_0('#skF_11',k1_tarski('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_679,plain,
    ( k4_xboole_0('#skF_11',k1_tarski('#skF_10')) != k2_xboole_0('#skF_11',k1_tarski('#skF_9'))
    | ~ r2_hidden('#skF_9',k4_xboole_0('#skF_11',k1_tarski('#skF_10'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_393])).

tff(c_791,plain,(
    ~ r2_hidden('#skF_9',k4_xboole_0('#skF_11',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_679])).

tff(c_41664,plain,
    ( r2_hidden('#skF_9',k1_tarski('#skF_10'))
    | ~ r2_hidden('#skF_9',k2_xboole_0(k1_tarski('#skF_10'),'#skF_11')) ),
    inference(resolution,[status(thm)],[c_41618,c_791])).

tff(c_41702,plain,
    ( r2_hidden('#skF_9',k1_tarski('#skF_10'))
    | ~ r2_hidden('#skF_9',k2_xboole_0('#skF_11',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_41664])).

tff(c_41708,plain,(
    ~ r2_hidden('#skF_9',k2_xboole_0('#skF_11',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_41702])).

tff(c_41732,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_6,c_41708])).

tff(c_88,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(k1_tarski(A_52),B_53) = k1_tarski(A_52)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3308,plain,(
    ! [A_225,C_226,B_227] : k2_xboole_0(k4_xboole_0(A_225,C_226),k4_xboole_0(B_227,C_226)) = k4_xboole_0(k2_xboole_0(A_225,B_227),C_226) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_53270,plain,(
    ! [A_719,A_720,B_721] :
      ( k4_xboole_0(k2_xboole_0(A_719,k1_tarski(A_720)),B_721) = k2_xboole_0(k4_xboole_0(A_719,B_721),k1_tarski(A_720))
      | r2_hidden(A_720,B_721) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_3308])).

tff(c_53554,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_11',k1_tarski('#skF_10')),k1_tarski('#skF_9')) != k2_xboole_0(k1_tarski('#skF_9'),k4_xboole_0('#skF_11',k1_tarski('#skF_10')))
    | r2_hidden('#skF_9',k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_53270,c_112])).

tff(c_53702,plain,(
    r2_hidden('#skF_9',k1_tarski('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_53554])).

tff(c_53704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41732,c_53702])).

tff(c_53705,plain,(
    r2_hidden('#skF_9',k1_tarski('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_41702])).

tff(c_74,plain,(
    ! [C_51,A_47] :
      ( C_51 = A_47
      | ~ r2_hidden(C_51,k1_tarski(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_53715,plain,(
    '#skF_10' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_53705,c_74])).

tff(c_53722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_53715])).

tff(c_53724,plain,(
    r2_hidden('#skF_9',k4_xboole_0('#skF_11',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_679])).

tff(c_26,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,A_9)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_53730,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_53724,c_26])).

tff(c_53738,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_538,c_53730])).

tff(c_53740,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_54319,plain,(
    ! [D_761,A_762,B_763] :
      ( r2_hidden(D_761,k4_xboole_0(A_762,B_763))
      | r2_hidden(D_761,B_763)
      | ~ r2_hidden(D_761,A_762) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_53739,plain,(
    k2_xboole_0(k1_tarski('#skF_9'),k4_xboole_0('#skF_11',k1_tarski('#skF_10'))) != k4_xboole_0('#skF_11',k1_tarski('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_53899,plain,(
    ~ r2_hidden('#skF_9',k4_xboole_0('#skF_11',k1_tarski('#skF_10'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_53739])).

tff(c_54322,plain,
    ( r2_hidden('#skF_9',k1_tarski('#skF_10'))
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_54319,c_53899])).

tff(c_54341,plain,(
    r2_hidden('#skF_9',k1_tarski('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53740,c_54322])).

tff(c_54350,plain,(
    '#skF_10' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_54341,c_74])).

tff(c_54355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:28:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.44/10.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.44/10.96  
% 19.44/10.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.44/10.97  %$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5
% 19.44/10.97  
% 19.44/10.97  %Foreground sorts:
% 19.44/10.97  
% 19.44/10.97  
% 19.44/10.97  %Background operators:
% 19.44/10.97  
% 19.44/10.97  
% 19.44/10.97  %Foreground operators:
% 19.44/10.97  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 19.44/10.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 19.44/10.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.44/10.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.44/10.97  tff('#skF_11', type, '#skF_11': $i).
% 19.44/10.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 19.44/10.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 19.44/10.97  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 19.44/10.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.44/10.97  tff('#skF_10', type, '#skF_10': $i).
% 19.44/10.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 19.44/10.97  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 19.44/10.97  tff('#skF_9', type, '#skF_9': $i).
% 19.44/10.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.44/10.97  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 19.44/10.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.44/10.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.44/10.97  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 19.44/10.97  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 19.44/10.97  
% 19.44/10.98  tff(f_135, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 19.44/10.98  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 19.44/10.98  tff(f_117, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 19.44/10.98  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 19.44/10.98  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 19.44/10.98  tff(f_129, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 19.44/10.98  tff(f_103, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 19.44/10.98  tff(f_77, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 19.44/10.98  tff(f_98, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 19.44/10.98  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 19.44/10.98  tff(c_110, plain, ('#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_135])).
% 19.44/10.98  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.44/10.98  tff(c_252, plain, (![A_96, B_97]: (k2_xboole_0(k1_tarski(A_96), B_97)=B_97 | ~r2_hidden(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_117])).
% 19.44/10.98  tff(c_438, plain, (![A_120, A_121]: (k2_xboole_0(A_120, k1_tarski(A_121))=A_120 | ~r2_hidden(A_121, A_120))), inference(superposition, [status(thm), theory('equality')], [c_2, c_252])).
% 19.44/10.98  tff(c_108, plain, (k4_xboole_0(k2_xboole_0('#skF_11', k1_tarski('#skF_9')), k1_tarski('#skF_10'))!=k2_xboole_0(k4_xboole_0('#skF_11', k1_tarski('#skF_10')), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 19.44/10.98  tff(c_112, plain, (k4_xboole_0(k2_xboole_0('#skF_11', k1_tarski('#skF_9')), k1_tarski('#skF_10'))!=k2_xboole_0(k1_tarski('#skF_9'), k4_xboole_0('#skF_11', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_108])).
% 19.44/10.98  tff(c_470, plain, (k2_xboole_0(k1_tarski('#skF_9'), k4_xboole_0('#skF_11', k1_tarski('#skF_10')))!=k4_xboole_0('#skF_11', k1_tarski('#skF_10')) | ~r2_hidden('#skF_9', '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_438, c_112])).
% 19.44/10.98  tff(c_538, plain, (~r2_hidden('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_470])).
% 19.44/10.98  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | r2_hidden(D_8, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 19.44/10.98  tff(c_62, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.44/10.98  tff(c_1854, plain, (![D_194, B_195, A_196]: (r2_hidden(D_194, B_195) | r2_hidden(D_194, A_196) | ~r2_hidden(D_194, k2_xboole_0(A_196, B_195)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 19.44/10.98  tff(c_41618, plain, (![D_629, B_630, A_631]: (r2_hidden(D_629, k4_xboole_0(B_630, A_631)) | r2_hidden(D_629, A_631) | ~r2_hidden(D_629, k2_xboole_0(A_631, B_630)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1854])).
% 19.44/10.98  tff(c_96, plain, (![A_59, B_60]: (k2_xboole_0(k1_tarski(A_59), B_60)=B_60 | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_117])).
% 19.44/10.98  tff(c_230, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k1_tarski(B_95))=A_94 | r2_hidden(B_95, A_94))), inference(cnfTransformation, [status(thm)], [f_129])).
% 19.44/10.98  tff(c_242, plain, (k2_xboole_0(k1_tarski('#skF_9'), k4_xboole_0('#skF_11', k1_tarski('#skF_10')))!=k2_xboole_0('#skF_11', k1_tarski('#skF_9')) | r2_hidden('#skF_10', k2_xboole_0('#skF_11', k1_tarski('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_230, c_112])).
% 19.44/10.98  tff(c_393, plain, (k2_xboole_0(k1_tarski('#skF_9'), k4_xboole_0('#skF_11', k1_tarski('#skF_10')))!=k2_xboole_0('#skF_11', k1_tarski('#skF_9'))), inference(splitLeft, [status(thm)], [c_242])).
% 19.44/10.98  tff(c_679, plain, (k4_xboole_0('#skF_11', k1_tarski('#skF_10'))!=k2_xboole_0('#skF_11', k1_tarski('#skF_9')) | ~r2_hidden('#skF_9', k4_xboole_0('#skF_11', k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_393])).
% 19.44/10.98  tff(c_791, plain, (~r2_hidden('#skF_9', k4_xboole_0('#skF_11', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_679])).
% 19.44/10.98  tff(c_41664, plain, (r2_hidden('#skF_9', k1_tarski('#skF_10')) | ~r2_hidden('#skF_9', k2_xboole_0(k1_tarski('#skF_10'), '#skF_11'))), inference(resolution, [status(thm)], [c_41618, c_791])).
% 19.44/10.98  tff(c_41702, plain, (r2_hidden('#skF_9', k1_tarski('#skF_10')) | ~r2_hidden('#skF_9', k2_xboole_0('#skF_11', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_41664])).
% 19.44/10.98  tff(c_41708, plain, (~r2_hidden('#skF_9', k2_xboole_0('#skF_11', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_41702])).
% 19.44/10.98  tff(c_41732, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_6, c_41708])).
% 19.44/10.98  tff(c_88, plain, (![A_52, B_53]: (k4_xboole_0(k1_tarski(A_52), B_53)=k1_tarski(A_52) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.44/10.98  tff(c_3308, plain, (![A_225, C_226, B_227]: (k2_xboole_0(k4_xboole_0(A_225, C_226), k4_xboole_0(B_227, C_226))=k4_xboole_0(k2_xboole_0(A_225, B_227), C_226))), inference(cnfTransformation, [status(thm)], [f_77])).
% 19.44/10.98  tff(c_53270, plain, (![A_719, A_720, B_721]: (k4_xboole_0(k2_xboole_0(A_719, k1_tarski(A_720)), B_721)=k2_xboole_0(k4_xboole_0(A_719, B_721), k1_tarski(A_720)) | r2_hidden(A_720, B_721))), inference(superposition, [status(thm), theory('equality')], [c_88, c_3308])).
% 19.44/10.98  tff(c_53554, plain, (k2_xboole_0(k4_xboole_0('#skF_11', k1_tarski('#skF_10')), k1_tarski('#skF_9'))!=k2_xboole_0(k1_tarski('#skF_9'), k4_xboole_0('#skF_11', k1_tarski('#skF_10'))) | r2_hidden('#skF_9', k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_53270, c_112])).
% 19.44/10.98  tff(c_53702, plain, (r2_hidden('#skF_9', k1_tarski('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_53554])).
% 19.44/10.98  tff(c_53704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41732, c_53702])).
% 19.44/10.98  tff(c_53705, plain, (r2_hidden('#skF_9', k1_tarski('#skF_10'))), inference(splitRight, [status(thm)], [c_41702])).
% 19.44/10.98  tff(c_74, plain, (![C_51, A_47]: (C_51=A_47 | ~r2_hidden(C_51, k1_tarski(A_47)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 19.44/10.98  tff(c_53715, plain, ('#skF_10'='#skF_9'), inference(resolution, [status(thm)], [c_53705, c_74])).
% 19.44/10.98  tff(c_53722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_53715])).
% 19.44/10.98  tff(c_53724, plain, (r2_hidden('#skF_9', k4_xboole_0('#skF_11', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_679])).
% 19.44/10.98  tff(c_26, plain, (![D_14, A_9, B_10]: (r2_hidden(D_14, A_9) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.44/10.98  tff(c_53730, plain, (r2_hidden('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_53724, c_26])).
% 19.44/10.98  tff(c_53738, plain, $false, inference(negUnitSimplification, [status(thm)], [c_538, c_53730])).
% 19.44/10.98  tff(c_53740, plain, (r2_hidden('#skF_9', '#skF_11')), inference(splitRight, [status(thm)], [c_470])).
% 19.44/10.98  tff(c_54319, plain, (![D_761, A_762, B_763]: (r2_hidden(D_761, k4_xboole_0(A_762, B_763)) | r2_hidden(D_761, B_763) | ~r2_hidden(D_761, A_762))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.44/10.98  tff(c_53739, plain, (k2_xboole_0(k1_tarski('#skF_9'), k4_xboole_0('#skF_11', k1_tarski('#skF_10')))!=k4_xboole_0('#skF_11', k1_tarski('#skF_10'))), inference(splitRight, [status(thm)], [c_470])).
% 19.44/10.98  tff(c_53899, plain, (~r2_hidden('#skF_9', k4_xboole_0('#skF_11', k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_53739])).
% 19.44/10.98  tff(c_54322, plain, (r2_hidden('#skF_9', k1_tarski('#skF_10')) | ~r2_hidden('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_54319, c_53899])).
% 19.44/10.98  tff(c_54341, plain, (r2_hidden('#skF_9', k1_tarski('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_53740, c_54322])).
% 19.44/10.98  tff(c_54350, plain, ('#skF_10'='#skF_9'), inference(resolution, [status(thm)], [c_54341, c_74])).
% 19.44/10.98  tff(c_54355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_54350])).
% 19.44/10.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.44/10.98  
% 19.44/10.98  Inference rules
% 19.44/10.98  ----------------------
% 19.44/10.98  #Ref     : 0
% 19.44/10.98  #Sup     : 13885
% 19.44/10.98  #Fact    : 6
% 19.44/10.98  #Define  : 0
% 19.44/10.98  #Split   : 5
% 19.44/10.98  #Chain   : 0
% 19.44/10.98  #Close   : 0
% 19.44/10.98  
% 19.44/10.98  Ordering : KBO
% 19.44/10.98  
% 19.44/10.98  Simplification rules
% 19.44/10.98  ----------------------
% 19.44/10.98  #Subsume      : 1947
% 19.44/10.98  #Demod        : 13154
% 19.44/10.98  #Tautology    : 4850
% 19.44/10.98  #SimpNegUnit  : 12
% 19.44/10.98  #BackRed      : 0
% 19.44/10.98  
% 19.44/10.98  #Partial instantiations: 0
% 19.44/10.98  #Strategies tried      : 1
% 19.44/10.98  
% 19.44/10.98  Timing (in seconds)
% 19.44/10.98  ----------------------
% 19.44/10.98  Preprocessing        : 0.38
% 19.44/10.98  Parsing              : 0.19
% 19.44/10.98  CNF conversion       : 0.03
% 19.44/10.98  Main loop            : 9.85
% 19.44/10.98  Inferencing          : 1.26
% 19.44/10.98  Reduction            : 6.17
% 19.44/10.98  Demodulation         : 5.73
% 19.44/10.98  BG Simplification    : 0.19
% 19.44/10.98  Subsumption          : 1.83
% 19.44/10.98  Abstraction          : 0.29
% 19.44/10.98  MUC search           : 0.00
% 19.44/10.98  Cooper               : 0.00
% 19.44/10.98  Total                : 10.26
% 19.44/10.98  Index Insertion      : 0.00
% 19.44/10.98  Index Deletion       : 0.00
% 19.44/10.98  Index Matching       : 0.00
% 19.44/10.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
