%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:16 EST 2020

% Result     : Theorem 9.17s
% Output     : CNFRefutation 9.17s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 106 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   81 ( 177 expanded)
%              Number of equality atoms :   18 (  42 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_154,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(c_76,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_260,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_84,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_144,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_1256,plain,(
    ! [A_150,B_151,C_152] :
      ( r1_tarski(A_150,k2_xboole_0(B_151,C_152))
      | ~ r1_tarski(k4_xboole_0(A_150,B_151),C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1287,plain,(
    ! [C_152] :
      ( r1_tarski(k2_tarski('#skF_6','#skF_7'),k2_xboole_0('#skF_8',C_152))
      | ~ r1_tarski(k1_xboole_0,C_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_1256])).

tff(c_1384,plain,(
    ! [C_156] : r1_tarski(k2_tarski('#skF_6','#skF_7'),k2_xboole_0('#skF_8',C_156)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1287])).

tff(c_58,plain,(
    ! [A_46,C_48,B_47] :
      ( r2_hidden(A_46,C_48)
      | ~ r1_tarski(k2_tarski(A_46,B_47),C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1417,plain,(
    ! [C_157] : r2_hidden('#skF_6',k2_xboole_0('#skF_8',C_157)) ),
    inference(resolution,[status(thm)],[c_1384,c_58])).

tff(c_1433,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1417])).

tff(c_1440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_1433])).

tff(c_1442,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1441,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1443,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1441])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1768,plain,(
    ! [B_195,C_196,A_197] :
      ( r2_hidden(B_195,C_196)
      | ~ r1_tarski(k2_tarski(A_197,B_195),C_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2693,plain,(
    ! [B_244,B_245,A_246] :
      ( r2_hidden(B_244,B_245)
      | k4_xboole_0(k2_tarski(A_246,B_244),B_245) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_1768])).

tff(c_2708,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_2693])).

tff(c_2718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1443,c_2708])).

tff(c_2720,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1441])).

tff(c_78,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2833,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1442,c_2720,c_78])).

tff(c_2719,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1441])).

tff(c_4911,plain,(
    ! [A_368,B_369,C_370] :
      ( r1_tarski(k2_tarski(A_368,B_369),C_370)
      | ~ r2_hidden(B_369,C_370)
      | ~ r2_hidden(A_368,C_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12917,plain,(
    ! [A_690,B_691,C_692] :
      ( k4_xboole_0(k2_tarski(A_690,B_691),C_692) = k1_xboole_0
      | ~ r2_hidden(B_691,C_692)
      | ~ r2_hidden(A_690,C_692) ) ),
    inference(resolution,[status(thm)],[c_4911,c_24])).

tff(c_74,plain,
    ( k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_3208,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1442,c_2720,c_74])).

tff(c_13146,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12917,c_3208])).

tff(c_13254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2719,c_13146])).

tff(c_13255,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_13256,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_82,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_13470,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_13256,c_82])).

tff(c_15144,plain,(
    ! [A_818,B_819,C_820] :
      ( r1_tarski(k2_tarski(A_818,B_819),C_820)
      | ~ r2_hidden(B_819,C_820)
      | ~ r2_hidden(A_818,C_820) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_22762,plain,(
    ! [A_1128,B_1129,C_1130] :
      ( k4_xboole_0(k2_tarski(A_1128,B_1129),C_1130) = k1_xboole_0
      | ~ r2_hidden(B_1129,C_1130)
      | ~ r2_hidden(A_1128,C_1130) ) ),
    inference(resolution,[status(thm)],[c_15144,c_24])).

tff(c_80,plain,
    ( k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0
    | k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_13789,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_13256,c_80])).

tff(c_22945,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_22762,c_13789])).

tff(c_23036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13255,c_13470,c_22945])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:36:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.17/3.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.17/3.64  
% 9.17/3.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.17/3.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 9.17/3.64  
% 9.17/3.64  %Foreground sorts:
% 9.17/3.64  
% 9.17/3.64  
% 9.17/3.64  %Background operators:
% 9.17/3.64  
% 9.17/3.64  
% 9.17/3.64  %Foreground operators:
% 9.17/3.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.17/3.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.17/3.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.17/3.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.17/3.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.17/3.64  tff('#skF_7', type, '#skF_7': $i).
% 9.17/3.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.17/3.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.17/3.64  tff('#skF_5', type, '#skF_5': $i).
% 9.17/3.64  tff('#skF_6', type, '#skF_6': $i).
% 9.17/3.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.17/3.64  tff('#skF_3', type, '#skF_3': $i).
% 9.17/3.64  tff('#skF_8', type, '#skF_8': $i).
% 9.17/3.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.17/3.64  tff('#skF_4', type, '#skF_4': $i).
% 9.17/3.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.17/3.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.17/3.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.17/3.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.17/3.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.17/3.64  
% 9.17/3.65  tff(f_154, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 9.17/3.65  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.17/3.65  tff(f_67, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.17/3.65  tff(f_75, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 9.17/3.65  tff(f_124, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 9.17/3.65  tff(f_71, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 9.17/3.65  tff(c_76, plain, (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.17/3.65  tff(c_260, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_76])).
% 9.17/3.65  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.17/3.65  tff(c_20, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.17/3.65  tff(c_84, plain, (r2_hidden('#skF_3', '#skF_5') | k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.17/3.65  tff(c_144, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_84])).
% 9.17/3.65  tff(c_1256, plain, (![A_150, B_151, C_152]: (r1_tarski(A_150, k2_xboole_0(B_151, C_152)) | ~r1_tarski(k4_xboole_0(A_150, B_151), C_152))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.17/3.65  tff(c_1287, plain, (![C_152]: (r1_tarski(k2_tarski('#skF_6', '#skF_7'), k2_xboole_0('#skF_8', C_152)) | ~r1_tarski(k1_xboole_0, C_152))), inference(superposition, [status(thm), theory('equality')], [c_144, c_1256])).
% 9.17/3.65  tff(c_1384, plain, (![C_156]: (r1_tarski(k2_tarski('#skF_6', '#skF_7'), k2_xboole_0('#skF_8', C_156)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1287])).
% 9.17/3.65  tff(c_58, plain, (![A_46, C_48, B_47]: (r2_hidden(A_46, C_48) | ~r1_tarski(k2_tarski(A_46, B_47), C_48))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.17/3.65  tff(c_1417, plain, (![C_157]: (r2_hidden('#skF_6', k2_xboole_0('#skF_8', C_157)))), inference(resolution, [status(thm)], [c_1384, c_58])).
% 9.17/3.65  tff(c_1433, plain, (r2_hidden('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4, c_1417])).
% 9.17/3.65  tff(c_1440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_1433])).
% 9.17/3.65  tff(c_1442, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_76])).
% 9.17/3.65  tff(c_1441, plain, (~r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_76])).
% 9.17/3.65  tff(c_1443, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_1441])).
% 9.17/3.65  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | k4_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.17/3.65  tff(c_1768, plain, (![B_195, C_196, A_197]: (r2_hidden(B_195, C_196) | ~r1_tarski(k2_tarski(A_197, B_195), C_196))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.17/3.65  tff(c_2693, plain, (![B_244, B_245, A_246]: (r2_hidden(B_244, B_245) | k4_xboole_0(k2_tarski(A_246, B_244), B_245)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_1768])).
% 9.17/3.65  tff(c_2708, plain, (r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_144, c_2693])).
% 9.17/3.65  tff(c_2718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1443, c_2708])).
% 9.17/3.65  tff(c_2720, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_1441])).
% 9.17/3.65  tff(c_78, plain, (r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.17/3.65  tff(c_2833, plain, (r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1442, c_2720, c_78])).
% 9.17/3.65  tff(c_2719, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1441])).
% 9.17/3.65  tff(c_4911, plain, (![A_368, B_369, C_370]: (r1_tarski(k2_tarski(A_368, B_369), C_370) | ~r2_hidden(B_369, C_370) | ~r2_hidden(A_368, C_370))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.17/3.65  tff(c_24, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.17/3.65  tff(c_12917, plain, (![A_690, B_691, C_692]: (k4_xboole_0(k2_tarski(A_690, B_691), C_692)=k1_xboole_0 | ~r2_hidden(B_691, C_692) | ~r2_hidden(A_690, C_692))), inference(resolution, [status(thm)], [c_4911, c_24])).
% 9.17/3.65  tff(c_74, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.17/3.65  tff(c_3208, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1442, c_2720, c_74])).
% 9.17/3.65  tff(c_13146, plain, (~r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12917, c_3208])).
% 9.17/3.65  tff(c_13254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2719, c_13146])).
% 9.17/3.65  tff(c_13255, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_84])).
% 9.17/3.65  tff(c_13256, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_84])).
% 9.17/3.65  tff(c_82, plain, (r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.17/3.65  tff(c_13470, plain, (r2_hidden('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_13256, c_82])).
% 9.17/3.65  tff(c_15144, plain, (![A_818, B_819, C_820]: (r1_tarski(k2_tarski(A_818, B_819), C_820) | ~r2_hidden(B_819, C_820) | ~r2_hidden(A_818, C_820))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.17/3.65  tff(c_22762, plain, (![A_1128, B_1129, C_1130]: (k4_xboole_0(k2_tarski(A_1128, B_1129), C_1130)=k1_xboole_0 | ~r2_hidden(B_1129, C_1130) | ~r2_hidden(A_1128, C_1130))), inference(resolution, [status(thm)], [c_15144, c_24])).
% 9.17/3.65  tff(c_80, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0 | k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.17/3.65  tff(c_13789, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_13256, c_80])).
% 9.17/3.65  tff(c_22945, plain, (~r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22762, c_13789])).
% 9.17/3.65  tff(c_23036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13255, c_13470, c_22945])).
% 9.17/3.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.17/3.65  
% 9.17/3.65  Inference rules
% 9.17/3.65  ----------------------
% 9.17/3.65  #Ref     : 8
% 9.17/3.65  #Sup     : 5533
% 9.17/3.65  #Fact    : 0
% 9.17/3.65  #Define  : 0
% 9.17/3.65  #Split   : 5
% 9.17/3.65  #Chain   : 0
% 9.17/3.65  #Close   : 0
% 9.17/3.65  
% 9.17/3.65  Ordering : KBO
% 9.17/3.65  
% 9.17/3.65  Simplification rules
% 9.17/3.65  ----------------------
% 9.17/3.65  #Subsume      : 1735
% 9.17/3.65  #Demod        : 2216
% 9.17/3.65  #Tautology    : 2185
% 9.17/3.65  #SimpNegUnit  : 235
% 9.17/3.65  #BackRed      : 1
% 9.17/3.65  
% 9.17/3.65  #Partial instantiations: 0
% 9.17/3.65  #Strategies tried      : 1
% 9.17/3.65  
% 9.17/3.65  Timing (in seconds)
% 9.17/3.65  ----------------------
% 9.17/3.65  Preprocessing        : 0.46
% 9.17/3.65  Parsing              : 0.28
% 9.40/3.65  CNF conversion       : 0.03
% 9.40/3.65  Main loop            : 2.38
% 9.40/3.65  Inferencing          : 0.65
% 9.40/3.65  Reduction            : 1.00
% 9.40/3.65  Demodulation         : 0.75
% 9.40/3.65  BG Simplification    : 0.07
% 9.40/3.65  Subsumption          : 0.50
% 9.40/3.66  Abstraction          : 0.09
% 9.40/3.66  MUC search           : 0.00
% 9.40/3.66  Cooper               : 0.00
% 9.40/3.66  Total                : 2.87
% 9.40/3.66  Index Insertion      : 0.00
% 9.40/3.66  Index Deletion       : 0.00
% 9.40/3.66  Index Matching       : 0.00
% 9.40/3.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
