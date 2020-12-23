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
% DateTime   : Thu Dec  3 09:51:09 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   51 (  68 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  84 expanded)
%              Number of equality atoms :   13 (  29 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_60,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_81,plain,(
    ! [A_79,B_80] : k1_enumset1(A_79,A_79,B_80) = k2_tarski(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [E_14,A_8,B_9] : r2_hidden(E_14,k1_enumset1(A_8,B_9,E_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,(
    ! [B_80,A_79] : r2_hidden(B_80,k2_tarski(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_16])).

tff(c_69,plain,(
    ! [A_77,B_78] : k3_tarski(k2_tarski(A_77,B_78)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_56,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,k3_tarski(B_62))
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_747,plain,(
    ! [A_194,A_195,B_196] :
      ( r1_tarski(A_194,k2_xboole_0(A_195,B_196))
      | ~ r2_hidden(A_194,k2_tarski(A_195,B_196)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_56])).

tff(c_760,plain,(
    ! [B_80,A_79] : r1_tarski(B_80,k2_xboole_0(A_79,B_80)) ),
    inference(resolution,[status(thm)],[c_87,c_747])).

tff(c_62,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_102,plain,(
    ! [B_85,A_86] :
      ( B_85 = A_86
      | ~ r1_tarski(B_85,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_109,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_62,c_102])).

tff(c_175,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_175])).

tff(c_822,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_58,plain,(
    ! [A_63,B_64] : k3_tarski(k2_tarski(A_63,B_64)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18,plain,(
    ! [E_14,A_8,C_10] : r2_hidden(E_14,k1_enumset1(A_8,E_14,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    ! [A_79,B_80] : r2_hidden(A_79,k2_tarski(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_18])).

tff(c_132,plain,(
    ! [C_94,B_95,A_96] :
      ( r2_hidden(C_94,B_95)
      | ~ r2_hidden(C_94,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_151,plain,(
    ! [A_97,B_98,B_99] :
      ( r2_hidden(A_97,B_98)
      | ~ r1_tarski(k2_tarski(A_97,B_99),B_98) ) ),
    inference(resolution,[status(thm)],[c_90,c_132])).

tff(c_1145,plain,(
    ! [A_250,B_251,B_252] :
      ( r2_hidden(A_250,k3_tarski(B_251))
      | ~ r2_hidden(k2_tarski(A_250,B_252),B_251) ) ),
    inference(resolution,[status(thm)],[c_56,c_151])).

tff(c_1157,plain,(
    ! [A_250,B_252,B_80] : r2_hidden(A_250,k3_tarski(k2_tarski(k2_tarski(A_250,B_252),B_80))) ),
    inference(resolution,[status(thm)],[c_90,c_1145])).

tff(c_1190,plain,(
    ! [A_255,B_256,B_257] : r2_hidden(A_255,k2_xboole_0(k2_tarski(A_255,B_256),B_257)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1157])).

tff(c_1203,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_1190])).

tff(c_1208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.45  
% 2.80/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.45  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.80/1.45  
% 2.80/1.45  %Foreground sorts:
% 2.80/1.45  
% 2.80/1.45  
% 2.80/1.45  %Background operators:
% 2.80/1.45  
% 2.80/1.45  
% 2.80/1.45  %Foreground operators:
% 2.80/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.80/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.80/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.80/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.80/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.80/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.80/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.80/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.80/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.80/1.45  
% 2.80/1.46  tff(f_82, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.80/1.46  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.80/1.46  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.80/1.46  tff(f_77, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.80/1.46  tff(f_75, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.80/1.46  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.80/1.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.80/1.46  tff(c_60, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.80/1.46  tff(c_81, plain, (![A_79, B_80]: (k1_enumset1(A_79, A_79, B_80)=k2_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.80/1.46  tff(c_16, plain, (![E_14, A_8, B_9]: (r2_hidden(E_14, k1_enumset1(A_8, B_9, E_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.46  tff(c_87, plain, (![B_80, A_79]: (r2_hidden(B_80, k2_tarski(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_81, c_16])).
% 2.80/1.46  tff(c_69, plain, (![A_77, B_78]: (k3_tarski(k2_tarski(A_77, B_78))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.80/1.46  tff(c_56, plain, (![A_61, B_62]: (r1_tarski(A_61, k3_tarski(B_62)) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.46  tff(c_747, plain, (![A_194, A_195, B_196]: (r1_tarski(A_194, k2_xboole_0(A_195, B_196)) | ~r2_hidden(A_194, k2_tarski(A_195, B_196)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_56])).
% 2.80/1.46  tff(c_760, plain, (![B_80, A_79]: (r1_tarski(B_80, k2_xboole_0(A_79, B_80)))), inference(resolution, [status(thm)], [c_87, c_747])).
% 2.80/1.46  tff(c_62, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.80/1.46  tff(c_102, plain, (![B_85, A_86]: (B_85=A_86 | ~r1_tarski(B_85, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.80/1.46  tff(c_109, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_62, c_102])).
% 2.80/1.46  tff(c_175, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_109])).
% 2.80/1.46  tff(c_821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_760, c_175])).
% 2.80/1.46  tff(c_822, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_109])).
% 2.80/1.46  tff(c_58, plain, (![A_63, B_64]: (k3_tarski(k2_tarski(A_63, B_64))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.80/1.46  tff(c_18, plain, (![E_14, A_8, C_10]: (r2_hidden(E_14, k1_enumset1(A_8, E_14, C_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.46  tff(c_90, plain, (![A_79, B_80]: (r2_hidden(A_79, k2_tarski(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_81, c_18])).
% 2.80/1.46  tff(c_132, plain, (![C_94, B_95, A_96]: (r2_hidden(C_94, B_95) | ~r2_hidden(C_94, A_96) | ~r1_tarski(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.46  tff(c_151, plain, (![A_97, B_98, B_99]: (r2_hidden(A_97, B_98) | ~r1_tarski(k2_tarski(A_97, B_99), B_98))), inference(resolution, [status(thm)], [c_90, c_132])).
% 2.80/1.46  tff(c_1145, plain, (![A_250, B_251, B_252]: (r2_hidden(A_250, k3_tarski(B_251)) | ~r2_hidden(k2_tarski(A_250, B_252), B_251))), inference(resolution, [status(thm)], [c_56, c_151])).
% 2.80/1.46  tff(c_1157, plain, (![A_250, B_252, B_80]: (r2_hidden(A_250, k3_tarski(k2_tarski(k2_tarski(A_250, B_252), B_80))))), inference(resolution, [status(thm)], [c_90, c_1145])).
% 2.80/1.46  tff(c_1190, plain, (![A_255, B_256, B_257]: (r2_hidden(A_255, k2_xboole_0(k2_tarski(A_255, B_256), B_257)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1157])).
% 2.80/1.46  tff(c_1203, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_822, c_1190])).
% 2.80/1.46  tff(c_1208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1203])).
% 2.80/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.46  
% 2.80/1.46  Inference rules
% 2.80/1.46  ----------------------
% 2.80/1.46  #Ref     : 0
% 2.80/1.46  #Sup     : 253
% 2.80/1.46  #Fact    : 0
% 2.80/1.46  #Define  : 0
% 2.80/1.46  #Split   : 1
% 2.80/1.46  #Chain   : 0
% 2.80/1.46  #Close   : 0
% 2.80/1.46  
% 2.80/1.46  Ordering : KBO
% 2.80/1.46  
% 2.80/1.46  Simplification rules
% 2.80/1.46  ----------------------
% 2.80/1.46  #Subsume      : 20
% 2.80/1.46  #Demod        : 77
% 2.80/1.46  #Tautology    : 123
% 2.80/1.46  #SimpNegUnit  : 1
% 2.80/1.46  #BackRed      : 2
% 2.80/1.46  
% 2.80/1.46  #Partial instantiations: 0
% 2.80/1.46  #Strategies tried      : 1
% 2.80/1.46  
% 3.18/1.46  Timing (in seconds)
% 3.18/1.46  ----------------------
% 3.18/1.47  Preprocessing        : 0.33
% 3.18/1.47  Parsing              : 0.17
% 3.18/1.47  CNF conversion       : 0.02
% 3.18/1.47  Main loop            : 0.38
% 3.18/1.47  Inferencing          : 0.14
% 3.18/1.47  Reduction            : 0.12
% 3.18/1.47  Demodulation         : 0.09
% 3.18/1.47  BG Simplification    : 0.02
% 3.18/1.47  Subsumption          : 0.07
% 3.18/1.47  Abstraction          : 0.02
% 3.18/1.47  MUC search           : 0.00
% 3.18/1.47  Cooper               : 0.00
% 3.18/1.47  Total                : 0.73
% 3.18/1.47  Index Insertion      : 0.00
% 3.18/1.47  Index Deletion       : 0.00
% 3.18/1.47  Index Matching       : 0.00
% 3.18/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
