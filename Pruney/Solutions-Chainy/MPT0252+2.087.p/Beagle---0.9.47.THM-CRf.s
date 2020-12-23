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
% DateTime   : Thu Dec  3 09:51:11 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   55 (  75 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  98 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_63,axiom,(
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

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_58,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_67,plain,(
    ! [A_65,B_66] : k1_enumset1(A_65,A_65,B_66) = k2_tarski(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_73,plain,(
    ! [B_66,A_65] : r2_hidden(B_66,k2_tarski(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_18])).

tff(c_56,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_97,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,k3_tarski(B_74))
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_772,plain,(
    ! [A_181,A_182,B_183] :
      ( r1_tarski(A_181,k2_xboole_0(A_182,B_183))
      | ~ r2_hidden(A_181,k2_tarski(A_182,B_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_97])).

tff(c_785,plain,(
    ! [B_66,A_65] : r1_tarski(B_66,k2_xboole_0(A_65,B_66)) ),
    inference(resolution,[status(thm)],[c_73,c_772])).

tff(c_60,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_232,plain,(
    ! [A_85,B_86] :
      ( r2_xboole_0(A_85,B_86)
      | B_86 = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ r2_xboole_0(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_249,plain,(
    ! [B_87,A_88] :
      ( ~ r1_tarski(B_87,A_88)
      | B_87 = A_88
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(resolution,[status(thm)],[c_232,c_14])).

tff(c_261,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_60,c_249])).

tff(c_338,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_338])).

tff(c_820,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_20,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_76,plain,(
    ! [A_65,B_66] : r2_hidden(A_65,k2_tarski(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_20])).

tff(c_54,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,k3_tarski(B_48))
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_262,plain,(
    ! [C_89,B_90,A_91] :
      ( r2_hidden(C_89,B_90)
      | ~ r2_hidden(C_89,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_290,plain,(
    ! [A_95,B_96,B_97] :
      ( r2_hidden(A_95,B_96)
      | ~ r1_tarski(k2_tarski(A_95,B_97),B_96) ) ),
    inference(resolution,[status(thm)],[c_76,c_262])).

tff(c_886,plain,(
    ! [A_198,B_199,B_200] :
      ( r2_hidden(A_198,k3_tarski(B_199))
      | ~ r2_hidden(k2_tarski(A_198,B_200),B_199) ) ),
    inference(resolution,[status(thm)],[c_54,c_290])).

tff(c_890,plain,(
    ! [A_198,B_200,B_66] : r2_hidden(A_198,k3_tarski(k2_tarski(k2_tarski(A_198,B_200),B_66))) ),
    inference(resolution,[status(thm)],[c_76,c_886])).

tff(c_914,plain,(
    ! [A_201,B_202,B_203] : r2_hidden(A_201,k2_xboole_0(k2_tarski(A_201,B_202),B_203)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_890])).

tff(c_923,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_914])).

tff(c_927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_923])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.08/0.27  % Computer   : n010.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % DateTime   : Tue Dec  1 18:00:59 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.11/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.35  
% 2.72/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.35  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.72/1.35  
% 2.72/1.35  %Foreground sorts:
% 2.72/1.35  
% 2.72/1.35  
% 2.72/1.35  %Background operators:
% 2.72/1.35  
% 2.72/1.35  
% 2.72/1.35  %Foreground operators:
% 2.72/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.72/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.72/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.72/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.35  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.72/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.72/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.72/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.72/1.35  
% 2.72/1.36  tff(f_84, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.72/1.36  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.72/1.36  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.72/1.36  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.72/1.36  tff(f_77, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.72/1.36  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.72/1.36  tff(f_44, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.72/1.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.72/1.36  tff(c_58, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.72/1.36  tff(c_67, plain, (![A_65, B_66]: (k1_enumset1(A_65, A_65, B_66)=k2_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.72/1.36  tff(c_18, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.72/1.36  tff(c_73, plain, (![B_66, A_65]: (r2_hidden(B_66, k2_tarski(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_18])).
% 2.72/1.36  tff(c_56, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.72/1.36  tff(c_97, plain, (![A_73, B_74]: (r1_tarski(A_73, k3_tarski(B_74)) | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.36  tff(c_772, plain, (![A_181, A_182, B_183]: (r1_tarski(A_181, k2_xboole_0(A_182, B_183)) | ~r2_hidden(A_181, k2_tarski(A_182, B_183)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_97])).
% 2.72/1.36  tff(c_785, plain, (![B_66, A_65]: (r1_tarski(B_66, k2_xboole_0(A_65, B_66)))), inference(resolution, [status(thm)], [c_73, c_772])).
% 2.72/1.36  tff(c_60, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.72/1.36  tff(c_232, plain, (![A_85, B_86]: (r2_xboole_0(A_85, B_86) | B_86=A_85 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.36  tff(c_14, plain, (![B_9, A_8]: (~r2_xboole_0(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.72/1.36  tff(c_249, plain, (![B_87, A_88]: (~r1_tarski(B_87, A_88) | B_87=A_88 | ~r1_tarski(A_88, B_87))), inference(resolution, [status(thm)], [c_232, c_14])).
% 2.72/1.36  tff(c_261, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_249])).
% 2.72/1.36  tff(c_338, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_261])).
% 2.72/1.36  tff(c_819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_785, c_338])).
% 2.72/1.36  tff(c_820, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_261])).
% 2.72/1.36  tff(c_20, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.72/1.36  tff(c_76, plain, (![A_65, B_66]: (r2_hidden(A_65, k2_tarski(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_20])).
% 2.72/1.36  tff(c_54, plain, (![A_47, B_48]: (r1_tarski(A_47, k3_tarski(B_48)) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.36  tff(c_262, plain, (![C_89, B_90, A_91]: (r2_hidden(C_89, B_90) | ~r2_hidden(C_89, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.36  tff(c_290, plain, (![A_95, B_96, B_97]: (r2_hidden(A_95, B_96) | ~r1_tarski(k2_tarski(A_95, B_97), B_96))), inference(resolution, [status(thm)], [c_76, c_262])).
% 2.72/1.36  tff(c_886, plain, (![A_198, B_199, B_200]: (r2_hidden(A_198, k3_tarski(B_199)) | ~r2_hidden(k2_tarski(A_198, B_200), B_199))), inference(resolution, [status(thm)], [c_54, c_290])).
% 2.72/1.36  tff(c_890, plain, (![A_198, B_200, B_66]: (r2_hidden(A_198, k3_tarski(k2_tarski(k2_tarski(A_198, B_200), B_66))))), inference(resolution, [status(thm)], [c_76, c_886])).
% 2.72/1.36  tff(c_914, plain, (![A_201, B_202, B_203]: (r2_hidden(A_201, k2_xboole_0(k2_tarski(A_201, B_202), B_203)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_890])).
% 2.72/1.36  tff(c_923, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_820, c_914])).
% 2.72/1.36  tff(c_927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_923])).
% 2.72/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.36  
% 2.72/1.36  Inference rules
% 2.72/1.36  ----------------------
% 2.72/1.36  #Ref     : 0
% 2.72/1.36  #Sup     : 187
% 2.72/1.36  #Fact    : 0
% 2.72/1.36  #Define  : 0
% 2.72/1.36  #Split   : 1
% 2.72/1.36  #Chain   : 0
% 2.72/1.36  #Close   : 0
% 2.72/1.36  
% 2.72/1.36  Ordering : KBO
% 2.72/1.36  
% 2.72/1.36  Simplification rules
% 2.72/1.36  ----------------------
% 2.72/1.36  #Subsume      : 20
% 2.72/1.36  #Demod        : 75
% 2.72/1.36  #Tautology    : 88
% 2.72/1.36  #SimpNegUnit  : 1
% 2.72/1.36  #BackRed      : 2
% 2.72/1.36  
% 2.72/1.36  #Partial instantiations: 0
% 2.72/1.36  #Strategies tried      : 1
% 2.72/1.36  
% 2.72/1.36  Timing (in seconds)
% 2.72/1.36  ----------------------
% 2.72/1.37  Preprocessing        : 0.32
% 2.72/1.37  Parsing              : 0.17
% 2.72/1.37  CNF conversion       : 0.02
% 2.72/1.37  Main loop            : 0.33
% 2.72/1.37  Inferencing          : 0.12
% 2.72/1.37  Reduction            : 0.11
% 2.72/1.37  Demodulation         : 0.09
% 2.72/1.37  BG Simplification    : 0.02
% 2.72/1.37  Subsumption          : 0.07
% 2.72/1.37  Abstraction          : 0.02
% 2.72/1.37  MUC search           : 0.00
% 2.72/1.37  Cooper               : 0.00
% 2.72/1.37  Total                : 0.69
% 2.72/1.37  Index Insertion      : 0.00
% 2.72/1.37  Index Deletion       : 0.00
% 2.72/1.37  Index Matching       : 0.00
% 2.72/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
