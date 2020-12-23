%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:31 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 150 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :   64 ( 278 expanded)
%              Number of equality atoms :   36 ( 172 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    ! [B_21] : r1_tarski(k1_tarski(B_21),k1_tarski(B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_208,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(A_52,C_53)
      | ~ r1_tarski(k2_xboole_0(A_52,B_54),C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_231,plain,(
    ! [C_55] :
      ( r1_tarski('#skF_2',C_55)
      | ~ r1_tarski(k1_tarski('#skF_1'),C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_208])).

tff(c_256,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_231])).

tff(c_281,plain,(
    ! [B_58,A_59] :
      ( k1_tarski(B_58) = A_59
      | k1_xboole_0 = A_59
      | ~ r1_tarski(A_59,k1_tarski(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_284,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_256,c_281])).

tff(c_296,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_284])).

tff(c_302,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_256])).

tff(c_157,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,k2_xboole_0(C_48,B_49))
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2593,plain,(
    ! [A_173,C_174,B_175] :
      ( k2_xboole_0(A_173,k2_xboole_0(C_174,B_175)) = k2_xboole_0(C_174,B_175)
      | ~ r1_tarski(A_173,B_175) ) ),
    inference(resolution,[status(thm)],[c_157,c_8])).

tff(c_306,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_42])).

tff(c_481,plain,(
    ! [A_70,B_71,C_72] : k2_xboole_0(k2_xboole_0(A_70,B_71),C_72) = k2_xboole_0(A_70,k2_xboole_0(B_71,C_72)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1340,plain,(
    ! [A_123,B_124] : k2_xboole_0(A_123,k2_xboole_0(B_124,k2_xboole_0(A_123,B_124))) = k2_xboole_0(A_123,B_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_2])).

tff(c_1466,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_2')) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_1340])).

tff(c_1502,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_1466])).

tff(c_2645,plain,
    ( k2_xboole_0('#skF_3','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2593,c_1502])).

tff(c_2807,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_2645])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2969,plain,(
    ! [C_177] :
      ( r1_tarski('#skF_3',C_177)
      | ~ r1_tarski('#skF_2',C_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2807,c_6])).

tff(c_3016,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_302,c_2969])).

tff(c_18,plain,(
    ! [B_21,A_20] :
      ( k1_tarski(B_21) = A_20
      | k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_tarski(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_310,plain,(
    ! [A_20] :
      ( k1_tarski('#skF_1') = A_20
      | k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_18])).

tff(c_333,plain,(
    ! [A_20] :
      ( A_20 = '#skF_2'
      | k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_310])).

tff(c_3022,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3016,c_333])).

tff(c_3029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_40,c_3022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:32:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/2.12  
% 4.88/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/2.12  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.88/2.12  
% 4.88/2.12  %Foreground sorts:
% 4.88/2.12  
% 4.88/2.12  
% 4.88/2.12  %Background operators:
% 4.88/2.12  
% 4.88/2.12  
% 4.88/2.12  %Foreground operators:
% 4.88/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/2.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.88/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.88/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.88/2.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.88/2.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.88/2.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.88/2.12  tff('#skF_2', type, '#skF_2': $i).
% 4.88/2.12  tff('#skF_3', type, '#skF_3': $i).
% 4.88/2.12  tff('#skF_1', type, '#skF_1': $i).
% 4.88/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/2.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.88/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/2.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.88/2.12  
% 4.88/2.13  tff(f_83, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 4.88/2.13  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.88/2.13  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.88/2.13  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.88/2.13  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.88/2.13  tff(f_41, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.88/2.13  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.88/2.13  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.88/2.13  tff(c_40, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.88/2.13  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.88/2.13  tff(c_20, plain, (![B_21]: (r1_tarski(k1_tarski(B_21), k1_tarski(B_21)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.88/2.13  tff(c_42, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.88/2.13  tff(c_208, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, C_53) | ~r1_tarski(k2_xboole_0(A_52, B_54), C_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.88/2.13  tff(c_231, plain, (![C_55]: (r1_tarski('#skF_2', C_55) | ~r1_tarski(k1_tarski('#skF_1'), C_55))), inference(superposition, [status(thm), theory('equality')], [c_42, c_208])).
% 4.88/2.13  tff(c_256, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_231])).
% 4.88/2.13  tff(c_281, plain, (![B_58, A_59]: (k1_tarski(B_58)=A_59 | k1_xboole_0=A_59 | ~r1_tarski(A_59, k1_tarski(B_58)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.88/2.13  tff(c_284, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_256, c_281])).
% 4.88/2.13  tff(c_296, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_38, c_284])).
% 4.88/2.13  tff(c_302, plain, (r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_256])).
% 4.88/2.13  tff(c_157, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, k2_xboole_0(C_48, B_49)) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.88/2.13  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.88/2.13  tff(c_2593, plain, (![A_173, C_174, B_175]: (k2_xboole_0(A_173, k2_xboole_0(C_174, B_175))=k2_xboole_0(C_174, B_175) | ~r1_tarski(A_173, B_175))), inference(resolution, [status(thm)], [c_157, c_8])).
% 4.88/2.13  tff(c_306, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_296, c_42])).
% 4.88/2.13  tff(c_481, plain, (![A_70, B_71, C_72]: (k2_xboole_0(k2_xboole_0(A_70, B_71), C_72)=k2_xboole_0(A_70, k2_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.88/2.13  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.88/2.13  tff(c_1340, plain, (![A_123, B_124]: (k2_xboole_0(A_123, k2_xboole_0(B_124, k2_xboole_0(A_123, B_124)))=k2_xboole_0(A_123, B_124))), inference(superposition, [status(thm), theory('equality')], [c_481, c_2])).
% 4.88/2.13  tff(c_1466, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_306, c_1340])).
% 4.88/2.13  tff(c_1502, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_306, c_1466])).
% 4.88/2.13  tff(c_2645, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2593, c_1502])).
% 4.88/2.13  tff(c_2807, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_302, c_2645])).
% 4.88/2.13  tff(c_6, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.88/2.13  tff(c_2969, plain, (![C_177]: (r1_tarski('#skF_3', C_177) | ~r1_tarski('#skF_2', C_177))), inference(superposition, [status(thm), theory('equality')], [c_2807, c_6])).
% 4.88/2.13  tff(c_3016, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_302, c_2969])).
% 4.88/2.13  tff(c_18, plain, (![B_21, A_20]: (k1_tarski(B_21)=A_20 | k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_tarski(B_21)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.88/2.13  tff(c_310, plain, (![A_20]: (k1_tarski('#skF_1')=A_20 | k1_xboole_0=A_20 | ~r1_tarski(A_20, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_296, c_18])).
% 4.88/2.13  tff(c_333, plain, (![A_20]: (A_20='#skF_2' | k1_xboole_0=A_20 | ~r1_tarski(A_20, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_310])).
% 4.88/2.13  tff(c_3022, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3016, c_333])).
% 4.88/2.13  tff(c_3029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_40, c_3022])).
% 4.88/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/2.13  
% 4.88/2.13  Inference rules
% 4.88/2.13  ----------------------
% 4.88/2.13  #Ref     : 0
% 4.88/2.13  #Sup     : 716
% 4.88/2.13  #Fact    : 0
% 4.88/2.13  #Define  : 0
% 4.88/2.13  #Split   : 1
% 4.88/2.13  #Chain   : 0
% 4.88/2.13  #Close   : 0
% 4.88/2.13  
% 4.88/2.13  Ordering : KBO
% 4.88/2.13  
% 4.88/2.13  Simplification rules
% 4.88/2.13  ----------------------
% 4.88/2.13  #Subsume      : 110
% 4.88/2.13  #Demod        : 452
% 4.88/2.13  #Tautology    : 385
% 4.88/2.13  #SimpNegUnit  : 8
% 4.88/2.13  #BackRed      : 5
% 4.88/2.13  
% 4.88/2.13  #Partial instantiations: 0
% 4.88/2.13  #Strategies tried      : 1
% 4.88/2.13  
% 4.88/2.13  Timing (in seconds)
% 4.88/2.13  ----------------------
% 4.88/2.14  Preprocessing        : 0.41
% 4.88/2.14  Parsing              : 0.21
% 4.88/2.14  CNF conversion       : 0.03
% 4.88/2.14  Main loop            : 0.88
% 4.88/2.14  Inferencing          : 0.30
% 4.88/2.14  Reduction            : 0.34
% 4.88/2.14  Demodulation         : 0.27
% 4.88/2.14  BG Simplification    : 0.04
% 4.88/2.14  Subsumption          : 0.16
% 4.88/2.14  Abstraction          : 0.04
% 4.88/2.14  MUC search           : 0.00
% 4.88/2.14  Cooper               : 0.00
% 4.88/2.14  Total                : 1.33
% 4.88/2.14  Index Insertion      : 0.00
% 4.88/2.14  Index Deletion       : 0.00
% 4.88/2.14  Index Matching       : 0.00
% 4.88/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
