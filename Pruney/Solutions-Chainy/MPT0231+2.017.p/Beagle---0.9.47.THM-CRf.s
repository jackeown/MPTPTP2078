%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:16 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 207 expanded)
%              Number of leaves         :   18 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 349 expanded)
%              Number of equality atoms :   43 ( 173 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_26,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_96,plain,(
    ! [B_30,A_31] :
      ( k1_tarski(B_30) = A_31
      | k1_xboole_0 = A_31
      | ~ r1_tarski(A_31,k1_tarski(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_108,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_96])).

tff(c_113,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_22,plain,(
    ! [A_12,B_13] : r1_tarski(k1_tarski(A_12),k2_tarski(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_120,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_22])).

tff(c_57,plain,(
    ! [B_24,A_25] :
      ( B_24 = A_25
      | ~ r1_tarski(B_24,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_57])).

tff(c_141,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_72])).

tff(c_24,plain,(
    ! [C_16,A_14,B_15] :
      ( C_16 = A_14
      | B_15 = A_14
      | ~ r1_tarski(k1_tarski(A_14),k2_tarski(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_150,plain,(
    ! [C_16,B_15] :
      ( C_16 = '#skF_1'
      | B_15 = '#skF_1'
      | ~ r1_tarski(k1_xboole_0,k2_tarski(B_15,C_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_24])).

tff(c_160,plain,(
    ! [C_16,B_15] :
      ( C_16 = '#skF_1'
      | B_15 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_150])).

tff(c_173,plain,(
    ! [B_36] : B_36 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_67,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_57])).

tff(c_86,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_114,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_86])).

tff(c_177,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_114])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_141,c_177])).

tff(c_212,plain,(
    ! [C_218] : C_218 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_216,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_114])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_141,c_216])).

tff(c_250,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_262,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_86])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_262])).

tff(c_267,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_274,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_22])).

tff(c_291,plain,(
    ! [B_385,A_386] :
      ( k1_tarski(B_385) = A_386
      | k1_xboole_0 = A_386
      | ~ r1_tarski(A_386,k1_tarski(B_385)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_303,plain,
    ( k1_tarski('#skF_3') = k1_tarski('#skF_1')
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_274,c_291])).

tff(c_308,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_324,plain,(
    ! [C_387,A_388,B_389] :
      ( C_387 = A_388
      | B_389 = A_388
      | ~ r1_tarski(k1_tarski(A_388),k2_tarski(B_389,C_387)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_327,plain,(
    ! [C_387,B_389] :
      ( C_387 = '#skF_1'
      | B_389 = '#skF_1'
      | ~ r1_tarski(k1_xboole_0,k2_tarski(B_389,C_387)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_324])).

tff(c_338,plain,(
    ! [C_387,B_389] :
      ( C_387 = '#skF_1'
      | B_389 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_327])).

tff(c_342,plain,(
    ! [B_390] : B_390 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_373,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_26])).

tff(c_375,plain,(
    ! [C_541] : C_541 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_406,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_26])).

tff(c_407,plain,(
    k1_tarski('#skF_3') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_478,plain,(
    ! [B_695] : r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_3',B_695)) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_22])).

tff(c_481,plain,(
    ! [B_695] :
      ( B_695 = '#skF_1'
      | '#skF_3' = '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_478,c_24])).

tff(c_493,plain,(
    ! [B_696] : B_696 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_481])).

tff(c_537,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:31:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.27  
% 2.12/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.27  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.12/1.27  
% 2.12/1.27  %Foreground sorts:
% 2.12/1.27  
% 2.12/1.27  
% 2.12/1.27  %Background operators:
% 2.12/1.27  
% 2.12/1.27  
% 2.12/1.27  %Foreground operators:
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.27  
% 2.12/1.28  tff(f_61, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.12/1.28  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.12/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.12/1.28  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.12/1.28  tff(f_47, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.12/1.28  tff(f_56, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.12/1.28  tff(c_26, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.28  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.28  tff(c_28, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.28  tff(c_96, plain, (![B_30, A_31]: (k1_tarski(B_30)=A_31 | k1_xboole_0=A_31 | ~r1_tarski(A_31, k1_tarski(B_30)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.12/1.28  tff(c_108, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_96])).
% 2.12/1.28  tff(c_113, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_108])).
% 2.12/1.28  tff(c_22, plain, (![A_12, B_13]: (r1_tarski(k1_tarski(A_12), k2_tarski(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.12/1.28  tff(c_120, plain, (r1_tarski(k1_tarski('#skF_1'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_113, c_22])).
% 2.12/1.28  tff(c_57, plain, (![B_24, A_25]: (B_24=A_25 | ~r1_tarski(B_24, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.28  tff(c_72, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_57])).
% 2.12/1.28  tff(c_141, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_120, c_72])).
% 2.12/1.28  tff(c_24, plain, (![C_16, A_14, B_15]: (C_16=A_14 | B_15=A_14 | ~r1_tarski(k1_tarski(A_14), k2_tarski(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.28  tff(c_150, plain, (![C_16, B_15]: (C_16='#skF_1' | B_15='#skF_1' | ~r1_tarski(k1_xboole_0, k2_tarski(B_15, C_16)))), inference(superposition, [status(thm), theory('equality')], [c_141, c_24])).
% 2.12/1.28  tff(c_160, plain, (![C_16, B_15]: (C_16='#skF_1' | B_15='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_150])).
% 2.12/1.28  tff(c_173, plain, (![B_36]: (B_36='#skF_1')), inference(splitLeft, [status(thm)], [c_160])).
% 2.12/1.28  tff(c_67, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | ~r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_57])).
% 2.12/1.28  tff(c_86, plain, (~r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_67])).
% 2.12/1.28  tff(c_114, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_86])).
% 2.12/1.28  tff(c_177, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_173, c_114])).
% 2.12/1.28  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_141, c_177])).
% 2.12/1.28  tff(c_212, plain, (![C_218]: (C_218='#skF_1')), inference(splitRight, [status(thm)], [c_160])).
% 2.12/1.28  tff(c_216, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_212, c_114])).
% 2.12/1.28  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_141, c_216])).
% 2.12/1.28  tff(c_250, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_108])).
% 2.12/1.28  tff(c_262, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_86])).
% 2.12/1.28  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_262])).
% 2.12/1.28  tff(c_267, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_67])).
% 2.12/1.28  tff(c_274, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_267, c_22])).
% 2.12/1.28  tff(c_291, plain, (![B_385, A_386]: (k1_tarski(B_385)=A_386 | k1_xboole_0=A_386 | ~r1_tarski(A_386, k1_tarski(B_385)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.12/1.28  tff(c_303, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_1') | k1_tarski('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_274, c_291])).
% 2.12/1.28  tff(c_308, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_303])).
% 2.12/1.28  tff(c_324, plain, (![C_387, A_388, B_389]: (C_387=A_388 | B_389=A_388 | ~r1_tarski(k1_tarski(A_388), k2_tarski(B_389, C_387)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.28  tff(c_327, plain, (![C_387, B_389]: (C_387='#skF_1' | B_389='#skF_1' | ~r1_tarski(k1_xboole_0, k2_tarski(B_389, C_387)))), inference(superposition, [status(thm), theory('equality')], [c_308, c_324])).
% 2.12/1.28  tff(c_338, plain, (![C_387, B_389]: (C_387='#skF_1' | B_389='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_327])).
% 2.12/1.28  tff(c_342, plain, (![B_390]: (B_390='#skF_1')), inference(splitLeft, [status(thm)], [c_338])).
% 2.12/1.28  tff(c_373, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_342, c_26])).
% 2.12/1.28  tff(c_375, plain, (![C_541]: (C_541='#skF_1')), inference(splitRight, [status(thm)], [c_338])).
% 2.12/1.28  tff(c_406, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_375, c_26])).
% 2.12/1.28  tff(c_407, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_303])).
% 2.12/1.28  tff(c_478, plain, (![B_695]: (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_3', B_695)))), inference(superposition, [status(thm), theory('equality')], [c_407, c_22])).
% 2.12/1.28  tff(c_481, plain, (![B_695]: (B_695='#skF_1' | '#skF_3'='#skF_1')), inference(resolution, [status(thm)], [c_478, c_24])).
% 2.12/1.28  tff(c_493, plain, (![B_696]: (B_696='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_26, c_481])).
% 2.12/1.28  tff(c_537, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_493, c_26])).
% 2.12/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  
% 2.12/1.28  Inference rules
% 2.12/1.28  ----------------------
% 2.12/1.28  #Ref     : 0
% 2.12/1.28  #Sup     : 153
% 2.12/1.28  #Fact    : 0
% 2.12/1.28  #Define  : 0
% 2.12/1.28  #Split   : 6
% 2.12/1.28  #Chain   : 0
% 2.12/1.28  #Close   : 0
% 2.12/1.28  
% 2.12/1.28  Ordering : KBO
% 2.12/1.28  
% 2.12/1.28  Simplification rules
% 2.12/1.28  ----------------------
% 2.12/1.28  #Subsume      : 24
% 2.12/1.28  #Demod        : 58
% 2.12/1.28  #Tautology    : 58
% 2.12/1.28  #SimpNegUnit  : 1
% 2.12/1.28  #BackRed      : 12
% 2.12/1.28  
% 2.12/1.28  #Partial instantiations: 0
% 2.12/1.28  #Strategies tried      : 1
% 2.12/1.28  
% 2.12/1.28  Timing (in seconds)
% 2.12/1.28  ----------------------
% 2.12/1.28  Preprocessing        : 0.27
% 2.12/1.28  Parsing              : 0.14
% 2.12/1.28  CNF conversion       : 0.02
% 2.12/1.28  Main loop            : 0.25
% 2.12/1.28  Inferencing          : 0.10
% 2.12/1.29  Reduction            : 0.07
% 2.12/1.29  Demodulation         : 0.06
% 2.12/1.29  BG Simplification    : 0.02
% 2.12/1.29  Subsumption          : 0.05
% 2.12/1.29  Abstraction          : 0.01
% 2.12/1.29  MUC search           : 0.00
% 2.12/1.29  Cooper               : 0.00
% 2.12/1.29  Total                : 0.55
% 2.12/1.29  Index Insertion      : 0.00
% 2.12/1.29  Index Deletion       : 0.00
% 2.12/1.29  Index Matching       : 0.00
% 2.12/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
