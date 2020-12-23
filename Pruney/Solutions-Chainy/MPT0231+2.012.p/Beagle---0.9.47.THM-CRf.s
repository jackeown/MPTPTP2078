%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:16 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 196 expanded)
%              Number of leaves         :   20 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 ( 319 expanded)
%              Number of equality atoms :   50 ( 200 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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

tff(c_24,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_86,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_30] : k3_xboole_0(k1_xboole_0,A_30) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    ! [A_30] : k3_xboole_0(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_2])).

tff(c_26,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_176,plain,(
    ! [B_32,A_33] :
      ( k1_tarski(B_32) = A_33
      | k1_xboole_0 = A_33
      | ~ r1_tarski(A_33,k1_tarski(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_187,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_176])).

tff(c_223,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(k1_tarski(A_14),k2_tarski(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_99,plain,(
    ! [A_14,B_15] : k3_xboole_0(k1_tarski(A_14),k2_tarski(A_14,B_15)) = k1_tarski(A_14) ),
    inference(resolution,[status(thm)],[c_20,c_86])).

tff(c_231,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_99])).

tff(c_237,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_231])).

tff(c_280,plain,(
    ! [C_41,A_42,B_43] :
      ( C_41 = A_42
      | B_43 = A_42
      | ~ r1_tarski(k1_tarski(A_42),k2_tarski(B_43,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_283,plain,(
    ! [C_41,B_43] :
      ( C_41 = '#skF_1'
      | B_43 = '#skF_1'
      | ~ r1_tarski(k1_xboole_0,k2_tarski(B_43,C_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_280])).

tff(c_294,plain,(
    ! [C_41,B_43] :
      ( C_41 = '#skF_1'
      | B_43 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_283])).

tff(c_298,plain,(
    ! [B_44] : B_44 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_356,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_24])).

tff(c_358,plain,(
    ! [C_308] : C_308 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_416,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_24])).

tff(c_417,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_430,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_20])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k1_tarski(B_13) = A_12
      | k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_tarski(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_440,plain,
    ( k1_tarski('#skF_3') = k1_tarski('#skF_1')
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_430,c_14])).

tff(c_459,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_440])).

tff(c_22,plain,(
    ! [C_18,A_16,B_17] :
      ( C_18 = A_16
      | B_17 = A_16
      | ~ r1_tarski(k1_tarski(A_16),k2_tarski(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_467,plain,(
    ! [C_18,B_17] :
      ( C_18 = '#skF_1'
      | B_17 = '#skF_1'
      | ~ r1_tarski(k1_xboole_0,k2_tarski(B_17,C_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_22])).

tff(c_492,plain,(
    ! [C_18,B_17] :
      ( C_18 = '#skF_1'
      | B_17 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_467])).

tff(c_503,plain,(
    ! [B_552] : B_552 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_492])).

tff(c_418,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_419,plain,(
    k1_tarski('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_418])).

tff(c_511,plain,(
    k1_tarski('#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_419])).

tff(c_564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_511])).

tff(c_566,plain,(
    ! [C_793] : C_793 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_492])).

tff(c_574,plain,(
    k1_tarski('#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_419])).

tff(c_627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_574])).

tff(c_628,plain,(
    k1_tarski('#skF_3') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_697,plain,(
    ! [B_1036] : r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_3',B_1036)) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_20])).

tff(c_700,plain,(
    ! [B_1036] :
      ( B_1036 = '#skF_1'
      | '#skF_3' = '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_697,c_22])).

tff(c_713,plain,(
    ! [B_1037] : B_1037 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_700])).

tff(c_787,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.31  
% 2.14/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.32  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.14/1.32  
% 2.14/1.32  %Foreground sorts:
% 2.14/1.32  
% 2.14/1.32  
% 2.14/1.32  %Background operators:
% 2.14/1.32  
% 2.14/1.32  
% 2.14/1.32  %Foreground operators:
% 2.14/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.32  
% 2.14/1.33  tff(f_61, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.14/1.33  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.14/1.33  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.14/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.14/1.33  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.14/1.33  tff(f_47, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.14/1.33  tff(f_56, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.14/1.33  tff(c_24, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.33  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.33  tff(c_86, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.33  tff(c_119, plain, (![A_30]: (k3_xboole_0(k1_xboole_0, A_30)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_86])).
% 2.14/1.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.14/1.33  tff(c_124, plain, (![A_30]: (k3_xboole_0(A_30, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_119, c_2])).
% 2.14/1.33  tff(c_26, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.33  tff(c_176, plain, (![B_32, A_33]: (k1_tarski(B_32)=A_33 | k1_xboole_0=A_33 | ~r1_tarski(A_33, k1_tarski(B_32)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.33  tff(c_187, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_176])).
% 2.14/1.33  tff(c_223, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_187])).
% 2.14/1.33  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), k2_tarski(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.14/1.33  tff(c_99, plain, (![A_14, B_15]: (k3_xboole_0(k1_tarski(A_14), k2_tarski(A_14, B_15))=k1_tarski(A_14))), inference(resolution, [status(thm)], [c_20, c_86])).
% 2.14/1.33  tff(c_231, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_223, c_99])).
% 2.14/1.33  tff(c_237, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_124, c_231])).
% 2.14/1.33  tff(c_280, plain, (![C_41, A_42, B_43]: (C_41=A_42 | B_43=A_42 | ~r1_tarski(k1_tarski(A_42), k2_tarski(B_43, C_41)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.33  tff(c_283, plain, (![C_41, B_43]: (C_41='#skF_1' | B_43='#skF_1' | ~r1_tarski(k1_xboole_0, k2_tarski(B_43, C_41)))), inference(superposition, [status(thm), theory('equality')], [c_237, c_280])).
% 2.14/1.33  tff(c_294, plain, (![C_41, B_43]: (C_41='#skF_1' | B_43='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_283])).
% 2.14/1.33  tff(c_298, plain, (![B_44]: (B_44='#skF_1')), inference(splitLeft, [status(thm)], [c_294])).
% 2.14/1.33  tff(c_356, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_298, c_24])).
% 2.14/1.33  tff(c_358, plain, (![C_308]: (C_308='#skF_1')), inference(splitRight, [status(thm)], [c_294])).
% 2.14/1.33  tff(c_416, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_358, c_24])).
% 2.14/1.33  tff(c_417, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_187])).
% 2.14/1.33  tff(c_430, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_417, c_20])).
% 2.14/1.33  tff(c_14, plain, (![B_13, A_12]: (k1_tarski(B_13)=A_12 | k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_tarski(B_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.33  tff(c_440, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_1') | k1_tarski('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_430, c_14])).
% 2.14/1.33  tff(c_459, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_440])).
% 2.14/1.33  tff(c_22, plain, (![C_18, A_16, B_17]: (C_18=A_16 | B_17=A_16 | ~r1_tarski(k1_tarski(A_16), k2_tarski(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.33  tff(c_467, plain, (![C_18, B_17]: (C_18='#skF_1' | B_17='#skF_1' | ~r1_tarski(k1_xboole_0, k2_tarski(B_17, C_18)))), inference(superposition, [status(thm), theory('equality')], [c_459, c_22])).
% 2.14/1.33  tff(c_492, plain, (![C_18, B_17]: (C_18='#skF_1' | B_17='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_467])).
% 2.14/1.33  tff(c_503, plain, (![B_552]: (B_552='#skF_1')), inference(splitLeft, [status(thm)], [c_492])).
% 2.14/1.33  tff(c_418, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_187])).
% 2.14/1.33  tff(c_419, plain, (k1_tarski('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_417, c_418])).
% 2.14/1.33  tff(c_511, plain, (k1_tarski('#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_503, c_419])).
% 2.14/1.33  tff(c_564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_459, c_511])).
% 2.14/1.33  tff(c_566, plain, (![C_793]: (C_793='#skF_1')), inference(splitRight, [status(thm)], [c_492])).
% 2.14/1.33  tff(c_574, plain, (k1_tarski('#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_566, c_419])).
% 2.14/1.33  tff(c_627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_459, c_574])).
% 2.14/1.33  tff(c_628, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_440])).
% 2.14/1.33  tff(c_697, plain, (![B_1036]: (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_3', B_1036)))), inference(superposition, [status(thm), theory('equality')], [c_628, c_20])).
% 2.14/1.33  tff(c_700, plain, (![B_1036]: (B_1036='#skF_1' | '#skF_3'='#skF_1')), inference(resolution, [status(thm)], [c_697, c_22])).
% 2.14/1.33  tff(c_713, plain, (![B_1037]: (B_1037='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_24, c_700])).
% 2.14/1.33  tff(c_787, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_713, c_24])).
% 2.14/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.33  
% 2.14/1.33  Inference rules
% 2.14/1.33  ----------------------
% 2.14/1.33  #Ref     : 0
% 2.14/1.33  #Sup     : 256
% 2.14/1.33  #Fact    : 0
% 2.14/1.33  #Define  : 0
% 2.14/1.33  #Split   : 4
% 2.14/1.33  #Chain   : 0
% 2.14/1.33  #Close   : 0
% 2.14/1.33  
% 2.14/1.33  Ordering : KBO
% 2.14/1.33  
% 2.14/1.33  Simplification rules
% 2.14/1.33  ----------------------
% 2.14/1.33  #Subsume      : 37
% 2.14/1.33  #Demod        : 87
% 2.14/1.33  #Tautology    : 90
% 2.14/1.33  #SimpNegUnit  : 1
% 2.14/1.33  #BackRed      : 11
% 2.14/1.33  
% 2.14/1.33  #Partial instantiations: 0
% 2.14/1.33  #Strategies tried      : 1
% 2.14/1.33  
% 2.14/1.33  Timing (in seconds)
% 2.14/1.33  ----------------------
% 2.56/1.33  Preprocessing        : 0.28
% 2.56/1.33  Parsing              : 0.15
% 2.56/1.33  CNF conversion       : 0.02
% 2.56/1.33  Main loop            : 0.29
% 2.56/1.33  Inferencing          : 0.12
% 2.56/1.33  Reduction            : 0.09
% 2.56/1.33  Demodulation         : 0.07
% 2.56/1.33  BG Simplification    : 0.02
% 2.56/1.33  Subsumption          : 0.04
% 2.56/1.33  Abstraction          : 0.01
% 2.56/1.33  MUC search           : 0.00
% 2.56/1.33  Cooper               : 0.00
% 2.56/1.33  Total                : 0.60
% 2.56/1.33  Index Insertion      : 0.00
% 2.56/1.33  Index Deletion       : 0.00
% 2.56/1.33  Index Matching       : 0.00
% 2.56/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
