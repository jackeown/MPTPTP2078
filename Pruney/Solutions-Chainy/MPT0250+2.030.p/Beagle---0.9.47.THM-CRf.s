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
% DateTime   : Thu Dec  3 09:50:36 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   55 (  68 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  69 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_60,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_38,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_34,plain,(
    ! [B_28] : k4_xboole_0(k1_tarski(B_28),k1_tarski(B_28)) != k1_tarski(B_28) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_194,plain,(
    ! [B_28] : k1_tarski(B_28) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_34])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(k1_tarski(A_23),B_24)
      | r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_196,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = A_52
      | ~ r1_xboole_0(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_491,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(k1_tarski(A_81),B_82) = k1_tarski(A_81)
      | r2_hidden(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_30,c_196])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_123,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_206,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(B_57,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_123])).

tff(c_32,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_212,plain,(
    ! [B_57,A_56] : k2_xboole_0(B_57,A_56) = k2_xboole_0(A_56,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_32])).

tff(c_40,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_233,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_317,plain,
    ( k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_233,c_2])).

tff(c_323,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_317])).

tff(c_234,plain,(
    ! [B_58,A_59] : k2_xboole_0(B_58,A_59) = k2_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_32])).

tff(c_255,plain,(
    ! [A_59,B_58] : r1_tarski(A_59,k2_xboole_0(B_58,A_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_14])).

tff(c_330,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_255])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_348,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_330,c_10])).

tff(c_505,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_348])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_194,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.38  
% 2.41/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.41/1.38  
% 2.41/1.38  %Foreground sorts:
% 2.41/1.38  
% 2.41/1.38  
% 2.41/1.38  %Background operators:
% 2.41/1.38  
% 2.41/1.38  
% 2.41/1.38  %Foreground operators:
% 2.41/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.41/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.41/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.41/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.41/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.41/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.41/1.38  
% 2.41/1.39  tff(f_70, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.41/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.41/1.39  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.41/1.39  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.41/1.39  tff(f_58, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.41/1.39  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.41/1.39  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.41/1.39  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.41/1.39  tff(f_60, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.41/1.39  tff(c_38, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.41/1.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.39  tff(c_87, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.41/1.39  tff(c_99, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_87])).
% 2.41/1.39  tff(c_34, plain, (![B_28]: (k4_xboole_0(k1_tarski(B_28), k1_tarski(B_28))!=k1_tarski(B_28))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.41/1.39  tff(c_194, plain, (![B_28]: (k1_tarski(B_28)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_99, c_34])).
% 2.41/1.39  tff(c_30, plain, (![A_23, B_24]: (r1_xboole_0(k1_tarski(A_23), B_24) | r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.41/1.39  tff(c_196, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=A_52 | ~r1_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.41/1.39  tff(c_491, plain, (![A_81, B_82]: (k4_xboole_0(k1_tarski(A_81), B_82)=k1_tarski(A_81) | r2_hidden(A_81, B_82))), inference(resolution, [status(thm)], [c_30, c_196])).
% 2.41/1.39  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.41/1.39  tff(c_20, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.41/1.39  tff(c_123, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.41/1.39  tff(c_206, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(B_57, A_56))), inference(superposition, [status(thm), theory('equality')], [c_20, c_123])).
% 2.41/1.39  tff(c_32, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.41/1.39  tff(c_212, plain, (![B_57, A_56]: (k2_xboole_0(B_57, A_56)=k2_xboole_0(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_206, c_32])).
% 2.41/1.39  tff(c_40, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.41/1.39  tff(c_233, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_40])).
% 2.41/1.39  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.39  tff(c_317, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_233, c_2])).
% 2.41/1.39  tff(c_323, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_317])).
% 2.41/1.39  tff(c_234, plain, (![B_58, A_59]: (k2_xboole_0(B_58, A_59)=k2_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_206, c_32])).
% 2.41/1.39  tff(c_255, plain, (![A_59, B_58]: (r1_tarski(A_59, k2_xboole_0(B_58, A_59)))), inference(superposition, [status(thm), theory('equality')], [c_234, c_14])).
% 2.41/1.39  tff(c_330, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_323, c_255])).
% 2.41/1.39  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.41/1.39  tff(c_348, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_330, c_10])).
% 2.41/1.39  tff(c_505, plain, (k1_tarski('#skF_1')=k1_xboole_0 | r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_491, c_348])).
% 2.41/1.39  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_194, c_505])).
% 2.41/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.39  
% 2.41/1.39  Inference rules
% 2.41/1.39  ----------------------
% 2.41/1.39  #Ref     : 0
% 2.41/1.39  #Sup     : 123
% 2.41/1.39  #Fact    : 0
% 2.41/1.39  #Define  : 0
% 2.41/1.39  #Split   : 1
% 2.41/1.39  #Chain   : 0
% 2.41/1.39  #Close   : 0
% 2.41/1.39  
% 2.41/1.39  Ordering : KBO
% 2.41/1.39  
% 2.41/1.39  Simplification rules
% 2.41/1.39  ----------------------
% 2.41/1.39  #Subsume      : 3
% 2.41/1.39  #Demod        : 33
% 2.41/1.39  #Tautology    : 83
% 2.41/1.39  #SimpNegUnit  : 4
% 2.41/1.39  #BackRed      : 3
% 2.41/1.39  
% 2.41/1.39  #Partial instantiations: 0
% 2.41/1.39  #Strategies tried      : 1
% 2.41/1.39  
% 2.41/1.39  Timing (in seconds)
% 2.41/1.39  ----------------------
% 2.41/1.39  Preprocessing        : 0.31
% 2.41/1.39  Parsing              : 0.17
% 2.41/1.39  CNF conversion       : 0.02
% 2.41/1.39  Main loop            : 0.25
% 2.41/1.39  Inferencing          : 0.09
% 2.41/1.39  Reduction            : 0.09
% 2.41/1.39  Demodulation         : 0.07
% 2.41/1.39  BG Simplification    : 0.01
% 2.41/1.39  Subsumption          : 0.04
% 2.41/1.39  Abstraction          : 0.02
% 2.41/1.39  MUC search           : 0.00
% 2.41/1.39  Cooper               : 0.00
% 2.41/1.39  Total                : 0.59
% 2.41/1.40  Index Insertion      : 0.00
% 2.41/1.40  Index Deletion       : 0.00
% 2.41/1.40  Index Matching       : 0.00
% 2.41/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
