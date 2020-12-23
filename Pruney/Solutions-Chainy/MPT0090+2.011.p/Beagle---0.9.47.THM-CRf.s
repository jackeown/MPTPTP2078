%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:26 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   59 (  85 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 ( 111 expanded)
%              Number of equality atoms :   41 (  61 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_27,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_50,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_27])).

tff(c_24,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_29,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_29])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_59])).

tff(c_94,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | k4_xboole_0(B_29,A_30) != k4_xboole_0(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_94])).

tff(c_1224,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = A_67
      | k3_xboole_0(A_67,B_68) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_100])).

tff(c_20,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_114,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_1302,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1224,c_114])).

tff(c_1378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1302])).

tff(c_1379,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_xboole_0(k4_xboole_0(A_11,B_12),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_37,plain,(
    ! [A_11,B_12] : k3_xboole_0(k4_xboole_0(A_11,B_12),B_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_29])).

tff(c_1387,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1379,c_37])).

tff(c_1397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1387])).

tff(c_1398,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1406,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1398,c_16])).

tff(c_1410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_1406])).

tff(c_1411,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1414,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = k1_xboole_0
      | ~ r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1425,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1411,c_1414])).

tff(c_1450,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = k1_xboole_0
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1458,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_1450])).

tff(c_1485,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | k4_xboole_0(B_81,A_82) != k4_xboole_0(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1488,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1458,c_1485])).

tff(c_2420,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(A_115,B_116) = A_115
      | k3_xboole_0(A_115,B_116) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1488])).

tff(c_1412,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1436,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1412,c_18])).

tff(c_2503,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2420,c_1436])).

tff(c_2563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_2503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.54  
% 3.30/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.54  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.30/1.54  
% 3.30/1.54  %Foreground sorts:
% 3.30/1.54  
% 3.30/1.54  
% 3.30/1.54  %Background operators:
% 3.30/1.54  
% 3.30/1.54  
% 3.30/1.54  %Foreground operators:
% 3.30/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.30/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.30/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.30/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.30/1.54  
% 3.30/1.55  tff(f_48, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.30/1.55  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.30/1.55  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.30/1.55  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.30/1.55  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.30/1.55  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 3.30/1.55  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.30/1.55  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.30/1.55  tff(c_27, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 3.30/1.55  tff(c_50, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.30/1.55  tff(c_58, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_27])).
% 3.30/1.55  tff(c_24, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.30/1.55  tff(c_28, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 3.30/1.55  tff(c_29, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.30/1.55  tff(c_36, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_29])).
% 3.30/1.55  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.30/1.55  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.30/1.55  tff(c_59, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.30/1.55  tff(c_67, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_59])).
% 3.30/1.55  tff(c_94, plain, (![B_29, A_30]: (B_29=A_30 | k4_xboole_0(B_29, A_30)!=k4_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.55  tff(c_100, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=A_7 | k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_67, c_94])).
% 3.30/1.55  tff(c_1224, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=A_67 | k3_xboole_0(A_67, B_68)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_100])).
% 3.30/1.55  tff(c_20, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.30/1.55  tff(c_114, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_20])).
% 3.30/1.55  tff(c_1302, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1224, c_114])).
% 3.30/1.55  tff(c_1378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1302])).
% 3.30/1.55  tff(c_1379, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 3.30/1.55  tff(c_16, plain, (![A_11, B_12]: (r1_xboole_0(k4_xboole_0(A_11, B_12), B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.30/1.55  tff(c_37, plain, (![A_11, B_12]: (k3_xboole_0(k4_xboole_0(A_11, B_12), B_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_29])).
% 3.30/1.55  tff(c_1387, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1379, c_37])).
% 3.30/1.55  tff(c_1397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1387])).
% 3.30/1.55  tff(c_1398, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 3.30/1.55  tff(c_1406, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1398, c_16])).
% 3.30/1.55  tff(c_1410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27, c_1406])).
% 3.30/1.55  tff(c_1411, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 3.30/1.55  tff(c_1414, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=k1_xboole_0 | ~r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.30/1.55  tff(c_1425, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1411, c_1414])).
% 3.30/1.55  tff(c_1450, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=k1_xboole_0 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.30/1.55  tff(c_1458, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_1450])).
% 3.30/1.55  tff(c_1485, plain, (![B_81, A_82]: (B_81=A_82 | k4_xboole_0(B_81, A_82)!=k4_xboole_0(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.55  tff(c_1488, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=A_7 | k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1458, c_1485])).
% 3.30/1.55  tff(c_2420, plain, (![A_115, B_116]: (k4_xboole_0(A_115, B_116)=A_115 | k3_xboole_0(A_115, B_116)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1488])).
% 3.30/1.55  tff(c_1412, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 3.30/1.55  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.30/1.55  tff(c_1436, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1412, c_18])).
% 3.30/1.55  tff(c_2503, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2420, c_1436])).
% 3.30/1.55  tff(c_2563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1425, c_2503])).
% 3.30/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.55  
% 3.30/1.55  Inference rules
% 3.30/1.55  ----------------------
% 3.30/1.55  #Ref     : 2
% 3.30/1.55  #Sup     : 686
% 3.30/1.55  #Fact    : 0
% 3.30/1.55  #Define  : 0
% 3.30/1.55  #Split   : 7
% 3.30/1.55  #Chain   : 0
% 3.30/1.55  #Close   : 0
% 3.30/1.55  
% 3.30/1.55  Ordering : KBO
% 3.30/1.55  
% 3.30/1.55  Simplification rules
% 3.30/1.55  ----------------------
% 3.30/1.55  #Subsume      : 5
% 3.30/1.55  #Demod        : 562
% 3.30/1.55  #Tautology    : 481
% 3.30/1.55  #SimpNegUnit  : 2
% 3.30/1.55  #BackRed      : 0
% 3.30/1.55  
% 3.30/1.55  #Partial instantiations: 0
% 3.30/1.55  #Strategies tried      : 1
% 3.30/1.55  
% 3.30/1.55  Timing (in seconds)
% 3.30/1.55  ----------------------
% 3.30/1.55  Preprocessing        : 0.27
% 3.30/1.55  Parsing              : 0.15
% 3.30/1.55  CNF conversion       : 0.02
% 3.30/1.55  Main loop            : 0.53
% 3.30/1.55  Inferencing          : 0.19
% 3.30/1.55  Reduction            : 0.20
% 3.30/1.55  Demodulation         : 0.15
% 3.30/1.55  BG Simplification    : 0.02
% 3.30/1.55  Subsumption          : 0.07
% 3.30/1.55  Abstraction          : 0.03
% 3.30/1.55  MUC search           : 0.00
% 3.30/1.55  Cooper               : 0.00
% 3.30/1.55  Total                : 0.83
% 3.30/1.55  Index Insertion      : 0.00
% 3.30/1.56  Index Deletion       : 0.00
% 3.30/1.56  Index Matching       : 0.00
% 3.30/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
