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
% DateTime   : Thu Dec  3 09:44:25 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   52 (  73 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  83 expanded)
%              Number of equality atoms :   28 (  44 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_20,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_33,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_18,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_140,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_22,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_125,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_127,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_125,c_127])).

tff(c_152,plain,(
    ! [A_24,B_25] : k2_xboole_0(k3_xboole_0(A_24,B_25),k4_xboole_0(A_24,B_25)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_164,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_152])).

tff(c_34,plain,(
    ! [B_15,A_16] : k2_xboole_0(B_15,A_16) = k2_xboole_0(A_16,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [A_16] : k2_xboole_0(k1_xboole_0,A_16) = A_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_8])).

tff(c_170,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_50])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_170])).

tff(c_178,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_183,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_14])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_183])).

tff(c_188,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_197,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_14])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_197])).

tff(c_203,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_16,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_290,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_16])).

tff(c_202,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_294,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_309,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_202,c_294])).

tff(c_387,plain,(
    ! [A_39,B_40] : k2_xboole_0(k3_xboole_0(A_39,B_40),k4_xboole_0(A_39,B_40)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_408,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_387])).

tff(c_204,plain,(
    ! [B_26,A_27] : k2_xboole_0(B_26,A_27) = k2_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_220,plain,(
    ! [A_27] : k2_xboole_0(k1_xboole_0,A_27) = A_27 ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_8])).

tff(c_417,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_220])).

tff(c_424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:47:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.33  
% 2.08/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.33  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.08/1.33  
% 2.08/1.33  %Foreground sorts:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Background operators:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Foreground operators:
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.33  
% 2.08/1.34  tff(f_44, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.08/1.34  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.08/1.34  tff(f_37, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.08/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.08/1.34  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.08/1.34  tff(f_39, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.08/1.34  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.34  tff(c_33, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_20])).
% 2.08/1.34  tff(c_18, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.34  tff(c_140, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_18])).
% 2.08/1.34  tff(c_22, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.34  tff(c_125, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_22])).
% 2.08/1.34  tff(c_127, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.34  tff(c_137, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_125, c_127])).
% 2.08/1.34  tff(c_152, plain, (![A_24, B_25]: (k2_xboole_0(k3_xboole_0(A_24, B_25), k4_xboole_0(A_24, B_25))=A_24)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.34  tff(c_164, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_137, c_152])).
% 2.08/1.34  tff(c_34, plain, (![B_15, A_16]: (k2_xboole_0(B_15, A_16)=k2_xboole_0(A_16, B_15))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.34  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.34  tff(c_50, plain, (![A_16]: (k2_xboole_0(k1_xboole_0, A_16)=A_16)), inference(superposition, [status(thm), theory('equality')], [c_34, c_8])).
% 2.08/1.34  tff(c_170, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_164, c_50])).
% 2.08/1.34  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_170])).
% 2.08/1.34  tff(c_178, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_18])).
% 2.08/1.34  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.34  tff(c_183, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_178, c_14])).
% 2.08/1.34  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_183])).
% 2.08/1.34  tff(c_188, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_22])).
% 2.08/1.34  tff(c_197, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_188, c_14])).
% 2.08/1.34  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_197])).
% 2.08/1.34  tff(c_203, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_20])).
% 2.08/1.34  tff(c_16, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.34  tff(c_290, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_16])).
% 2.08/1.34  tff(c_202, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_20])).
% 2.08/1.34  tff(c_294, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.34  tff(c_309, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_202, c_294])).
% 2.08/1.34  tff(c_387, plain, (![A_39, B_40]: (k2_xboole_0(k3_xboole_0(A_39, B_40), k4_xboole_0(A_39, B_40))=A_39)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.34  tff(c_408, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_309, c_387])).
% 2.08/1.34  tff(c_204, plain, (![B_26, A_27]: (k2_xboole_0(B_26, A_27)=k2_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.34  tff(c_220, plain, (![A_27]: (k2_xboole_0(k1_xboole_0, A_27)=A_27)), inference(superposition, [status(thm), theory('equality')], [c_204, c_8])).
% 2.08/1.34  tff(c_417, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_408, c_220])).
% 2.08/1.34  tff(c_424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_290, c_417])).
% 2.08/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.34  
% 2.08/1.34  Inference rules
% 2.08/1.34  ----------------------
% 2.08/1.34  #Ref     : 0
% 2.08/1.34  #Sup     : 106
% 2.08/1.34  #Fact    : 0
% 2.08/1.34  #Define  : 0
% 2.08/1.34  #Split   : 3
% 2.08/1.34  #Chain   : 0
% 2.08/1.34  #Close   : 0
% 2.08/1.34  
% 2.08/1.34  Ordering : KBO
% 2.08/1.35  
% 2.08/1.35  Simplification rules
% 2.08/1.35  ----------------------
% 2.08/1.35  #Subsume      : 2
% 2.08/1.35  #Demod        : 16
% 2.08/1.35  #Tautology    : 67
% 2.08/1.35  #SimpNegUnit  : 4
% 2.08/1.35  #BackRed      : 0
% 2.08/1.35  
% 2.08/1.35  #Partial instantiations: 0
% 2.08/1.35  #Strategies tried      : 1
% 2.08/1.35  
% 2.08/1.35  Timing (in seconds)
% 2.08/1.35  ----------------------
% 2.08/1.35  Preprocessing        : 0.25
% 2.08/1.35  Parsing              : 0.13
% 2.08/1.35  CNF conversion       : 0.02
% 2.08/1.35  Main loop            : 0.27
% 2.08/1.35  Inferencing          : 0.10
% 2.08/1.35  Reduction            : 0.09
% 2.08/1.35  Demodulation         : 0.07
% 2.08/1.35  BG Simplification    : 0.01
% 2.08/1.35  Subsumption          : 0.04
% 2.08/1.35  Abstraction          : 0.01
% 2.08/1.35  MUC search           : 0.00
% 2.08/1.35  Cooper               : 0.00
% 2.08/1.35  Total                : 0.55
% 2.08/1.35  Index Insertion      : 0.00
% 2.08/1.35  Index Deletion       : 0.00
% 2.08/1.35  Index Matching       : 0.00
% 2.08/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
