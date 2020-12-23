%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:26 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   61 (  94 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 ( 111 expanded)
%              Number of equality atoms :   40 (  70 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_14,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_343,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_241,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(A_28,B_29)
      | k3_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_37,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_249,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_241,c_37])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_256,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_274,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_256])).

tff(c_277,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_274])).

tff(c_130,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_138,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_37])).

tff(c_156,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_156])).

tff(c_187,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_180])).

tff(c_16,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_20,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_39,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_39])).

tff(c_98,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_110,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_98])).

tff(c_117,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_110])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_117])).

tff(c_120,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_177,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_156])).

tff(c_233,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_177])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_233])).

tff(c_235,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_271,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_256])).

tff(c_339,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_271])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_339])).

tff(c_341,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_345,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_353,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_341,c_345])).

tff(c_367,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_376,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_367])).

tff(c_385,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_376])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_385])).

tff(c_388,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_342,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.28  
% 2.00/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.28  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.00/1.28  
% 2.00/1.28  %Foreground sorts:
% 2.00/1.28  
% 2.00/1.28  
% 2.00/1.28  %Background operators:
% 2.00/1.28  
% 2.00/1.28  
% 2.00/1.28  %Foreground operators:
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.28  
% 2.00/1.30  tff(f_42, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.00/1.30  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.00/1.30  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.00/1.30  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.00/1.30  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.00/1.30  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.00/1.30  tff(c_14, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.00/1.30  tff(c_343, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_14])).
% 2.00/1.30  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.30  tff(c_241, plain, (![A_28, B_29]: (r1_xboole_0(A_28, B_29) | k3_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.30  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.00/1.30  tff(c_37, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_18])).
% 2.00/1.30  tff(c_249, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_241, c_37])).
% 2.00/1.30  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.30  tff(c_256, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.30  tff(c_274, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_256])).
% 2.00/1.30  tff(c_277, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_274])).
% 2.00/1.30  tff(c_130, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k3_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.30  tff(c_138, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_130, c_37])).
% 2.00/1.30  tff(c_156, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.30  tff(c_180, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_156])).
% 2.00/1.30  tff(c_187, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_180])).
% 2.00/1.30  tff(c_16, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.00/1.30  tff(c_48, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_16])).
% 2.00/1.30  tff(c_20, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.00/1.30  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_20])).
% 2.00/1.30  tff(c_39, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.30  tff(c_43, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_39])).
% 2.00/1.30  tff(c_98, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.30  tff(c_110, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_43, c_98])).
% 2.00/1.30  tff(c_117, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_110])).
% 2.00/1.30  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_117])).
% 2.00/1.30  tff(c_120, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 2.00/1.30  tff(c_177, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_120, c_156])).
% 2.00/1.30  tff(c_233, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_187, c_177])).
% 2.00/1.30  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_233])).
% 2.00/1.30  tff(c_235, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 2.00/1.30  tff(c_271, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_235, c_256])).
% 2.00/1.30  tff(c_339, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_277, c_271])).
% 2.00/1.30  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_339])).
% 2.00/1.30  tff(c_341, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_18])).
% 2.00/1.30  tff(c_345, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.30  tff(c_353, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_341, c_345])).
% 2.00/1.30  tff(c_367, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.30  tff(c_376, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_353, c_367])).
% 2.00/1.30  tff(c_385, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_376])).
% 2.00/1.30  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_343, c_385])).
% 2.00/1.30  tff(c_388, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_14])).
% 2.00/1.30  tff(c_342, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_18])).
% 2.00/1.30  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_388, c_342])).
% 2.00/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.30  
% 2.00/1.30  Inference rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Ref     : 0
% 2.00/1.30  #Sup     : 89
% 2.00/1.30  #Fact    : 0
% 2.00/1.30  #Define  : 0
% 2.00/1.30  #Split   : 5
% 2.00/1.30  #Chain   : 0
% 2.00/1.30  #Close   : 0
% 2.00/1.30  
% 2.00/1.30  Ordering : KBO
% 2.00/1.30  
% 2.00/1.30  Simplification rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Subsume      : 2
% 2.00/1.30  #Demod        : 29
% 2.00/1.30  #Tautology    : 62
% 2.00/1.30  #SimpNegUnit  : 5
% 2.00/1.30  #BackRed      : 0
% 2.00/1.30  
% 2.00/1.30  #Partial instantiations: 0
% 2.00/1.30  #Strategies tried      : 1
% 2.00/1.30  
% 2.00/1.30  Timing (in seconds)
% 2.00/1.30  ----------------------
% 2.00/1.30  Preprocessing        : 0.24
% 2.00/1.30  Parsing              : 0.13
% 2.00/1.30  CNF conversion       : 0.02
% 2.00/1.30  Main loop            : 0.20
% 2.00/1.30  Inferencing          : 0.09
% 2.00/1.30  Reduction            : 0.06
% 2.00/1.30  Demodulation         : 0.05
% 2.00/1.30  BG Simplification    : 0.01
% 2.00/1.30  Subsumption          : 0.03
% 2.00/1.30  Abstraction          : 0.01
% 2.00/1.30  MUC search           : 0.00
% 2.00/1.30  Cooper               : 0.00
% 2.00/1.30  Total                : 0.47
% 2.00/1.30  Index Insertion      : 0.00
% 2.00/1.30  Index Deletion       : 0.00
% 2.00/1.30  Index Matching       : 0.00
% 2.00/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
