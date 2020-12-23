%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:27 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   50 (  72 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  87 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_16,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_33,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_78,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k3_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_33])).

tff(c_14,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_114,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_69,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_87,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_102,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_87])).

tff(c_111,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_102])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_111])).

tff(c_116,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_6,B_7] : k3_xboole_0(k4_xboole_0(A_6,B_7),B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_34])).

tff(c_121,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_42])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_121])).

tff(c_129,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_137,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_10])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_137])).

tff(c_143,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_12,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_162,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_12])).

tff(c_142,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_144,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_158,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142,c_144])).

tff(c_203,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_224,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_203])).

tff(c_232,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_224])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:00:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.20  
% 1.83/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.20  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.83/1.20  
% 1.83/1.20  %Foreground sorts:
% 1.83/1.20  
% 1.83/1.20  
% 1.83/1.20  %Background operators:
% 1.83/1.20  
% 1.83/1.20  
% 1.83/1.20  %Foreground operators:
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.20  
% 1.83/1.21  tff(f_40, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.83/1.21  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.83/1.21  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.83/1.21  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.83/1.21  tff(f_35, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.83/1.21  tff(c_16, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.21  tff(c_33, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_16])).
% 1.83/1.21  tff(c_78, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k3_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.21  tff(c_86, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_78, c_33])).
% 1.83/1.21  tff(c_14, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.21  tff(c_114, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_14])).
% 1.83/1.21  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.21  tff(c_18, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.21  tff(c_69, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_18])).
% 1.83/1.21  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.21  tff(c_73, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_2])).
% 1.83/1.21  tff(c_87, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.83/1.21  tff(c_102, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_73, c_87])).
% 1.83/1.21  tff(c_111, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_102])).
% 1.83/1.21  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_111])).
% 1.83/1.21  tff(c_116, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_14])).
% 1.83/1.21  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.21  tff(c_34, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.21  tff(c_42, plain, (![A_6, B_7]: (k3_xboole_0(k4_xboole_0(A_6, B_7), B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_34])).
% 1.83/1.21  tff(c_121, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_116, c_42])).
% 1.83/1.21  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_121])).
% 1.83/1.21  tff(c_129, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_18])).
% 1.83/1.21  tff(c_137, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_129, c_10])).
% 1.83/1.21  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_137])).
% 1.83/1.21  tff(c_143, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_16])).
% 1.83/1.21  tff(c_12, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.21  tff(c_162, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_12])).
% 1.83/1.21  tff(c_142, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_16])).
% 1.83/1.21  tff(c_144, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.21  tff(c_158, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_142, c_144])).
% 1.83/1.21  tff(c_203, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.83/1.21  tff(c_224, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_158, c_203])).
% 1.83/1.21  tff(c_232, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_224])).
% 1.83/1.21  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_232])).
% 1.83/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.21  
% 1.83/1.21  Inference rules
% 1.83/1.21  ----------------------
% 1.83/1.21  #Ref     : 0
% 1.83/1.21  #Sup     : 56
% 1.83/1.21  #Fact    : 0
% 1.83/1.21  #Define  : 0
% 1.83/1.21  #Split   : 3
% 1.83/1.21  #Chain   : 0
% 1.83/1.21  #Close   : 0
% 1.83/1.21  
% 1.83/1.21  Ordering : KBO
% 1.83/1.21  
% 1.83/1.21  Simplification rules
% 1.83/1.21  ----------------------
% 1.83/1.21  #Subsume      : 3
% 1.83/1.21  #Demod        : 12
% 1.83/1.21  #Tautology    : 33
% 1.83/1.21  #SimpNegUnit  : 4
% 1.83/1.21  #BackRed      : 0
% 1.83/1.21  
% 1.83/1.21  #Partial instantiations: 0
% 1.83/1.21  #Strategies tried      : 1
% 1.83/1.21  
% 1.83/1.21  Timing (in seconds)
% 1.83/1.21  ----------------------
% 1.83/1.21  Preprocessing        : 0.26
% 1.83/1.21  Parsing              : 0.14
% 1.83/1.21  CNF conversion       : 0.02
% 1.83/1.21  Main loop            : 0.17
% 1.83/1.21  Inferencing          : 0.07
% 1.83/1.22  Reduction            : 0.05
% 1.83/1.22  Demodulation         : 0.04
% 1.83/1.22  BG Simplification    : 0.01
% 1.83/1.22  Subsumption          : 0.02
% 1.83/1.22  Abstraction          : 0.01
% 1.83/1.22  MUC search           : 0.00
% 1.83/1.22  Cooper               : 0.00
% 1.83/1.22  Total                : 0.46
% 1.83/1.22  Index Insertion      : 0.00
% 1.83/1.22  Index Deletion       : 0.00
% 1.83/1.22  Index Matching       : 0.00
% 1.83/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
