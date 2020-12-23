%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:58 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   26 (  40 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  50 expanded)
%              Number of equality atoms :   11 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_17,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_13])).

tff(c_10,plain,(
    k7_relat_1('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k7_relat_1('#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17,c_17,c_10])).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k7_relat_1(A_8,B_9))
      | ~ v1_xboole_0(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17,c_2])).

tff(c_36,plain,(
    ! [A_10,B_11] :
      ( k7_relat_1(A_10,B_11) = '#skF_1'
      | ~ v1_xboole_0(B_11)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_31,c_18])).

tff(c_43,plain,(
    ! [A_12] :
      ( k7_relat_1(A_12,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_4,c_36])).

tff(c_49,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_43])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.06  
% 1.52/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.07  %$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.52/1.07  
% 1.52/1.07  %Foreground sorts:
% 1.52/1.07  
% 1.52/1.07  
% 1.52/1.07  %Background operators:
% 1.52/1.07  
% 1.52/1.07  
% 1.52/1.07  %Foreground operators:
% 1.52/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.07  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.52/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.52/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.52/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.52/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.52/1.07  
% 1.52/1.07  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.52/1.07  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.52/1.07  tff(f_44, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 1.52/1.07  tff(f_39, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_relat_1)).
% 1.52/1.07  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.52/1.07  tff(c_13, plain, (![A_4]: (k1_xboole_0=A_4 | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.52/1.07  tff(c_17, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_13])).
% 1.52/1.07  tff(c_10, plain, (k7_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.52/1.07  tff(c_19, plain, (k7_relat_1('#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17, c_17, c_10])).
% 1.52/1.07  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.52/1.07  tff(c_31, plain, (![A_8, B_9]: (v1_xboole_0(k7_relat_1(A_8, B_9)) | ~v1_xboole_0(B_9) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.52/1.07  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.52/1.07  tff(c_18, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_17, c_2])).
% 1.52/1.07  tff(c_36, plain, (![A_10, B_11]: (k7_relat_1(A_10, B_11)='#skF_1' | ~v1_xboole_0(B_11) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_31, c_18])).
% 1.52/1.07  tff(c_43, plain, (![A_12]: (k7_relat_1(A_12, '#skF_1')='#skF_1' | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_4, c_36])).
% 1.52/1.07  tff(c_49, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_12, c_43])).
% 1.52/1.07  tff(c_54, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19, c_49])).
% 1.52/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.07  
% 1.52/1.07  Inference rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Ref     : 0
% 1.52/1.07  #Sup     : 9
% 1.52/1.07  #Fact    : 0
% 1.52/1.07  #Define  : 0
% 1.52/1.07  #Split   : 0
% 1.52/1.07  #Chain   : 0
% 1.52/1.07  #Close   : 0
% 1.52/1.07  
% 1.52/1.07  Ordering : KBO
% 1.52/1.07  
% 1.52/1.07  Simplification rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Subsume      : 0
% 1.52/1.07  #Demod        : 3
% 1.52/1.07  #Tautology    : 3
% 1.52/1.07  #SimpNegUnit  : 1
% 1.52/1.07  #BackRed      : 2
% 1.52/1.07  
% 1.52/1.07  #Partial instantiations: 0
% 1.52/1.07  #Strategies tried      : 1
% 1.52/1.07  
% 1.52/1.07  Timing (in seconds)
% 1.52/1.07  ----------------------
% 1.52/1.08  Preprocessing        : 0.24
% 1.52/1.08  Parsing              : 0.13
% 1.64/1.08  CNF conversion       : 0.01
% 1.64/1.08  Main loop            : 0.09
% 1.64/1.08  Inferencing          : 0.04
% 1.64/1.08  Reduction            : 0.02
% 1.64/1.08  Demodulation         : 0.02
% 1.64/1.08  BG Simplification    : 0.01
% 1.64/1.08  Subsumption          : 0.01
% 1.64/1.08  Abstraction          : 0.00
% 1.64/1.08  MUC search           : 0.00
% 1.64/1.08  Cooper               : 0.00
% 1.64/1.08  Total                : 0.35
% 1.64/1.08  Index Insertion      : 0.00
% 1.64/1.08  Index Deletion       : 0.00
% 1.64/1.08  Index Matching       : 0.00
% 1.64/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
