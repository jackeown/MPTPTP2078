%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:40 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   43 (  81 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 156 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_137,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(A_28,B_29)
      | k3_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_148,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_20])).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    r1_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_60,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_60])).

tff(c_214,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k2_relat_1(k3_xboole_0(A_39,B_40)),k3_xboole_0(k2_relat_1(A_39),k2_relat_1(B_40)))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_226,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0)
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_214])).

tff(c_236,plain,(
    r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_226])).

tff(c_8,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_xboole_0 = A_34
      | ~ r1_xboole_0(B_35,C_36)
      | ~ r1_tarski(A_34,C_36)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_212,plain,(
    ! [A_34,A_5] :
      ( k1_xboole_0 = A_34
      | ~ r1_tarski(A_34,k1_xboole_0)
      | ~ r1_tarski(A_34,A_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_194])).

tff(c_243,plain,(
    ! [A_5] :
      ( k2_relat_1(k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
      | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),A_5) ) ),
    inference(resolution,[status(thm)],[c_236,c_212])).

tff(c_306,plain,(
    ! [A_5] : ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),A_5) ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_236])).

tff(c_309,plain,(
    k2_relat_1(k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k3_xboole_0(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,(
    ! [A_25] :
      ( k2_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_87,plain,(
    ! [A_9,B_10] :
      ( k2_relat_1(k3_xboole_0(A_9,B_10)) != k1_xboole_0
      | k3_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_77])).

tff(c_314,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_87])).

tff(c_334,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_314])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.25  
% 2.16/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.25  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.25  
% 2.16/1.25  %Foreground sorts:
% 2.16/1.25  
% 2.16/1.25  
% 2.16/1.25  %Background operators:
% 2.16/1.25  
% 2.16/1.25  
% 2.16/1.25  %Foreground operators:
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.25  
% 2.16/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.16/1.26  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t215_relat_1)).
% 2.16/1.26  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 2.16/1.26  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.16/1.26  tff(f_43, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.16/1.26  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.16/1.26  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.16/1.26  tff(c_137, plain, (![A_28, B_29]: (r1_xboole_0(A_28, B_29) | k3_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.26  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.16/1.26  tff(c_148, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_137, c_20])).
% 2.16/1.26  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.16/1.26  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.16/1.26  tff(c_22, plain, (r1_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.16/1.26  tff(c_60, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.26  tff(c_75, plain, (k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_60])).
% 2.16/1.26  tff(c_214, plain, (![A_39, B_40]: (r1_tarski(k2_relat_1(k3_xboole_0(A_39, B_40)), k3_xboole_0(k2_relat_1(A_39), k2_relat_1(B_40))) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.16/1.26  tff(c_226, plain, (r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_75, c_214])).
% 2.16/1.26  tff(c_236, plain, (r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_226])).
% 2.16/1.26  tff(c_8, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.26  tff(c_194, plain, (![A_34, B_35, C_36]: (k1_xboole_0=A_34 | ~r1_xboole_0(B_35, C_36) | ~r1_tarski(A_34, C_36) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.26  tff(c_212, plain, (![A_34, A_5]: (k1_xboole_0=A_34 | ~r1_tarski(A_34, k1_xboole_0) | ~r1_tarski(A_34, A_5))), inference(resolution, [status(thm)], [c_8, c_194])).
% 2.16/1.26  tff(c_243, plain, (![A_5]: (k2_relat_1(k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), A_5))), inference(resolution, [status(thm)], [c_236, c_212])).
% 2.16/1.26  tff(c_306, plain, (![A_5]: (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), A_5))), inference(splitLeft, [status(thm)], [c_243])).
% 2.16/1.26  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_236])).
% 2.16/1.26  tff(c_309, plain, (k2_relat_1(k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_243])).
% 2.16/1.26  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k3_xboole_0(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.26  tff(c_77, plain, (![A_25]: (k2_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.16/1.26  tff(c_87, plain, (![A_9, B_10]: (k2_relat_1(k3_xboole_0(A_9, B_10))!=k1_xboole_0 | k3_xboole_0(A_9, B_10)=k1_xboole_0 | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_12, c_77])).
% 2.16/1.26  tff(c_314, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_309, c_87])).
% 2.16/1.26  tff(c_334, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_314])).
% 2.16/1.26  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_334])).
% 2.16/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.26  
% 2.16/1.26  Inference rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Ref     : 0
% 2.16/1.26  #Sup     : 75
% 2.16/1.26  #Fact    : 0
% 2.16/1.26  #Define  : 0
% 2.16/1.26  #Split   : 7
% 2.16/1.26  #Chain   : 0
% 2.16/1.26  #Close   : 0
% 2.16/1.26  
% 2.16/1.26  Ordering : KBO
% 2.16/1.26  
% 2.16/1.26  Simplification rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Subsume      : 6
% 2.16/1.26  #Demod        : 28
% 2.16/1.26  #Tautology    : 31
% 2.16/1.26  #SimpNegUnit  : 5
% 2.16/1.26  #BackRed      : 4
% 2.16/1.26  
% 2.16/1.26  #Partial instantiations: 0
% 2.16/1.26  #Strategies tried      : 1
% 2.16/1.26  
% 2.16/1.26  Timing (in seconds)
% 2.16/1.26  ----------------------
% 2.16/1.26  Preprocessing        : 0.27
% 2.16/1.26  Parsing              : 0.15
% 2.16/1.27  CNF conversion       : 0.02
% 2.16/1.27  Main loop            : 0.23
% 2.16/1.27  Inferencing          : 0.09
% 2.16/1.27  Reduction            : 0.07
% 2.16/1.27  Demodulation         : 0.05
% 2.16/1.27  BG Simplification    : 0.01
% 2.16/1.27  Subsumption          : 0.05
% 2.16/1.27  Abstraction          : 0.01
% 2.16/1.27  MUC search           : 0.00
% 2.16/1.27  Cooper               : 0.00
% 2.16/1.27  Total                : 0.53
% 2.16/1.27  Index Insertion      : 0.00
% 2.16/1.27  Index Deletion       : 0.00
% 2.16/1.27  Index Matching       : 0.00
% 2.16/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
