%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:28 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   27 (  30 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  42 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_10,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_31,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14,c_31])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_xboole_0(A_14,C_15)
      | ~ r1_xboole_0(B_16,C_15)
      | ~ r1_tarski(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_55,plain,(
    ! [A_17] :
      ( r1_xboole_0(A_17,'#skF_3')
      | ~ r1_tarski(A_17,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_48])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [A_18] :
      ( k3_xboole_0(A_18,'#skF_3') = k1_xboole_0
      | ~ r1_tarski(A_18,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_66,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_63])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_66])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.09  
% 1.61/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.09  %$ r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.61/1.09  
% 1.61/1.09  %Foreground sorts:
% 1.61/1.09  
% 1.61/1.09  
% 1.61/1.09  %Background operators:
% 1.61/1.09  
% 1.61/1.09  
% 1.61/1.09  %Foreground operators:
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.61/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.61/1.09  
% 1.61/1.10  tff(f_48, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.61/1.10  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.61/1.10  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.61/1.10  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.61/1.10  tff(c_10, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.61/1.10  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.61/1.10  tff(c_31, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.10  tff(c_38, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_14, c_31])).
% 1.61/1.10  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.61/1.10  tff(c_12, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.61/1.10  tff(c_48, plain, (![A_14, C_15, B_16]: (r1_xboole_0(A_14, C_15) | ~r1_xboole_0(B_16, C_15) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.61/1.10  tff(c_55, plain, (![A_17]: (r1_xboole_0(A_17, '#skF_3') | ~r1_tarski(A_17, '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_48])).
% 1.61/1.10  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.10  tff(c_63, plain, (![A_18]: (k3_xboole_0(A_18, '#skF_3')=k1_xboole_0 | ~r1_tarski(A_18, '#skF_2'))), inference(resolution, [status(thm)], [c_55, c_2])).
% 1.61/1.10  tff(c_66, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_63])).
% 1.61/1.10  tff(c_68, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_66])).
% 1.61/1.10  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_68])).
% 1.61/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.10  
% 1.61/1.10  Inference rules
% 1.61/1.10  ----------------------
% 1.61/1.10  #Ref     : 0
% 1.61/1.10  #Sup     : 15
% 1.61/1.10  #Fact    : 0
% 1.61/1.10  #Define  : 0
% 1.61/1.10  #Split   : 0
% 1.61/1.10  #Chain   : 0
% 1.61/1.10  #Close   : 0
% 1.61/1.10  
% 1.61/1.10  Ordering : KBO
% 1.61/1.10  
% 1.61/1.10  Simplification rules
% 1.61/1.10  ----------------------
% 1.61/1.10  #Subsume      : 0
% 1.61/1.10  #Demod        : 1
% 1.61/1.10  #Tautology    : 7
% 1.61/1.10  #SimpNegUnit  : 1
% 1.61/1.10  #BackRed      : 0
% 1.61/1.10  
% 1.61/1.10  #Partial instantiations: 0
% 1.61/1.10  #Strategies tried      : 1
% 1.61/1.10  
% 1.61/1.10  Timing (in seconds)
% 1.61/1.10  ----------------------
% 1.61/1.10  Preprocessing        : 0.25
% 1.61/1.10  Parsing              : 0.14
% 1.61/1.10  CNF conversion       : 0.01
% 1.61/1.10  Main loop            : 0.08
% 1.61/1.10  Inferencing          : 0.03
% 1.61/1.10  Reduction            : 0.02
% 1.61/1.10  Demodulation         : 0.02
% 1.61/1.10  BG Simplification    : 0.01
% 1.61/1.10  Subsumption          : 0.01
% 1.61/1.10  Abstraction          : 0.00
% 1.61/1.10  MUC search           : 0.00
% 1.61/1.10  Cooper               : 0.00
% 1.61/1.10  Total                : 0.35
% 1.61/1.10  Index Insertion      : 0.00
% 1.61/1.10  Index Deletion       : 0.00
% 1.61/1.10  Index Matching       : 0.00
% 1.61/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
