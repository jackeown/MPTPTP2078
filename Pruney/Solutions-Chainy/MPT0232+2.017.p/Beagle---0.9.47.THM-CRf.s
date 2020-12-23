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
% DateTime   : Thu Dec  3 09:49:22 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   25 (  33 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  36 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
     => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_16,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [C_13,A_14,B_15] :
      ( C_13 = A_14
      | ~ r1_tarski(k2_tarski(A_14,B_15),k1_tarski(C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_20])).

tff(c_14,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k1_tarski(A_5),k2_tarski(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_1')
    | ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_2])).

tff(c_53,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_47])).

tff(c_55,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.14  
% 1.71/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.15  %$ r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.71/1.15  
% 1.71/1.15  %Foreground sorts:
% 1.71/1.15  
% 1.71/1.15  
% 1.71/1.15  %Background operators:
% 1.71/1.15  
% 1.71/1.15  
% 1.71/1.15  %Foreground operators:
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.15  
% 1.71/1.15  tff(f_44, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 1.71/1.15  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.71/1.15  tff(f_35, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.71/1.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.71/1.15  tff(c_16, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.71/1.15  tff(c_20, plain, (![C_13, A_14, B_15]: (C_13=A_14 | ~r1_tarski(k2_tarski(A_14, B_15), k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.15  tff(c_24, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_16, c_20])).
% 1.71/1.15  tff(c_14, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.71/1.15  tff(c_41, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14])).
% 1.71/1.15  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), k2_tarski(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.15  tff(c_40, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16])).
% 1.71/1.15  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.15  tff(c_47, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_1') | ~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_2])).
% 1.71/1.15  tff(c_53, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_47])).
% 1.71/1.15  tff(c_55, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_53])).
% 1.71/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.15  
% 1.71/1.15  Inference rules
% 1.71/1.15  ----------------------
% 1.71/1.15  #Ref     : 0
% 1.71/1.15  #Sup     : 8
% 1.71/1.15  #Fact    : 0
% 1.71/1.15  #Define  : 0
% 1.71/1.15  #Split   : 0
% 1.71/1.15  #Chain   : 0
% 1.71/1.15  #Close   : 0
% 1.71/1.15  
% 1.71/1.15  Ordering : KBO
% 1.71/1.16  
% 1.71/1.16  Simplification rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Subsume      : 0
% 1.71/1.16  #Demod        : 5
% 1.71/1.16  #Tautology    : 4
% 1.71/1.16  #SimpNegUnit  : 2
% 1.71/1.16  #BackRed      : 2
% 1.71/1.16  
% 1.71/1.16  #Partial instantiations: 0
% 1.71/1.16  #Strategies tried      : 1
% 1.71/1.16  
% 1.71/1.16  Timing (in seconds)
% 1.71/1.16  ----------------------
% 1.71/1.16  Preprocessing        : 0.27
% 1.71/1.16  Parsing              : 0.15
% 1.71/1.16  CNF conversion       : 0.01
% 1.71/1.16  Main loop            : 0.07
% 1.71/1.16  Inferencing          : 0.03
% 1.71/1.16  Reduction            : 0.03
% 1.71/1.16  Demodulation         : 0.02
% 1.71/1.16  BG Simplification    : 0.01
% 1.71/1.16  Subsumption          : 0.01
% 1.71/1.16  Abstraction          : 0.00
% 1.71/1.16  MUC search           : 0.00
% 1.71/1.16  Cooper               : 0.00
% 1.71/1.16  Total                : 0.37
% 1.71/1.16  Index Insertion      : 0.00
% 1.71/1.16  Index Deletion       : 0.00
% 1.71/1.16  Index Matching       : 0.00
% 1.71/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
