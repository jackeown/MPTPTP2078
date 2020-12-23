%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:16 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_18,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_14,B_15] : r1_tarski(k1_tarski(A_14),k2_tarski(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_94,plain,(
    ! [A_14,B_15] : k3_xboole_0(k1_tarski(A_14),k2_tarski(A_14,B_15)) = k1_tarski(A_14) ),
    inference(resolution,[status(thm)],[c_14,c_83])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_121,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_tarski(k3_xboole_0(A_31,C_32),B_33)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [B_36,A_37,B_38] :
      ( r1_tarski(k3_xboole_0(B_36,A_37),B_38)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_121])).

tff(c_194,plain,(
    ! [A_42,B_43,B_44] :
      ( r1_tarski(k1_tarski(A_42),B_43)
      | ~ r1_tarski(k2_tarski(A_42,B_44),B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_154])).

tff(c_201,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_194])).

tff(c_16,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | ~ r1_tarski(k1_tarski(A_16),k1_tarski(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_207,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_201,c_16])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.24  
% 1.97/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.25  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.97/1.25  
% 1.97/1.25  %Foreground sorts:
% 1.97/1.25  
% 1.97/1.25  
% 1.97/1.25  %Background operators:
% 1.97/1.25  
% 1.97/1.25  
% 1.97/1.25  %Foreground operators:
% 1.97/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.25  
% 1.97/1.25  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.97/1.25  tff(f_43, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.97/1.25  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.97/1.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.97/1.25  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.97/1.25  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.97/1.25  tff(c_18, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.97/1.25  tff(c_20, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.97/1.25  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), k2_tarski(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.25  tff(c_83, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.25  tff(c_94, plain, (![A_14, B_15]: (k3_xboole_0(k1_tarski(A_14), k2_tarski(A_14, B_15))=k1_tarski(A_14))), inference(resolution, [status(thm)], [c_14, c_83])).
% 1.97/1.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.25  tff(c_121, plain, (![A_31, C_32, B_33]: (r1_tarski(k3_xboole_0(A_31, C_32), B_33) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.25  tff(c_154, plain, (![B_36, A_37, B_38]: (r1_tarski(k3_xboole_0(B_36, A_37), B_38) | ~r1_tarski(A_37, B_38))), inference(superposition, [status(thm), theory('equality')], [c_2, c_121])).
% 1.97/1.26  tff(c_194, plain, (![A_42, B_43, B_44]: (r1_tarski(k1_tarski(A_42), B_43) | ~r1_tarski(k2_tarski(A_42, B_44), B_43))), inference(superposition, [status(thm), theory('equality')], [c_94, c_154])).
% 1.97/1.26  tff(c_201, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_194])).
% 1.97/1.26  tff(c_16, plain, (![B_17, A_16]: (B_17=A_16 | ~r1_tarski(k1_tarski(A_16), k1_tarski(B_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.26  tff(c_207, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_201, c_16])).
% 1.97/1.26  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_207])).
% 1.97/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.26  
% 1.97/1.26  Inference rules
% 1.97/1.26  ----------------------
% 1.97/1.26  #Ref     : 0
% 1.97/1.26  #Sup     : 50
% 1.97/1.26  #Fact    : 0
% 1.97/1.26  #Define  : 0
% 1.97/1.26  #Split   : 0
% 1.97/1.26  #Chain   : 0
% 1.97/1.26  #Close   : 0
% 1.97/1.26  
% 1.97/1.26  Ordering : KBO
% 1.97/1.26  
% 1.97/1.26  Simplification rules
% 1.97/1.26  ----------------------
% 1.97/1.26  #Subsume      : 3
% 1.97/1.26  #Demod        : 2
% 1.97/1.26  #Tautology    : 31
% 1.97/1.26  #SimpNegUnit  : 1
% 1.97/1.26  #BackRed      : 0
% 1.97/1.26  
% 1.97/1.26  #Partial instantiations: 0
% 1.97/1.26  #Strategies tried      : 1
% 1.97/1.26  
% 1.97/1.26  Timing (in seconds)
% 1.97/1.26  ----------------------
% 1.97/1.26  Preprocessing        : 0.29
% 1.97/1.26  Parsing              : 0.16
% 1.97/1.26  CNF conversion       : 0.02
% 1.97/1.26  Main loop            : 0.16
% 1.97/1.26  Inferencing          : 0.06
% 1.97/1.26  Reduction            : 0.05
% 1.97/1.26  Demodulation         : 0.04
% 1.97/1.26  BG Simplification    : 0.01
% 1.97/1.26  Subsumption          : 0.03
% 1.97/1.26  Abstraction          : 0.01
% 1.97/1.26  MUC search           : 0.00
% 1.97/1.26  Cooper               : 0.00
% 1.97/1.26  Total                : 0.46
% 1.97/1.26  Index Insertion      : 0.00
% 1.97/1.26  Index Deletion       : 0.00
% 1.97/1.26  Index Matching       : 0.00
% 1.97/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
