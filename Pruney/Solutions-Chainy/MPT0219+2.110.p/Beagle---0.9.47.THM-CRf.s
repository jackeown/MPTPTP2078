%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:03 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [A_14,B_15] : r1_tarski(k1_tarski(A_14),k2_tarski(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_29,plain,(
    ! [A_8] : r1_tarski(k1_tarski(A_8),k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_26])).

tff(c_16,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_41,plain,(
    ! [A_19,C_20,B_21] :
      ( r1_tarski(A_19,k2_xboole_0(C_20,B_21))
      | ~ r1_tarski(A_19,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_24,k1_tarski('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_41])).

tff(c_77,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_29,c_72])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(k1_tarski(A_11),k1_tarski(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_77,c_12])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:40:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.32  
% 1.79/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.33  %$ r1_tarski > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.79/1.33  
% 1.79/1.33  %Foreground sorts:
% 1.79/1.33  
% 1.79/1.33  
% 1.79/1.33  %Background operators:
% 1.79/1.33  
% 1.79/1.33  
% 1.79/1.33  %Foreground operators:
% 1.79/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.79/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.33  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.33  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.33  
% 1.79/1.34  tff(f_46, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 1.79/1.34  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.79/1.34  tff(f_37, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.79/1.34  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.79/1.34  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.79/1.34  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.34  tff(c_8, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.34  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), k2_tarski(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.79/1.34  tff(c_29, plain, (![A_8]: (r1_tarski(k1_tarski(A_8), k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_26])).
% 1.79/1.34  tff(c_16, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.34  tff(c_41, plain, (![A_19, C_20, B_21]: (r1_tarski(A_19, k2_xboole_0(C_20, B_21)) | ~r1_tarski(A_19, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.34  tff(c_72, plain, (![A_24]: (r1_tarski(A_24, k1_tarski('#skF_1')) | ~r1_tarski(A_24, k1_tarski('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_16, c_41])).
% 1.79/1.34  tff(c_77, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_29, c_72])).
% 1.79/1.34  tff(c_12, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(k1_tarski(A_11), k1_tarski(B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.79/1.34  tff(c_80, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_77, c_12])).
% 1.79/1.34  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_80])).
% 1.79/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.34  
% 1.79/1.34  Inference rules
% 1.79/1.34  ----------------------
% 1.79/1.34  #Ref     : 0
% 1.79/1.34  #Sup     : 17
% 1.79/1.34  #Fact    : 0
% 1.79/1.34  #Define  : 0
% 1.79/1.34  #Split   : 0
% 1.79/1.34  #Chain   : 0
% 1.79/1.34  #Close   : 0
% 1.79/1.34  
% 1.79/1.34  Ordering : KBO
% 1.79/1.34  
% 1.79/1.34  Simplification rules
% 1.79/1.34  ----------------------
% 1.79/1.34  #Subsume      : 0
% 1.79/1.34  #Demod        : 2
% 1.79/1.34  #Tautology    : 11
% 1.79/1.34  #SimpNegUnit  : 1
% 1.79/1.34  #BackRed      : 0
% 1.79/1.34  
% 1.79/1.34  #Partial instantiations: 0
% 1.79/1.34  #Strategies tried      : 1
% 1.79/1.34  
% 1.79/1.34  Timing (in seconds)
% 1.79/1.34  ----------------------
% 1.95/1.34  Preprocessing        : 0.41
% 1.95/1.34  Parsing              : 0.21
% 1.95/1.34  CNF conversion       : 0.03
% 1.95/1.34  Main loop            : 0.10
% 1.95/1.34  Inferencing          : 0.04
% 1.95/1.34  Reduction            : 0.03
% 1.95/1.34  Demodulation         : 0.03
% 1.95/1.34  BG Simplification    : 0.01
% 1.95/1.34  Subsumption          : 0.02
% 1.95/1.34  Abstraction          : 0.00
% 1.95/1.34  MUC search           : 0.00
% 1.95/1.34  Cooper               : 0.00
% 1.95/1.34  Total                : 0.54
% 1.95/1.34  Index Insertion      : 0.00
% 1.95/1.34  Index Deletion       : 0.00
% 1.95/1.34  Index Matching       : 0.00
% 1.95/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
