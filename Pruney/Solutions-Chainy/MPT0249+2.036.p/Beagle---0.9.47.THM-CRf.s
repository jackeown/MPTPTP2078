%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:28 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   40 (  80 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 ( 141 expanded)
%              Number of equality atoms :   29 (  81 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_33,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_33])).

tff(c_66,plain,(
    ! [B_21,A_22] :
      ( k1_tarski(B_21) = A_22
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_tarski(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_83,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_72])).

tff(c_42,plain,(
    ! [B_18,A_19] :
      ( B_18 = A_19
      | ~ r1_tarski(B_18,A_19)
      | ~ r1_tarski(A_19,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_42])).

tff(c_65,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_103,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_65])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_103])).

tff(c_110,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_37,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_tarski(A_14,k2_xboole_0(C_15,B_16))
      | ~ r1_tarski(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_14,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_37])).

tff(c_112,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,'#skF_2')
      | ~ r1_tarski(A_14,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_40])).

tff(c_166,plain,(
    ! [B_27,A_28] :
      ( k1_tarski(B_27) = A_28
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,k1_tarski(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_169,plain,(
    ! [A_28] :
      ( k1_tarski('#skF_1') = A_28
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_166])).

tff(c_182,plain,(
    ! [A_29] :
      ( A_29 = '#skF_2'
      | k1_xboole_0 = A_29
      | ~ r1_tarski(A_29,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_169])).

tff(c_202,plain,(
    ! [A_30] :
      ( A_30 = '#skF_2'
      | k1_xboole_0 = A_30
      | ~ r1_tarski(A_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_112,c_182])).

tff(c_206,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_202])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_22,c_206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.18  
% 1.89/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.18  %$ r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.18  
% 1.89/1.18  %Foreground sorts:
% 1.89/1.18  
% 1.89/1.18  
% 1.89/1.18  %Background operators:
% 1.89/1.18  
% 1.89/1.18  
% 1.89/1.18  %Foreground operators:
% 1.89/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.18  
% 1.89/1.19  tff(f_56, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.89/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.89/1.19  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.89/1.19  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.89/1.19  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.89/1.19  tff(c_18, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.89/1.19  tff(c_22, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.89/1.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.19  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.89/1.19  tff(c_24, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.89/1.19  tff(c_33, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.89/1.19  tff(c_36, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_33])).
% 1.89/1.19  tff(c_66, plain, (![B_21, A_22]: (k1_tarski(B_21)=A_22 | k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_tarski(B_21)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.89/1.19  tff(c_72, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_66])).
% 1.89/1.19  tff(c_83, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_20, c_72])).
% 1.89/1.19  tff(c_42, plain, (![B_18, A_19]: (B_18=A_19 | ~r1_tarski(B_18, A_19) | ~r1_tarski(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.19  tff(c_57, plain, (k1_tarski('#skF_1')='#skF_2' | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_36, c_42])).
% 1.89/1.19  tff(c_65, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_57])).
% 1.89/1.19  tff(c_103, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_65])).
% 1.89/1.19  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_103])).
% 1.89/1.19  tff(c_110, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_57])).
% 1.89/1.19  tff(c_37, plain, (![A_14, C_15, B_16]: (r1_tarski(A_14, k2_xboole_0(C_15, B_16)) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.19  tff(c_40, plain, (![A_14]: (r1_tarski(A_14, k1_tarski('#skF_1')) | ~r1_tarski(A_14, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_37])).
% 1.89/1.19  tff(c_112, plain, (![A_14]: (r1_tarski(A_14, '#skF_2') | ~r1_tarski(A_14, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_40])).
% 1.89/1.19  tff(c_166, plain, (![B_27, A_28]: (k1_tarski(B_27)=A_28 | k1_xboole_0=A_28 | ~r1_tarski(A_28, k1_tarski(B_27)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.89/1.19  tff(c_169, plain, (![A_28]: (k1_tarski('#skF_1')=A_28 | k1_xboole_0=A_28 | ~r1_tarski(A_28, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_166])).
% 1.89/1.19  tff(c_182, plain, (![A_29]: (A_29='#skF_2' | k1_xboole_0=A_29 | ~r1_tarski(A_29, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_169])).
% 1.89/1.19  tff(c_202, plain, (![A_30]: (A_30='#skF_2' | k1_xboole_0=A_30 | ~r1_tarski(A_30, '#skF_3'))), inference(resolution, [status(thm)], [c_112, c_182])).
% 1.89/1.19  tff(c_206, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_202])).
% 1.89/1.19  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_22, c_206])).
% 1.89/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  Inference rules
% 1.89/1.19  ----------------------
% 1.89/1.19  #Ref     : 0
% 1.89/1.19  #Sup     : 38
% 1.89/1.19  #Fact    : 0
% 1.89/1.19  #Define  : 0
% 1.89/1.19  #Split   : 1
% 1.89/1.19  #Chain   : 0
% 1.89/1.19  #Close   : 0
% 1.89/1.19  
% 1.89/1.19  Ordering : KBO
% 1.89/1.19  
% 1.89/1.19  Simplification rules
% 1.89/1.19  ----------------------
% 1.89/1.19  #Subsume      : 3
% 1.89/1.19  #Demod        : 18
% 1.89/1.19  #Tautology    : 20
% 1.89/1.19  #SimpNegUnit  : 6
% 1.89/1.19  #BackRed      : 7
% 1.89/1.19  
% 1.89/1.19  #Partial instantiations: 0
% 1.89/1.19  #Strategies tried      : 1
% 1.89/1.19  
% 1.89/1.19  Timing (in seconds)
% 1.89/1.19  ----------------------
% 1.89/1.20  Preprocessing        : 0.28
% 1.89/1.20  Parsing              : 0.15
% 1.89/1.20  CNF conversion       : 0.02
% 1.89/1.20  Main loop            : 0.17
% 1.89/1.20  Inferencing          : 0.05
% 1.89/1.20  Reduction            : 0.05
% 1.89/1.20  Demodulation         : 0.04
% 1.89/1.20  BG Simplification    : 0.01
% 1.89/1.20  Subsumption          : 0.04
% 1.89/1.20  Abstraction          : 0.01
% 1.89/1.20  MUC search           : 0.00
% 1.89/1.20  Cooper               : 0.00
% 1.89/1.20  Total                : 0.47
% 1.89/1.20  Index Insertion      : 0.00
% 1.89/1.20  Index Deletion       : 0.00
% 1.89/1.20  Index Matching       : 0.00
% 1.89/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
