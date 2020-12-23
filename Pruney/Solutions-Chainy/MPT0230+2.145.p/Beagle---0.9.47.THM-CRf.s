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
% DateTime   : Thu Dec  3 09:49:14 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   47 (  51 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  50 expanded)
%              Number of equality atoms :   35 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( A != B
        & A != C
        & k4_xboole_0(k1_enumset1(A,B,C),k1_tarski(A)) != k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_enumset1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_36,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_96,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_87])).

tff(c_102,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_96])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_99,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_87])).

tff(c_110,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_99])).

tff(c_30,plain,(
    ! [B_45] : k4_xboole_0(k1_tarski(B_45),k1_tarski(B_45)) != k1_tarski(B_45) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_111,plain,(
    ! [B_45] : k1_tarski(B_45) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_30])).

tff(c_694,plain,(
    ! [A_92,B_93,C_94] :
      ( k4_xboole_0(k1_enumset1(A_92,B_93,C_94),k1_tarski(A_92)) = k2_tarski(B_93,C_94)
      | C_94 = A_92
      | B_93 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_703,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_tarski(A_92) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(A_92),k2_tarski(B_93,C_94))
      | C_94 = A_92
      | B_93 = A_92 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_8])).

tff(c_714,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r1_tarski(k1_tarski(A_95),k2_tarski(B_96,C_97))
      | C_97 = A_95
      | B_96 = A_95 ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_703])).

tff(c_717,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_714])).

tff(c_724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:46:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.33  
% 2.61/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.33  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.33  
% 2.61/1.33  %Foreground sorts:
% 2.61/1.33  
% 2.61/1.33  
% 2.61/1.33  %Background operators:
% 2.61/1.33  
% 2.61/1.33  
% 2.61/1.33  %Foreground operators:
% 2.61/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.33  
% 2.61/1.34  tff(f_78, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.61/1.34  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.61/1.34  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.61/1.34  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.61/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.61/1.34  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.61/1.34  tff(f_49, axiom, (![A, B, C]: ~((~(A = B) & ~(A = C)) & ~(k4_xboole_0(k1_enumset1(A, B, C), k1_tarski(A)) = k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_enumset1)).
% 2.61/1.34  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.61/1.34  tff(c_36, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.34  tff(c_34, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.34  tff(c_38, plain, (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.34  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.34  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.34  tff(c_87, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.34  tff(c_96, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_87])).
% 2.61/1.34  tff(c_102, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_96])).
% 2.61/1.34  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.61/1.34  tff(c_99, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_87])).
% 2.61/1.34  tff(c_110, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_102, c_99])).
% 2.61/1.34  tff(c_30, plain, (![B_45]: (k4_xboole_0(k1_tarski(B_45), k1_tarski(B_45))!=k1_tarski(B_45))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.61/1.34  tff(c_111, plain, (![B_45]: (k1_tarski(B_45)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_30])).
% 2.61/1.34  tff(c_694, plain, (![A_92, B_93, C_94]: (k4_xboole_0(k1_enumset1(A_92, B_93, C_94), k1_tarski(A_92))=k2_tarski(B_93, C_94) | C_94=A_92 | B_93=A_92)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.34  tff(c_8, plain, (![A_7, B_8]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k4_xboole_0(B_8, A_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.34  tff(c_703, plain, (![A_92, B_93, C_94]: (k1_tarski(A_92)=k1_xboole_0 | ~r1_tarski(k1_tarski(A_92), k2_tarski(B_93, C_94)) | C_94=A_92 | B_93=A_92)), inference(superposition, [status(thm), theory('equality')], [c_694, c_8])).
% 2.61/1.34  tff(c_714, plain, (![A_95, B_96, C_97]: (~r1_tarski(k1_tarski(A_95), k2_tarski(B_96, C_97)) | C_97=A_95 | B_96=A_95)), inference(negUnitSimplification, [status(thm)], [c_111, c_703])).
% 2.61/1.34  tff(c_717, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_38, c_714])).
% 2.61/1.34  tff(c_724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_717])).
% 2.61/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.34  
% 2.61/1.34  Inference rules
% 2.61/1.34  ----------------------
% 2.61/1.34  #Ref     : 0
% 2.61/1.34  #Sup     : 176
% 2.61/1.34  #Fact    : 0
% 2.61/1.34  #Define  : 0
% 2.61/1.34  #Split   : 0
% 2.61/1.34  #Chain   : 0
% 2.61/1.34  #Close   : 0
% 2.61/1.34  
% 2.61/1.34  Ordering : KBO
% 2.61/1.34  
% 2.61/1.34  Simplification rules
% 2.61/1.34  ----------------------
% 2.61/1.34  #Subsume      : 16
% 2.61/1.34  #Demod        : 75
% 2.61/1.34  #Tautology    : 105
% 2.61/1.34  #SimpNegUnit  : 5
% 2.61/1.34  #BackRed      : 1
% 2.61/1.34  
% 2.61/1.34  #Partial instantiations: 0
% 2.61/1.34  #Strategies tried      : 1
% 2.61/1.34  
% 2.61/1.34  Timing (in seconds)
% 2.61/1.34  ----------------------
% 2.61/1.35  Preprocessing        : 0.30
% 2.61/1.35  Parsing              : 0.16
% 2.61/1.35  CNF conversion       : 0.02
% 2.61/1.35  Main loop            : 0.29
% 2.61/1.35  Inferencing          : 0.11
% 2.61/1.35  Reduction            : 0.11
% 2.61/1.35  Demodulation         : 0.09
% 2.61/1.35  BG Simplification    : 0.02
% 2.61/1.35  Subsumption          : 0.04
% 2.61/1.35  Abstraction          : 0.02
% 2.61/1.35  MUC search           : 0.00
% 2.61/1.35  Cooper               : 0.00
% 2.61/1.35  Total                : 0.61
% 2.61/1.35  Index Insertion      : 0.00
% 2.61/1.35  Index Deletion       : 0.00
% 2.61/1.35  Index Matching       : 0.00
% 2.61/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
