%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:14 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   41 (  43 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  44 expanded)
%              Number of equality atoms :   31 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( A != B
        & A != C
        & k4_xboole_0(k1_enumset1(A,B,C),k1_tarski(A)) != k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_30,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_81,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_24,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_82,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_24])).

tff(c_151,plain,(
    ! [A_63,B_64,C_65] :
      ( k4_xboole_0(k1_enumset1(A_63,B_64,C_65),k1_tarski(A_63)) = k2_tarski(B_64,C_65)
      | C_65 = A_63
      | B_64 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_157,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_tarski(A_63) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(A_63),k2_tarski(B_64,C_65))
      | C_65 = A_63
      | B_64 = A_63 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_6])).

tff(c_177,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ r1_tarski(k1_tarski(A_72),k2_tarski(B_73,C_74))
      | C_74 = A_72
      | B_73 = A_72 ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_157])).

tff(c_180,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_177])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.22  
% 2.00/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.22  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.00/1.22  
% 2.00/1.22  %Foreground sorts:
% 2.00/1.22  
% 2.00/1.22  
% 2.00/1.22  %Background operators:
% 2.00/1.22  
% 2.00/1.22  
% 2.00/1.22  %Foreground operators:
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.22  
% 2.00/1.23  tff(f_72, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.00/1.23  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.00/1.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.00/1.23  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.00/1.23  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.00/1.23  tff(f_45, axiom, (![A, B, C]: ~((~(A = B) & ~(A = C)) & ~(k4_xboole_0(k1_enumset1(A, B, C), k1_tarski(A)) = k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_enumset1)).
% 2.00/1.23  tff(f_33, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.00/1.23  tff(c_30, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.23  tff(c_28, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.23  tff(c_32, plain, (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.23  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.23  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.00/1.23  tff(c_69, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.23  tff(c_78, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_69])).
% 2.00/1.23  tff(c_81, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_78])).
% 2.00/1.23  tff(c_24, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.00/1.23  tff(c_82, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_24])).
% 2.00/1.23  tff(c_151, plain, (![A_63, B_64, C_65]: (k4_xboole_0(k1_enumset1(A_63, B_64, C_65), k1_tarski(A_63))=k2_tarski(B_64, C_65) | C_65=A_63 | B_64=A_63)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.23  tff(c_6, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k4_xboole_0(B_6, A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.23  tff(c_157, plain, (![A_63, B_64, C_65]: (k1_tarski(A_63)=k1_xboole_0 | ~r1_tarski(k1_tarski(A_63), k2_tarski(B_64, C_65)) | C_65=A_63 | B_64=A_63)), inference(superposition, [status(thm), theory('equality')], [c_151, c_6])).
% 2.00/1.23  tff(c_177, plain, (![A_72, B_73, C_74]: (~r1_tarski(k1_tarski(A_72), k2_tarski(B_73, C_74)) | C_74=A_72 | B_73=A_72)), inference(negUnitSimplification, [status(thm)], [c_82, c_157])).
% 2.00/1.23  tff(c_180, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_32, c_177])).
% 2.00/1.23  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_180])).
% 2.00/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  Inference rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Ref     : 0
% 2.00/1.23  #Sup     : 33
% 2.00/1.23  #Fact    : 0
% 2.00/1.23  #Define  : 0
% 2.00/1.23  #Split   : 0
% 2.00/1.23  #Chain   : 0
% 2.00/1.23  #Close   : 0
% 2.00/1.23  
% 2.00/1.23  Ordering : KBO
% 2.00/1.23  
% 2.00/1.23  Simplification rules
% 2.11/1.23  ----------------------
% 2.11/1.23  #Subsume      : 0
% 2.11/1.23  #Demod        : 2
% 2.11/1.23  #Tautology    : 27
% 2.11/1.23  #SimpNegUnit  : 5
% 2.11/1.23  #BackRed      : 1
% 2.11/1.23  
% 2.11/1.23  #Partial instantiations: 0
% 2.11/1.23  #Strategies tried      : 1
% 2.11/1.23  
% 2.11/1.23  Timing (in seconds)
% 2.11/1.23  ----------------------
% 2.11/1.23  Preprocessing        : 0.32
% 2.11/1.23  Parsing              : 0.17
% 2.11/1.23  CNF conversion       : 0.02
% 2.11/1.24  Main loop            : 0.14
% 2.11/1.24  Inferencing          : 0.06
% 2.11/1.24  Reduction            : 0.04
% 2.11/1.24  Demodulation         : 0.03
% 2.11/1.24  BG Simplification    : 0.01
% 2.11/1.24  Subsumption          : 0.02
% 2.11/1.24  Abstraction          : 0.01
% 2.11/1.24  MUC search           : 0.00
% 2.11/1.24  Cooper               : 0.00
% 2.11/1.24  Total                : 0.49
% 2.11/1.24  Index Insertion      : 0.00
% 2.11/1.24  Index Deletion       : 0.00
% 2.11/1.24  Index Matching       : 0.00
% 2.13/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
