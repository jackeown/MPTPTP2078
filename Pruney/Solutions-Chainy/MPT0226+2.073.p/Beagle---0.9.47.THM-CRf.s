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
% DateTime   : Thu Dec  3 09:48:47 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  50 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_40,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_61,plain,(
    ! [D_23,B_24] : r2_hidden(D_23,k2_tarski(D_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_64,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_61])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k2_xboole_0(A_28,B_29)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_75])).

tff(c_121,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden(A_41,B_42)
      | k4_xboole_0(k1_tarski(A_41),B_42) != k1_tarski(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_125,plain,(
    ! [A_41] :
      ( ~ r2_hidden(A_41,k1_tarski(A_41))
      | k1_tarski(A_41) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_121])).

tff(c_134,plain,(
    ! [A_41] : k1_tarski(A_41) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_125])).

tff(c_156,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(k1_tarski(A_49),B_50) = k1_tarski(A_49)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_173,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_42])).

tff(c_193,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_173])).

tff(c_135,plain,(
    ! [D_43,B_44,A_45] :
      ( D_43 = B_44
      | D_43 = A_45
      | ~ r2_hidden(D_43,k2_tarski(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_144,plain,(
    ! [D_43,A_14] :
      ( D_43 = A_14
      | D_43 = A_14
      | ~ r2_hidden(D_43,k1_tarski(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_135])).

tff(c_201,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_193,c_144])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.22  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.92/1.22  
% 1.92/1.22  %Foreground sorts:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Background operators:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Foreground operators:
% 1.92/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.22  
% 1.92/1.23  tff(f_63, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.92/1.23  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.92/1.23  tff(f_44, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.92/1.23  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.92/1.23  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.92/1.23  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.92/1.23  tff(c_40, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.92/1.23  tff(c_30, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.92/1.23  tff(c_61, plain, (![D_23, B_24]: (r2_hidden(D_23, k2_tarski(D_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.92/1.23  tff(c_64, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_61])).
% 1.92/1.23  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.23  tff(c_75, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k2_xboole_0(A_28, B_29))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.23  tff(c_82, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_75])).
% 1.92/1.23  tff(c_121, plain, (![A_41, B_42]: (~r2_hidden(A_41, B_42) | k4_xboole_0(k1_tarski(A_41), B_42)!=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.92/1.23  tff(c_125, plain, (![A_41]: (~r2_hidden(A_41, k1_tarski(A_41)) | k1_tarski(A_41)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_82, c_121])).
% 1.92/1.23  tff(c_134, plain, (![A_41]: (k1_tarski(A_41)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_125])).
% 1.92/1.23  tff(c_156, plain, (![A_49, B_50]: (k4_xboole_0(k1_tarski(A_49), B_50)=k1_tarski(A_49) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.92/1.23  tff(c_42, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.92/1.23  tff(c_173, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_42])).
% 1.92/1.23  tff(c_193, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_134, c_173])).
% 1.92/1.23  tff(c_135, plain, (![D_43, B_44, A_45]: (D_43=B_44 | D_43=A_45 | ~r2_hidden(D_43, k2_tarski(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.92/1.23  tff(c_144, plain, (![D_43, A_14]: (D_43=A_14 | D_43=A_14 | ~r2_hidden(D_43, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_135])).
% 1.92/1.23  tff(c_201, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_193, c_144])).
% 1.92/1.23  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_201])).
% 1.92/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.23  
% 1.92/1.23  Inference rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Ref     : 0
% 1.92/1.23  #Sup     : 36
% 1.92/1.23  #Fact    : 0
% 1.92/1.23  #Define  : 0
% 1.92/1.23  #Split   : 0
% 1.92/1.23  #Chain   : 0
% 1.92/1.23  #Close   : 0
% 1.92/1.23  
% 1.92/1.23  Ordering : KBO
% 1.92/1.23  
% 1.92/1.23  Simplification rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Subsume      : 1
% 1.92/1.23  #Demod        : 4
% 1.92/1.23  #Tautology    : 24
% 1.92/1.23  #SimpNegUnit  : 7
% 1.92/1.23  #BackRed      : 0
% 1.92/1.23  
% 1.92/1.23  #Partial instantiations: 0
% 1.92/1.23  #Strategies tried      : 1
% 1.92/1.23  
% 1.92/1.23  Timing (in seconds)
% 1.92/1.23  ----------------------
% 1.92/1.23  Preprocessing        : 0.28
% 1.92/1.23  Parsing              : 0.14
% 1.92/1.23  CNF conversion       : 0.02
% 1.92/1.23  Main loop            : 0.13
% 1.92/1.23  Inferencing          : 0.05
% 1.92/1.23  Reduction            : 0.04
% 1.92/1.23  Demodulation         : 0.03
% 1.92/1.23  BG Simplification    : 0.01
% 1.92/1.23  Subsumption          : 0.02
% 1.92/1.23  Abstraction          : 0.01
% 1.92/1.23  MUC search           : 0.00
% 1.92/1.23  Cooper               : 0.00
% 1.92/1.23  Total                : 0.44
% 1.92/1.23  Index Insertion      : 0.00
% 1.92/1.23  Index Deletion       : 0.00
% 1.92/1.23  Index Matching       : 0.00
% 1.92/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
