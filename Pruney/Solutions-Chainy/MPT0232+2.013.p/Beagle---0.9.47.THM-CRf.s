%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:21 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   45 (  51 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  57 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_89,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [E_18,A_12,B_13] : r2_hidden(E_18,k1_enumset1(A_12,B_13,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_98,plain,(
    ! [B_46,A_45] : r2_hidden(B_46,k2_tarski(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_32])).

tff(c_28,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_119,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_137,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ r1_tarski(A_57,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_119])).

tff(c_155,plain,(
    ! [B_58] : k4_xboole_0(k1_xboole_0,B_58) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_137])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_173,plain,(
    ! [D_62,B_63] :
      ( ~ r2_hidden(D_62,B_63)
      | ~ r2_hidden(D_62,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_4])).

tff(c_186,plain,(
    ! [B_46] : ~ r2_hidden(B_46,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_98,c_173])).

tff(c_68,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_70,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_202,plain,(
    ! [B_68,A_69] :
      ( k1_tarski(B_68) = A_69
      | k1_xboole_0 = A_69
      | ~ r1_tarski(A_69,k1_tarski(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_205,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_202])).

tff(c_220,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_205])).

tff(c_233,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_98])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.21  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.88/1.21  
% 1.88/1.21  %Foreground sorts:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Background operators:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Foreground operators:
% 1.88/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.88/1.21  tff('#skF_7', type, '#skF_7': $i).
% 1.88/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.88/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.88/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.88/1.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.88/1.21  
% 1.88/1.22  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.88/1.22  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 1.88/1.22  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.88/1.22  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.88/1.22  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.88/1.22  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.88/1.22  tff(f_79, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 1.88/1.22  tff(f_74, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.88/1.22  tff(c_89, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.88/1.22  tff(c_32, plain, (![E_18, A_12, B_13]: (r2_hidden(E_18, k1_enumset1(A_12, B_13, E_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.88/1.22  tff(c_98, plain, (![B_46, A_45]: (r2_hidden(B_46, k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_32])).
% 1.88/1.22  tff(c_28, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.22  tff(c_26, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.88/1.22  tff(c_119, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.22  tff(c_137, plain, (![A_57]: (k1_xboole_0=A_57 | ~r1_tarski(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_119])).
% 1.88/1.22  tff(c_155, plain, (![B_58]: (k4_xboole_0(k1_xboole_0, B_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_137])).
% 1.88/1.22  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.22  tff(c_173, plain, (![D_62, B_63]: (~r2_hidden(D_62, B_63) | ~r2_hidden(D_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_155, c_4])).
% 1.88/1.22  tff(c_186, plain, (![B_46]: (~r2_hidden(B_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_98, c_173])).
% 1.88/1.22  tff(c_68, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.88/1.22  tff(c_70, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.88/1.22  tff(c_202, plain, (![B_68, A_69]: (k1_tarski(B_68)=A_69 | k1_xboole_0=A_69 | ~r1_tarski(A_69, k1_tarski(B_68)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.88/1.22  tff(c_205, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_202])).
% 1.88/1.22  tff(c_220, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_205])).
% 1.88/1.22  tff(c_233, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_220, c_98])).
% 1.88/1.22  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_233])).
% 1.88/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  Inference rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Ref     : 0
% 1.88/1.22  #Sup     : 37
% 1.88/1.22  #Fact    : 0
% 1.88/1.22  #Define  : 0
% 1.88/1.22  #Split   : 0
% 1.88/1.22  #Chain   : 0
% 1.88/1.22  #Close   : 0
% 1.88/1.22  
% 1.88/1.22  Ordering : KBO
% 1.88/1.22  
% 1.88/1.22  Simplification rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Subsume      : 6
% 1.88/1.22  #Demod        : 11
% 1.88/1.22  #Tautology    : 22
% 1.88/1.22  #SimpNegUnit  : 3
% 1.88/1.22  #BackRed      : 3
% 1.88/1.22  
% 1.88/1.22  #Partial instantiations: 0
% 1.88/1.22  #Strategies tried      : 1
% 1.88/1.22  
% 1.88/1.22  Timing (in seconds)
% 1.88/1.22  ----------------------
% 1.88/1.23  Preprocessing        : 0.31
% 1.88/1.23  Parsing              : 0.15
% 1.88/1.23  CNF conversion       : 0.02
% 1.88/1.23  Main loop            : 0.16
% 1.88/1.23  Inferencing          : 0.04
% 1.88/1.23  Reduction            : 0.06
% 1.88/1.23  Demodulation         : 0.04
% 1.88/1.23  BG Simplification    : 0.02
% 1.88/1.23  Subsumption          : 0.04
% 1.88/1.23  Abstraction          : 0.01
% 1.88/1.23  MUC search           : 0.00
% 1.88/1.23  Cooper               : 0.00
% 1.88/1.23  Total                : 0.50
% 1.88/1.23  Index Insertion      : 0.00
% 1.88/1.23  Index Deletion       : 0.00
% 1.88/1.23  Index Matching       : 0.00
% 1.88/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
