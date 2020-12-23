%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:23 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   40 (  51 expanded)
%              Number of equality atoms :   19 (  26 expanded)
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

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_101,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_110,plain,(
    ! [A_45,B_46] : r2_hidden(A_45,k2_tarski(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_28])).

tff(c_77,plain,(
    ! [A_33,B_34] : r1_tarski(k4_xboole_0(A_33,B_34),A_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [B_34] : k4_xboole_0(k1_xboole_0,B_34) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_22])).

tff(c_134,plain,(
    ! [D_55,B_56,A_57] :
      ( ~ r2_hidden(D_55,B_56)
      | ~ r2_hidden(D_55,k4_xboole_0(A_57,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_147,plain,(
    ! [D_61,B_62] :
      ( ~ r2_hidden(D_61,B_62)
      | ~ r2_hidden(D_61,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_134])).

tff(c_160,plain,(
    ! [A_45] : ~ r2_hidden(A_45,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_110,c_147])).

tff(c_62,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_64,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_167,plain,(
    ! [B_64,A_65] :
      ( k1_tarski(B_64) = A_65
      | k1_xboole_0 = A_65
      | ~ r1_tarski(A_65,k1_tarski(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_170,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_167])).

tff(c_183,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_170])).

tff(c_195,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_110])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.24  
% 2.05/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.24  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.05/1.24  
% 2.05/1.24  %Foreground sorts:
% 2.05/1.24  
% 2.05/1.24  
% 2.05/1.24  %Background operators:
% 2.05/1.24  
% 2.05/1.24  
% 2.05/1.24  %Foreground operators:
% 2.05/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.05/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.05/1.24  tff('#skF_7', type, '#skF_7': $i).
% 2.05/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.05/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.05/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.05/1.24  
% 2.05/1.25  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.05/1.25  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.05/1.25  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.05/1.25  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.05/1.25  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.05/1.25  tff(f_75, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.05/1.25  tff(f_70, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.05/1.25  tff(c_101, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.05/1.25  tff(c_28, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.05/1.25  tff(c_110, plain, (![A_45, B_46]: (r2_hidden(A_45, k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_28])).
% 2.05/1.25  tff(c_77, plain, (![A_33, B_34]: (r1_tarski(k4_xboole_0(A_33, B_34), A_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.25  tff(c_22, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.25  tff(c_82, plain, (![B_34]: (k4_xboole_0(k1_xboole_0, B_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_77, c_22])).
% 2.05/1.25  tff(c_134, plain, (![D_55, B_56, A_57]: (~r2_hidden(D_55, B_56) | ~r2_hidden(D_55, k4_xboole_0(A_57, B_56)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.25  tff(c_147, plain, (![D_61, B_62]: (~r2_hidden(D_61, B_62) | ~r2_hidden(D_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_82, c_134])).
% 2.05/1.25  tff(c_160, plain, (![A_45]: (~r2_hidden(A_45, k1_xboole_0))), inference(resolution, [status(thm)], [c_110, c_147])).
% 2.05/1.25  tff(c_62, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.25  tff(c_64, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.25  tff(c_167, plain, (![B_64, A_65]: (k1_tarski(B_64)=A_65 | k1_xboole_0=A_65 | ~r1_tarski(A_65, k1_tarski(B_64)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.05/1.25  tff(c_170, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_167])).
% 2.05/1.25  tff(c_183, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_170])).
% 2.05/1.25  tff(c_195, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_183, c_110])).
% 2.05/1.25  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_195])).
% 2.05/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.25  
% 2.05/1.25  Inference rules
% 2.05/1.25  ----------------------
% 2.05/1.25  #Ref     : 0
% 2.05/1.25  #Sup     : 32
% 2.05/1.25  #Fact    : 0
% 2.05/1.25  #Define  : 0
% 2.05/1.25  #Split   : 0
% 2.05/1.25  #Chain   : 0
% 2.05/1.25  #Close   : 0
% 2.05/1.25  
% 2.05/1.25  Ordering : KBO
% 2.05/1.25  
% 2.05/1.25  Simplification rules
% 2.05/1.25  ----------------------
% 2.05/1.25  #Subsume      : 6
% 2.05/1.25  #Demod        : 5
% 2.05/1.25  #Tautology    : 16
% 2.05/1.25  #SimpNegUnit  : 2
% 2.05/1.25  #BackRed      : 2
% 2.05/1.25  
% 2.05/1.25  #Partial instantiations: 0
% 2.05/1.25  #Strategies tried      : 1
% 2.05/1.25  
% 2.05/1.25  Timing (in seconds)
% 2.05/1.25  ----------------------
% 2.05/1.25  Preprocessing        : 0.32
% 2.05/1.25  Parsing              : 0.16
% 2.05/1.25  CNF conversion       : 0.03
% 2.05/1.25  Main loop            : 0.16
% 2.05/1.25  Inferencing          : 0.05
% 2.05/1.25  Reduction            : 0.06
% 2.05/1.25  Demodulation         : 0.04
% 2.05/1.25  BG Simplification    : 0.02
% 2.05/1.25  Subsumption          : 0.03
% 2.05/1.25  Abstraction          : 0.01
% 2.05/1.25  MUC search           : 0.00
% 2.05/1.25  Cooper               : 0.00
% 2.05/1.25  Total                : 0.50
% 2.05/1.25  Index Insertion      : 0.00
% 2.05/1.25  Index Deletion       : 0.00
% 2.05/1.25  Index Matching       : 0.00
% 2.05/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
