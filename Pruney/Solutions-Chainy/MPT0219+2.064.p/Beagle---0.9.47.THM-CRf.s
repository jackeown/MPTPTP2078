%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:57 EST 2020

% Result     : Theorem 9.57s
% Output     : CNFRefutation 9.57s
% Verified   : 
% Statistics : Number of formulae       :   41 (  44 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   28 (  32 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_64,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    ! [A_38] : k2_tarski(A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_60,plain,(
    ! [A_41,B_42,C_43] : k2_enumset1(A_41,A_41,B_42,C_43) = k1_enumset1(A_41,B_42,C_43) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2025,plain,(
    ! [A_2236,B_2237,C_2238,D_2239] : k2_xboole_0(k2_tarski(A_2236,B_2237),k2_tarski(C_2238,D_2239)) = k2_enumset1(A_2236,B_2237,C_2238,D_2239) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2052,plain,(
    ! [A_38,C_2238,D_2239] : k2_xboole_0(k1_tarski(A_38),k2_tarski(C_2238,D_2239)) = k2_enumset1(A_38,A_38,C_2238,D_2239) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2025])).

tff(c_5796,plain,(
    ! [A_4730,C_4731,D_4732] : k2_xboole_0(k1_tarski(A_4730),k2_tarski(C_4731,D_4732)) = k1_enumset1(A_4730,C_4731,D_4732) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2052])).

tff(c_18164,plain,(
    ! [A_8556,A_8557] : k2_xboole_0(k1_tarski(A_8556),k1_tarski(A_8557)) = k1_enumset1(A_8556,A_8557,A_8557) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_5796])).

tff(c_66,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18301,plain,(
    k1_enumset1('#skF_5','#skF_6','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18164,c_66])).

tff(c_20,plain,(
    ! [E_21,A_15,C_17] : r2_hidden(E_21,k1_enumset1(A_15,E_21,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18475,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18301,c_20])).

tff(c_40,plain,(
    ! [C_26,A_22] :
      ( C_26 = A_22
      | ~ r2_hidden(C_26,k1_tarski(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18517,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_18475,c_40])).

tff(c_18558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_18517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:15:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.57/3.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.57/3.63  
% 9.57/3.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.57/3.63  %$ r2_hidden > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 9.57/3.63  
% 9.57/3.63  %Foreground sorts:
% 9.57/3.63  
% 9.57/3.63  
% 9.57/3.63  %Background operators:
% 9.57/3.63  
% 9.57/3.63  
% 9.57/3.63  %Foreground operators:
% 9.57/3.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.57/3.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.57/3.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.57/3.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.57/3.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.57/3.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.57/3.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.57/3.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.57/3.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.57/3.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.57/3.63  tff('#skF_5', type, '#skF_5': $i).
% 9.57/3.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.57/3.63  tff('#skF_6', type, '#skF_6': $i).
% 9.57/3.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.57/3.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.57/3.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.57/3.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.57/3.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.57/3.63  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.57/3.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.57/3.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.57/3.63  
% 9.57/3.64  tff(f_78, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 9.57/3.64  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.57/3.64  tff(f_71, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 9.57/3.64  tff(f_63, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 9.57/3.64  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 9.57/3.64  tff(f_61, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 9.57/3.64  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.57/3.64  tff(c_56, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.57/3.64  tff(c_60, plain, (![A_41, B_42, C_43]: (k2_enumset1(A_41, A_41, B_42, C_43)=k1_enumset1(A_41, B_42, C_43))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.57/3.64  tff(c_2025, plain, (![A_2236, B_2237, C_2238, D_2239]: (k2_xboole_0(k2_tarski(A_2236, B_2237), k2_tarski(C_2238, D_2239))=k2_enumset1(A_2236, B_2237, C_2238, D_2239))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.57/3.64  tff(c_2052, plain, (![A_38, C_2238, D_2239]: (k2_xboole_0(k1_tarski(A_38), k2_tarski(C_2238, D_2239))=k2_enumset1(A_38, A_38, C_2238, D_2239))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2025])).
% 9.57/3.64  tff(c_5796, plain, (![A_4730, C_4731, D_4732]: (k2_xboole_0(k1_tarski(A_4730), k2_tarski(C_4731, D_4732))=k1_enumset1(A_4730, C_4731, D_4732))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2052])).
% 9.57/3.64  tff(c_18164, plain, (![A_8556, A_8557]: (k2_xboole_0(k1_tarski(A_8556), k1_tarski(A_8557))=k1_enumset1(A_8556, A_8557, A_8557))), inference(superposition, [status(thm), theory('equality')], [c_56, c_5796])).
% 9.57/3.64  tff(c_66, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.57/3.64  tff(c_18301, plain, (k1_enumset1('#skF_5', '#skF_6', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18164, c_66])).
% 9.57/3.64  tff(c_20, plain, (![E_21, A_15, C_17]: (r2_hidden(E_21, k1_enumset1(A_15, E_21, C_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.57/3.64  tff(c_18475, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_18301, c_20])).
% 9.57/3.64  tff(c_40, plain, (![C_26, A_22]: (C_26=A_22 | ~r2_hidden(C_26, k1_tarski(A_22)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.57/3.64  tff(c_18517, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_18475, c_40])).
% 9.57/3.64  tff(c_18558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_18517])).
% 9.57/3.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.57/3.64  
% 9.57/3.64  Inference rules
% 9.57/3.64  ----------------------
% 9.57/3.64  #Ref     : 0
% 9.57/3.64  #Sup     : 3828
% 9.57/3.64  #Fact    : 12
% 9.57/3.64  #Define  : 0
% 9.57/3.64  #Split   : 6
% 9.57/3.64  #Chain   : 0
% 9.57/3.64  #Close   : 0
% 9.57/3.64  
% 9.57/3.64  Ordering : KBO
% 9.57/3.64  
% 9.57/3.64  Simplification rules
% 9.57/3.64  ----------------------
% 9.57/3.64  #Subsume      : 251
% 9.57/3.64  #Demod        : 3627
% 9.57/3.64  #Tautology    : 2287
% 9.57/3.64  #SimpNegUnit  : 3
% 9.57/3.64  #BackRed      : 4
% 9.57/3.64  
% 9.57/3.64  #Partial instantiations: 3332
% 9.57/3.64  #Strategies tried      : 1
% 9.57/3.64  
% 9.57/3.64  Timing (in seconds)
% 9.57/3.64  ----------------------
% 9.57/3.64  Preprocessing        : 0.32
% 9.57/3.64  Parsing              : 0.16
% 9.57/3.65  CNF conversion       : 0.02
% 9.57/3.65  Main loop            : 2.54
% 9.57/3.65  Inferencing          : 0.72
% 9.57/3.65  Reduction            : 1.25
% 9.57/3.65  Demodulation         : 1.09
% 9.57/3.65  BG Simplification    : 0.07
% 9.57/3.65  Subsumption          : 0.36
% 9.57/3.65  Abstraction          : 0.11
% 9.57/3.65  MUC search           : 0.00
% 9.57/3.65  Cooper               : 0.00
% 9.57/3.65  Total                : 2.88
% 9.57/3.65  Index Insertion      : 0.00
% 9.57/3.65  Index Deletion       : 0.00
% 9.57/3.65  Index Matching       : 0.00
% 9.57/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
