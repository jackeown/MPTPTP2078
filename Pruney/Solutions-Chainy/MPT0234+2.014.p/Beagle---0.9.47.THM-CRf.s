%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:43 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   44 (  47 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   43 (  47 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_63,plain,(
    ! [A_24,B_25] : k4_xboole_0(k1_tarski(A_24),k2_tarski(A_24,B_25)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70,plain,(
    ! [A_13] : k4_xboole_0(k1_tarski(A_13),k1_tarski(A_13)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_63])).

tff(c_28,plain,(
    ! [B_15,C_16] :
      ( k4_xboole_0(k2_tarski(B_15,B_15),C_16) = k1_tarski(B_15)
      | r2_hidden(B_15,C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_154,plain,(
    ! [B_33,C_34] :
      ( k4_xboole_0(k1_tarski(B_33),C_34) = k1_tarski(B_33)
      | r2_hidden(B_33,C_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28])).

tff(c_6,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_164,plain,(
    ! [B_33,C_34] :
      ( k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) = k3_xboole_0(k1_tarski(B_33),C_34)
      | r2_hidden(B_33,C_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_6])).

tff(c_204,plain,(
    ! [B_33,C_34] :
      ( k3_xboole_0(k1_tarski(B_33),C_34) = k1_xboole_0
      | r2_hidden(B_33,C_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_164])).

tff(c_362,plain,(
    ! [A_50,B_51] : k4_xboole_0(k2_xboole_0(A_50,B_51),k3_xboole_0(A_50,B_51)) = k5_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_374,plain,(
    ! [B_33,C_34] :
      ( k4_xboole_0(k2_xboole_0(k1_tarski(B_33),C_34),k1_xboole_0) = k5_xboole_0(k1_tarski(B_33),C_34)
      | r2_hidden(B_33,C_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_362])).

tff(c_579,plain,(
    ! [B_68,C_69] :
      ( k5_xboole_0(k1_tarski(B_68),C_69) = k2_xboole_0(k1_tarski(B_68),C_69)
      | r2_hidden(B_68,C_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_374])).

tff(c_34,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_593,plain,
    ( k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4')
    | r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_34])).

tff(c_609,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_593])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_617,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_609,c_8])).

tff(c_621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:35:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.28  
% 2.24/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.28  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.24/1.28  
% 2.24/1.28  %Foreground sorts:
% 2.24/1.28  
% 2.24/1.28  
% 2.24/1.28  %Background operators:
% 2.24/1.28  
% 2.24/1.28  
% 2.24/1.28  %Foreground operators:
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.24/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.24/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.28  
% 2.24/1.29  tff(f_59, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.24/1.29  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.24/1.29  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.24/1.29  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.24/1.29  tff(f_53, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.24/1.29  tff(f_51, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.24/1.29  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.24/1.29  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_xboole_1)).
% 2.24/1.29  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.24/1.29  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.29  tff(c_20, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.24/1.29  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.29  tff(c_22, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.29  tff(c_63, plain, (![A_24, B_25]: (k4_xboole_0(k1_tarski(A_24), k2_tarski(A_24, B_25))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.29  tff(c_70, plain, (![A_13]: (k4_xboole_0(k1_tarski(A_13), k1_tarski(A_13))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_63])).
% 2.24/1.29  tff(c_28, plain, (![B_15, C_16]: (k4_xboole_0(k2_tarski(B_15, B_15), C_16)=k1_tarski(B_15) | r2_hidden(B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.29  tff(c_154, plain, (![B_33, C_34]: (k4_xboole_0(k1_tarski(B_33), C_34)=k1_tarski(B_33) | r2_hidden(B_33, C_34))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28])).
% 2.24/1.29  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.29  tff(c_164, plain, (![B_33, C_34]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))=k3_xboole_0(k1_tarski(B_33), C_34) | r2_hidden(B_33, C_34))), inference(superposition, [status(thm), theory('equality')], [c_154, c_6])).
% 2.24/1.29  tff(c_204, plain, (![B_33, C_34]: (k3_xboole_0(k1_tarski(B_33), C_34)=k1_xboole_0 | r2_hidden(B_33, C_34))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_164])).
% 2.24/1.29  tff(c_362, plain, (![A_50, B_51]: (k4_xboole_0(k2_xboole_0(A_50, B_51), k3_xboole_0(A_50, B_51))=k5_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.29  tff(c_374, plain, (![B_33, C_34]: (k4_xboole_0(k2_xboole_0(k1_tarski(B_33), C_34), k1_xboole_0)=k5_xboole_0(k1_tarski(B_33), C_34) | r2_hidden(B_33, C_34))), inference(superposition, [status(thm), theory('equality')], [c_204, c_362])).
% 2.24/1.29  tff(c_579, plain, (![B_68, C_69]: (k5_xboole_0(k1_tarski(B_68), C_69)=k2_xboole_0(k1_tarski(B_68), C_69) | r2_hidden(B_68, C_69))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_374])).
% 2.24/1.29  tff(c_34, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.29  tff(c_593, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4') | r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_579, c_34])).
% 2.24/1.29  tff(c_609, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_593])).
% 2.24/1.29  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.24/1.29  tff(c_617, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_609, c_8])).
% 2.24/1.29  tff(c_621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_617])).
% 2.24/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.29  
% 2.24/1.29  Inference rules
% 2.24/1.29  ----------------------
% 2.24/1.29  #Ref     : 0
% 2.24/1.29  #Sup     : 134
% 2.24/1.29  #Fact    : 0
% 2.24/1.29  #Define  : 0
% 2.24/1.29  #Split   : 0
% 2.24/1.29  #Chain   : 0
% 2.24/1.29  #Close   : 0
% 2.24/1.29  
% 2.24/1.29  Ordering : KBO
% 2.24/1.29  
% 2.24/1.29  Simplification rules
% 2.24/1.29  ----------------------
% 2.24/1.29  #Subsume      : 9
% 2.24/1.29  #Demod        : 88
% 2.24/1.29  #Tautology    : 86
% 2.24/1.29  #SimpNegUnit  : 11
% 2.24/1.29  #BackRed      : 1
% 2.24/1.29  
% 2.24/1.29  #Partial instantiations: 0
% 2.24/1.29  #Strategies tried      : 1
% 2.24/1.29  
% 2.24/1.29  Timing (in seconds)
% 2.24/1.29  ----------------------
% 2.24/1.30  Preprocessing        : 0.30
% 2.24/1.30  Parsing              : 0.16
% 2.24/1.30  CNF conversion       : 0.02
% 2.24/1.30  Main loop            : 0.25
% 2.24/1.30  Inferencing          : 0.10
% 2.24/1.30  Reduction            : 0.09
% 2.24/1.30  Demodulation         : 0.06
% 2.24/1.30  BG Simplification    : 0.01
% 2.24/1.30  Subsumption          : 0.04
% 2.24/1.30  Abstraction          : 0.01
% 2.24/1.30  MUC search           : 0.00
% 2.24/1.30  Cooper               : 0.00
% 2.24/1.30  Total                : 0.57
% 2.24/1.30  Index Insertion      : 0.00
% 2.24/1.30  Index Deletion       : 0.00
% 2.24/1.30  Index Matching       : 0.00
% 2.24/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
