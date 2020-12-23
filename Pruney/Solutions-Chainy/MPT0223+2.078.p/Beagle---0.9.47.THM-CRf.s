%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:26 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  38 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_10,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(k1_tarski(A_14),k1_tarski(B_15))
      | B_15 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,k3_xboole_0(A_22,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [C_24] :
      ( ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5'))
      | ~ r2_hidden(C_24,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_48])).

tff(c_67,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_70,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_67])).

tff(c_74,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_70])).

tff(c_77,plain,(
    ! [C_27] : ~ r2_hidden(C_27,k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_82,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.13  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 1.66/1.13  
% 1.66/1.13  %Foreground sorts:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Background operators:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Foreground operators:
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.66/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.66/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.66/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.66/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.66/1.13  
% 1.66/1.14  tff(f_48, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.66/1.14  tff(f_60, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.66/1.14  tff(f_55, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.66/1.14  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.66/1.14  tff(c_10, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.66/1.14  tff(c_24, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.66/1.14  tff(c_22, plain, (![A_14, B_15]: (r1_xboole_0(k1_tarski(A_14), k1_tarski(B_15)) | B_15=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.66/1.14  tff(c_26, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.66/1.14  tff(c_48, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, k3_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.66/1.14  tff(c_51, plain, (![C_24]: (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')) | ~r2_hidden(C_24, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_26, c_48])).
% 1.66/1.14  tff(c_67, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_51])).
% 1.66/1.14  tff(c_70, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_22, c_67])).
% 1.66/1.14  tff(c_74, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_70])).
% 1.66/1.14  tff(c_77, plain, (![C_27]: (~r2_hidden(C_27, k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_51])).
% 1.66/1.14  tff(c_82, plain, $false, inference(resolution, [status(thm)], [c_10, c_77])).
% 1.66/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  Inference rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Ref     : 0
% 1.66/1.14  #Sup     : 12
% 1.66/1.14  #Fact    : 0
% 1.66/1.14  #Define  : 0
% 1.66/1.14  #Split   : 1
% 1.66/1.14  #Chain   : 0
% 1.66/1.14  #Close   : 0
% 1.66/1.14  
% 1.66/1.14  Ordering : KBO
% 1.66/1.14  
% 1.66/1.14  Simplification rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Subsume      : 0
% 1.66/1.14  #Demod        : 0
% 1.66/1.14  #Tautology    : 7
% 1.66/1.14  #SimpNegUnit  : 1
% 1.66/1.14  #BackRed      : 0
% 1.66/1.14  
% 1.66/1.14  #Partial instantiations: 0
% 1.66/1.14  #Strategies tried      : 1
% 1.66/1.14  
% 1.66/1.14  Timing (in seconds)
% 1.66/1.14  ----------------------
% 1.66/1.14  Preprocessing        : 0.29
% 1.66/1.14  Parsing              : 0.15
% 1.66/1.14  CNF conversion       : 0.02
% 1.66/1.14  Main loop            : 0.09
% 1.66/1.14  Inferencing          : 0.03
% 1.66/1.14  Reduction            : 0.02
% 1.66/1.15  Demodulation         : 0.01
% 1.66/1.15  BG Simplification    : 0.01
% 1.66/1.15  Subsumption          : 0.02
% 1.66/1.15  Abstraction          : 0.00
% 1.66/1.15  MUC search           : 0.00
% 1.66/1.15  Cooper               : 0.00
% 1.66/1.15  Total                : 0.39
% 1.66/1.15  Index Insertion      : 0.00
% 1.66/1.15  Index Deletion       : 0.00
% 1.66/1.15  Index Matching       : 0.00
% 1.66/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
