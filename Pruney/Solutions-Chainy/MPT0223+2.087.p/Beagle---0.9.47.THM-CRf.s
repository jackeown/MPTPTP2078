%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:27 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  42 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_26,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_44,plain,(
    ! [D_20,B_21] : r2_hidden(D_20,k2_tarski(D_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_47,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_44])).

tff(c_32,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(k1_tarski(A_17),k1_tarski(B_18))
      | B_18 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_83,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_33,k3_xboole_0(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [C_33] :
      ( ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5'))
      | ~ r2_hidden(C_33,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_83])).

tff(c_107,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_110,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_107])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_110])).

tff(c_117,plain,(
    ! [C_39] : ~ r2_hidden(C_39,k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_122,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_47,c_117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:41:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.12  
% 1.74/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.13  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.74/1.13  
% 1.74/1.13  %Foreground sorts:
% 1.74/1.13  
% 1.74/1.13  
% 1.74/1.13  %Background operators:
% 1.74/1.13  
% 1.74/1.13  
% 1.74/1.13  %Foreground operators:
% 1.74/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.74/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.74/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.74/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.74/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.74/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.74/1.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.74/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.74/1.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.74/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.74/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.74/1.13  
% 1.74/1.13  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.74/1.13  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.74/1.13  tff(f_64, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.74/1.13  tff(f_59, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.74/1.13  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.74/1.13  tff(c_26, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.74/1.13  tff(c_44, plain, (![D_20, B_21]: (r2_hidden(D_20, k2_tarski(D_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.74/1.13  tff(c_47, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_44])).
% 1.74/1.13  tff(c_32, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.74/1.13  tff(c_30, plain, (![A_17, B_18]: (r1_xboole_0(k1_tarski(A_17), k1_tarski(B_18)) | B_18=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.74/1.13  tff(c_34, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.74/1.13  tff(c_83, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r2_hidden(C_33, k3_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.74/1.13  tff(c_86, plain, (![C_33]: (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')) | ~r2_hidden(C_33, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_83])).
% 1.74/1.13  tff(c_107, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_86])).
% 1.74/1.13  tff(c_110, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_30, c_107])).
% 1.74/1.13  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_110])).
% 1.74/1.13  tff(c_117, plain, (![C_39]: (~r2_hidden(C_39, k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_86])).
% 1.74/1.13  tff(c_122, plain, $false, inference(resolution, [status(thm)], [c_47, c_117])).
% 1.74/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.13  
% 1.74/1.13  Inference rules
% 1.74/1.13  ----------------------
% 1.74/1.13  #Ref     : 0
% 1.74/1.13  #Sup     : 19
% 1.74/1.13  #Fact    : 0
% 1.74/1.13  #Define  : 0
% 1.74/1.13  #Split   : 1
% 1.74/1.13  #Chain   : 0
% 1.74/1.14  #Close   : 0
% 1.74/1.14  
% 1.74/1.14  Ordering : KBO
% 1.74/1.14  
% 1.74/1.14  Simplification rules
% 1.74/1.14  ----------------------
% 1.74/1.14  #Subsume      : 0
% 1.74/1.14  #Demod        : 1
% 1.74/1.14  #Tautology    : 12
% 1.74/1.14  #SimpNegUnit  : 1
% 1.74/1.14  #BackRed      : 0
% 1.74/1.14  
% 1.74/1.14  #Partial instantiations: 0
% 1.74/1.14  #Strategies tried      : 1
% 1.74/1.14  
% 1.74/1.14  Timing (in seconds)
% 1.74/1.14  ----------------------
% 1.74/1.14  Preprocessing        : 0.29
% 1.74/1.14  Parsing              : 0.15
% 1.74/1.14  CNF conversion       : 0.02
% 1.74/1.14  Main loop            : 0.11
% 1.74/1.14  Inferencing          : 0.04
% 1.74/1.14  Reduction            : 0.03
% 1.74/1.14  Demodulation         : 0.03
% 1.74/1.14  BG Simplification    : 0.01
% 1.74/1.14  Subsumption          : 0.02
% 1.74/1.14  Abstraction          : 0.01
% 1.74/1.14  MUC search           : 0.00
% 1.74/1.14  Cooper               : 0.00
% 1.74/1.14  Total                : 0.42
% 1.74/1.14  Index Insertion      : 0.00
% 1.74/1.14  Index Deletion       : 0.00
% 1.74/1.14  Index Matching       : 0.00
% 1.74/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
