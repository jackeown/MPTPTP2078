%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:59 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  60 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_36,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_115,plain,(
    ! [C_72,A_73] :
      ( r2_hidden(k4_tarski(C_72,'#skF_6'(A_73,k1_relat_1(A_73),C_72)),A_73)
      | ~ r2_hidden(C_72,k1_relat_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_47,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,k3_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    ! [A_8,C_53] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_53,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_47])).

tff(c_57,plain,(
    ! [C_53] : ~ r2_hidden(C_53,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_54])).

tff(c_149,plain,(
    ! [C_74] : ~ r2_hidden(C_74,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_115,c_57])).

tff(c_161,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_149])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_161])).

tff(c_168,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_252,plain,(
    ! [A_96,C_97] :
      ( r2_hidden(k4_tarski('#skF_10'(A_96,k2_relat_1(A_96),C_97),C_97),A_96)
      | ~ r2_hidden(C_97,k2_relat_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_174,plain,(
    ! [A_75,B_76,C_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | ~ r2_hidden(C_77,k3_xboole_0(A_75,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_181,plain,(
    ! [A_8,C_77] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_77,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_174])).

tff(c_184,plain,(
    ! [C_77] : ~ r2_hidden(C_77,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_181])).

tff(c_276,plain,(
    ! [C_98] : ~ r2_hidden(C_98,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_252,c_184])).

tff(c_288,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_276])).

tff(c_294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.23  
% 1.79/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.24  %$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4 > #skF_10
% 1.79/1.24  
% 1.79/1.24  %Foreground sorts:
% 1.79/1.24  
% 1.79/1.24  
% 1.79/1.24  %Background operators:
% 1.79/1.24  
% 1.79/1.24  
% 1.79/1.24  %Foreground operators:
% 1.79/1.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.79/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.24  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.79/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.79/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.79/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.79/1.24  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 1.79/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.24  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.79/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.24  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 1.79/1.24  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.79/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.79/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.79/1.24  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 1.79/1.24  
% 1.99/1.24  tff(f_71, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.99/1.24  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.99/1.24  tff(f_59, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.99/1.24  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.99/1.24  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.99/1.24  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.99/1.25  tff(f_67, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 1.99/1.25  tff(c_36, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.99/1.25  tff(c_46, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 1.99/1.25  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.25  tff(c_115, plain, (![C_72, A_73]: (r2_hidden(k4_tarski(C_72, '#skF_6'(A_73, k1_relat_1(A_73), C_72)), A_73) | ~r2_hidden(C_72, k1_relat_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.25  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.25  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.99/1.25  tff(c_47, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, k3_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.25  tff(c_54, plain, (![A_8, C_53]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_47])).
% 1.99/1.25  tff(c_57, plain, (![C_53]: (~r2_hidden(C_53, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_54])).
% 1.99/1.25  tff(c_149, plain, (![C_74]: (~r2_hidden(C_74, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_115, c_57])).
% 1.99/1.25  tff(c_161, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_149])).
% 1.99/1.25  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_161])).
% 1.99/1.25  tff(c_168, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 1.99/1.25  tff(c_252, plain, (![A_96, C_97]: (r2_hidden(k4_tarski('#skF_10'(A_96, k2_relat_1(A_96), C_97), C_97), A_96) | ~r2_hidden(C_97, k2_relat_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.99/1.25  tff(c_174, plain, (![A_75, B_76, C_77]: (~r1_xboole_0(A_75, B_76) | ~r2_hidden(C_77, k3_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.25  tff(c_181, plain, (![A_8, C_77]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_174])).
% 1.99/1.25  tff(c_184, plain, (![C_77]: (~r2_hidden(C_77, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_181])).
% 1.99/1.25  tff(c_276, plain, (![C_98]: (~r2_hidden(C_98, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_252, c_184])).
% 1.99/1.25  tff(c_288, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_276])).
% 1.99/1.25  tff(c_294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_288])).
% 1.99/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  Inference rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Ref     : 0
% 1.99/1.25  #Sup     : 49
% 1.99/1.25  #Fact    : 0
% 1.99/1.25  #Define  : 0
% 1.99/1.25  #Split   : 1
% 1.99/1.25  #Chain   : 0
% 1.99/1.25  #Close   : 0
% 1.99/1.25  
% 1.99/1.25  Ordering : KBO
% 1.99/1.25  
% 1.99/1.25  Simplification rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Subsume      : 5
% 1.99/1.25  #Demod        : 12
% 1.99/1.25  #Tautology    : 18
% 1.99/1.25  #SimpNegUnit  : 6
% 1.99/1.25  #BackRed      : 1
% 1.99/1.25  
% 1.99/1.25  #Partial instantiations: 0
% 1.99/1.25  #Strategies tried      : 1
% 1.99/1.25  
% 1.99/1.25  Timing (in seconds)
% 1.99/1.25  ----------------------
% 1.99/1.25  Preprocessing        : 0.28
% 1.99/1.25  Parsing              : 0.15
% 1.99/1.25  CNF conversion       : 0.03
% 1.99/1.25  Main loop            : 0.17
% 1.99/1.25  Inferencing          : 0.07
% 1.99/1.25  Reduction            : 0.04
% 1.99/1.25  Demodulation         : 0.03
% 1.99/1.25  BG Simplification    : 0.01
% 1.99/1.25  Subsumption          : 0.03
% 1.99/1.25  Abstraction          : 0.01
% 1.99/1.25  MUC search           : 0.00
% 1.99/1.25  Cooper               : 0.00
% 1.99/1.25  Total                : 0.48
% 1.99/1.25  Index Insertion      : 0.00
% 1.99/1.25  Index Deletion       : 0.00
% 1.99/1.25  Index Matching       : 0.00
% 1.99/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
