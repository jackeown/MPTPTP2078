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
% DateTime   : Thu Dec  3 09:49:11 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  97 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_28,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ! [B_31,A_32] :
      ( ~ r2_hidden(B_31,A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [C_17] : ~ v1_xboole_0(k1_tarski(C_17)) ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_64,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_62,plain,(
    '#skF_10' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_110,plain,(
    ! [A_43] :
      ( v1_xboole_0(A_43)
      | r2_hidden('#skF_1'(A_43),A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_114,plain,(
    ! [A_13] :
      ( '#skF_1'(k1_tarski(A_13)) = A_13
      | v1_xboole_0(k1_tarski(A_13)) ) ),
    inference(resolution,[status(thm)],[c_110,c_26])).

tff(c_120,plain,(
    ! [A_13] : '#skF_1'(k1_tarski(A_13)) = A_13 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_114])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    r1_tarski(k1_tarski('#skF_8'),k2_tarski('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_145,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_149,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k2_tarski('#skF_9','#skF_10')) = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_145])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_165,plain,(
    ! [D_10] :
      ( r2_hidden(D_10,k2_tarski('#skF_9','#skF_10'))
      | ~ r2_hidden(D_10,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_8])).

tff(c_186,plain,(
    ! [D_59,B_60,A_61] :
      ( D_59 = B_60
      | D_59 = A_61
      | ~ r2_hidden(D_59,k2_tarski(A_61,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_211,plain,(
    ! [D_62] :
      ( D_62 = '#skF_10'
      | D_62 = '#skF_9'
      | ~ r2_hidden(D_62,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_165,c_186])).

tff(c_215,plain,
    ( '#skF_1'(k1_tarski('#skF_8')) = '#skF_10'
    | '#skF_1'(k1_tarski('#skF_8')) = '#skF_9'
    | v1_xboole_0(k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_4,c_211])).

tff(c_221,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_9' = '#skF_8'
    | v1_xboole_0(k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_120,c_215])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_64,c_62,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:33:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.65  
% 2.52/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.65  %$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 2.52/1.65  
% 2.52/1.65  %Foreground sorts:
% 2.52/1.65  
% 2.52/1.65  
% 2.52/1.65  %Background operators:
% 2.52/1.65  
% 2.52/1.65  
% 2.52/1.65  %Foreground operators:
% 2.52/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.65  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.52/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.52/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.65  tff('#skF_10', type, '#skF_10': $i).
% 2.52/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.52/1.65  tff('#skF_9', type, '#skF_9': $i).
% 2.52/1.65  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.52/1.65  tff('#skF_8', type, '#skF_8': $i).
% 2.52/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.52/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.52/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.52/1.65  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.52/1.65  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.52/1.65  
% 2.52/1.67  tff(f_51, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.52/1.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.52/1.67  tff(f_76, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.52/1.67  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.52/1.67  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.52/1.67  tff(f_60, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.52/1.67  tff(c_28, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.52/1.67  tff(c_68, plain, (![B_31, A_32]: (~r2_hidden(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.67  tff(c_72, plain, (![C_17]: (~v1_xboole_0(k1_tarski(C_17)))), inference(resolution, [status(thm)], [c_28, c_68])).
% 2.52/1.67  tff(c_64, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.67  tff(c_62, plain, ('#skF_10'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.67  tff(c_110, plain, (![A_43]: (v1_xboole_0(A_43) | r2_hidden('#skF_1'(A_43), A_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.67  tff(c_26, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.52/1.67  tff(c_114, plain, (![A_13]: ('#skF_1'(k1_tarski(A_13))=A_13 | v1_xboole_0(k1_tarski(A_13)))), inference(resolution, [status(thm)], [c_110, c_26])).
% 2.52/1.67  tff(c_120, plain, (![A_13]: ('#skF_1'(k1_tarski(A_13))=A_13)), inference(negUnitSimplification, [status(thm)], [c_72, c_114])).
% 2.52/1.67  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.67  tff(c_66, plain, (r1_tarski(k1_tarski('#skF_8'), k2_tarski('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.67  tff(c_145, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.52/1.67  tff(c_149, plain, (k3_xboole_0(k1_tarski('#skF_8'), k2_tarski('#skF_9', '#skF_10'))=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_66, c_145])).
% 2.52/1.67  tff(c_8, plain, (![D_10, B_6, A_5]: (r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.52/1.67  tff(c_165, plain, (![D_10]: (r2_hidden(D_10, k2_tarski('#skF_9', '#skF_10')) | ~r2_hidden(D_10, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_149, c_8])).
% 2.52/1.67  tff(c_186, plain, (![D_59, B_60, A_61]: (D_59=B_60 | D_59=A_61 | ~r2_hidden(D_59, k2_tarski(A_61, B_60)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.52/1.67  tff(c_211, plain, (![D_62]: (D_62='#skF_10' | D_62='#skF_9' | ~r2_hidden(D_62, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_165, c_186])).
% 2.52/1.67  tff(c_215, plain, ('#skF_1'(k1_tarski('#skF_8'))='#skF_10' | '#skF_1'(k1_tarski('#skF_8'))='#skF_9' | v1_xboole_0(k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_4, c_211])).
% 2.52/1.67  tff(c_221, plain, ('#skF_10'='#skF_8' | '#skF_9'='#skF_8' | v1_xboole_0(k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_120, c_215])).
% 2.52/1.67  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_64, c_62, c_221])).
% 2.52/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.67  
% 2.52/1.67  Inference rules
% 2.52/1.67  ----------------------
% 2.52/1.67  #Ref     : 0
% 2.52/1.67  #Sup     : 33
% 2.52/1.67  #Fact    : 0
% 2.52/1.67  #Define  : 0
% 2.52/1.67  #Split   : 0
% 2.52/1.67  #Chain   : 0
% 2.52/1.67  #Close   : 0
% 2.52/1.67  
% 2.52/1.67  Ordering : KBO
% 2.52/1.67  
% 2.52/1.67  Simplification rules
% 2.52/1.67  ----------------------
% 2.52/1.67  #Subsume      : 4
% 2.52/1.67  #Demod        : 5
% 2.52/1.67  #Tautology    : 18
% 2.52/1.67  #SimpNegUnit  : 4
% 2.52/1.67  #BackRed      : 0
% 2.52/1.67  
% 2.52/1.67  #Partial instantiations: 0
% 2.52/1.67  #Strategies tried      : 1
% 2.52/1.67  
% 2.52/1.67  Timing (in seconds)
% 2.52/1.67  ----------------------
% 2.52/1.67  Preprocessing        : 0.50
% 2.52/1.67  Parsing              : 0.24
% 2.52/1.68  CNF conversion       : 0.04
% 2.52/1.68  Main loop            : 0.26
% 2.52/1.68  Inferencing          : 0.08
% 2.52/1.68  Reduction            : 0.09
% 2.52/1.68  Demodulation         : 0.07
% 2.52/1.68  BG Simplification    : 0.03
% 2.52/1.68  Subsumption          : 0.05
% 2.52/1.68  Abstraction          : 0.01
% 2.52/1.68  MUC search           : 0.00
% 2.52/1.68  Cooper               : 0.00
% 2.52/1.68  Total                : 0.81
% 2.52/1.68  Index Insertion      : 0.00
% 2.52/1.68  Index Deletion       : 0.00
% 2.52/1.68  Index Matching       : 0.00
% 2.52/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
