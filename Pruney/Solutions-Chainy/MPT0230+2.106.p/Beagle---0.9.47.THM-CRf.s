%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:09 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   42 (  46 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  58 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_56,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_71,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_89,plain,(
    ! [B_38,A_39] : r2_hidden(B_38,k2_tarski(A_39,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_24])).

tff(c_92,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_89])).

tff(c_58,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_97,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_93])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_122,plain,(
    ! [D_6] :
      ( r2_hidden(D_6,k2_tarski('#skF_6','#skF_7'))
      | ~ r2_hidden(D_6,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_4])).

tff(c_48,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_148,plain,(
    ! [E_62,C_63,B_64,A_65] :
      ( E_62 = C_63
      | E_62 = B_64
      | E_62 = A_65
      | ~ r2_hidden(E_62,k1_enumset1(A_65,B_64,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_167,plain,(
    ! [E_66,B_67,A_68] :
      ( E_66 = B_67
      | E_66 = A_68
      | E_66 = A_68
      | ~ r2_hidden(E_66,k2_tarski(A_68,B_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_148])).

tff(c_185,plain,(
    ! [D_69] :
      ( D_69 = '#skF_7'
      | D_69 = '#skF_6'
      | ~ r2_hidden(D_69,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_122,c_167])).

tff(c_189,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_92,c_185])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.26  
% 2.05/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.26  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.05/1.26  
% 2.05/1.26  %Foreground sorts:
% 2.05/1.26  
% 2.05/1.26  
% 2.05/1.26  %Background operators:
% 2.05/1.26  
% 2.05/1.26  
% 2.05/1.26  %Foreground operators:
% 2.05/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.05/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.05/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.05/1.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.05/1.26  
% 2.05/1.27  tff(f_71, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.05/1.27  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.05/1.27  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.05/1.27  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.05/1.27  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.05/1.27  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.05/1.27  tff(c_56, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.27  tff(c_54, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.27  tff(c_46, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.05/1.27  tff(c_71, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.05/1.27  tff(c_24, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.05/1.27  tff(c_89, plain, (![B_38, A_39]: (r2_hidden(B_38, k2_tarski(A_39, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_24])).
% 2.05/1.27  tff(c_92, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_89])).
% 2.05/1.27  tff(c_58, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.27  tff(c_93, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.05/1.27  tff(c_97, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_58, c_93])).
% 2.05/1.27  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.05/1.27  tff(c_122, plain, (![D_6]: (r2_hidden(D_6, k2_tarski('#skF_6', '#skF_7')) | ~r2_hidden(D_6, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_97, c_4])).
% 2.05/1.27  tff(c_48, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.05/1.27  tff(c_148, plain, (![E_62, C_63, B_64, A_65]: (E_62=C_63 | E_62=B_64 | E_62=A_65 | ~r2_hidden(E_62, k1_enumset1(A_65, B_64, C_63)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.05/1.27  tff(c_167, plain, (![E_66, B_67, A_68]: (E_66=B_67 | E_66=A_68 | E_66=A_68 | ~r2_hidden(E_66, k2_tarski(A_68, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_148])).
% 2.05/1.27  tff(c_185, plain, (![D_69]: (D_69='#skF_7' | D_69='#skF_6' | ~r2_hidden(D_69, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_122, c_167])).
% 2.05/1.27  tff(c_189, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_92, c_185])).
% 2.05/1.27  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_189])).
% 2.05/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.27  
% 2.05/1.27  Inference rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Ref     : 0
% 2.05/1.27  #Sup     : 30
% 2.05/1.27  #Fact    : 0
% 2.05/1.27  #Define  : 0
% 2.05/1.27  #Split   : 0
% 2.05/1.27  #Chain   : 0
% 2.05/1.27  #Close   : 0
% 2.05/1.27  
% 2.05/1.27  Ordering : KBO
% 2.05/1.27  
% 2.05/1.27  Simplification rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Subsume      : 0
% 2.05/1.27  #Demod        : 2
% 2.05/1.27  #Tautology    : 21
% 2.05/1.27  #SimpNegUnit  : 1
% 2.05/1.27  #BackRed      : 0
% 2.05/1.27  
% 2.05/1.27  #Partial instantiations: 0
% 2.05/1.27  #Strategies tried      : 1
% 2.05/1.27  
% 2.05/1.27  Timing (in seconds)
% 2.05/1.27  ----------------------
% 2.05/1.27  Preprocessing        : 0.30
% 2.05/1.27  Parsing              : 0.14
% 2.05/1.27  CNF conversion       : 0.02
% 2.05/1.27  Main loop            : 0.16
% 2.05/1.27  Inferencing          : 0.05
% 2.05/1.27  Reduction            : 0.05
% 2.05/1.27  Demodulation         : 0.04
% 2.05/1.27  BG Simplification    : 0.02
% 2.05/1.27  Subsumption          : 0.03
% 2.05/1.27  Abstraction          : 0.01
% 2.05/1.27  MUC search           : 0.00
% 2.05/1.28  Cooper               : 0.00
% 2.05/1.28  Total                : 0.48
% 2.05/1.28  Index Insertion      : 0.00
% 2.05/1.28  Index Deletion       : 0.00
% 2.05/1.28  Index Matching       : 0.00
% 2.05/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
