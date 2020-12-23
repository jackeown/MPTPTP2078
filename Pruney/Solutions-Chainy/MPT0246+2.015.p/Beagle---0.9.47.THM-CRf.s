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
% DateTime   : Thu Dec  3 09:50:02 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  76 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [E_12,B_7,C_8] : r2_hidden(E_12,k1_enumset1(E_12,B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    ! [A_38,B_39] : r2_hidden(A_38,k2_tarski(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_14])).

tff(c_85,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_82])).

tff(c_94,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [C_22] :
      ( C_22 = '#skF_5'
      | ~ r2_hidden(C_22,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_104,plain,(
    ! [B_46] :
      ( '#skF_1'('#skF_4',B_46) = '#skF_5'
      | r1_tarski('#skF_4',B_46) ) ),
    inference(resolution,[status(thm)],[c_94,c_44])).

tff(c_166,plain,(
    ! [B_63,A_64] :
      ( k1_tarski(B_63) = A_64
      | k1_xboole_0 = A_64
      | ~ r1_tarski(A_64,k1_tarski(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_170,plain,(
    ! [B_63] :
      ( k1_tarski(B_63) = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | '#skF_1'('#skF_4',k1_tarski(B_63)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_104,c_166])).

tff(c_185,plain,(
    ! [B_65] :
      ( k1_tarski(B_65) = '#skF_4'
      | '#skF_1'('#skF_4',k1_tarski(B_65)) = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_170])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_335,plain,(
    ! [B_90] :
      ( ~ r2_hidden('#skF_5',k1_tarski(B_90))
      | r1_tarski('#skF_4',k1_tarski(B_90))
      | k1_tarski(B_90) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_4])).

tff(c_345,plain,
    ( r1_tarski('#skF_4',k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_85,c_335])).

tff(c_350,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_345])).

tff(c_38,plain,(
    ! [B_20,A_19] :
      ( k1_tarski(B_20) = A_19
      | k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_tarski(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_355,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_350,c_38])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_48,c_355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:38 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.27  
% 2.04/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.27  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.04/1.27  
% 2.04/1.27  %Foreground sorts:
% 2.04/1.27  
% 2.04/1.27  
% 2.04/1.27  %Background operators:
% 2.04/1.27  
% 2.04/1.27  
% 2.04/1.27  %Foreground operators:
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.04/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.04/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.27  
% 2.04/1.28  tff(f_74, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.04/1.28  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.04/1.28  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.04/1.28  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.04/1.28  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.04/1.28  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.04/1.28  tff(c_46, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.04/1.28  tff(c_48, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.04/1.28  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.28  tff(c_64, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.28  tff(c_14, plain, (![E_12, B_7, C_8]: (r2_hidden(E_12, k1_enumset1(E_12, B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.04/1.28  tff(c_82, plain, (![A_38, B_39]: (r2_hidden(A_38, k2_tarski(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_14])).
% 2.04/1.28  tff(c_85, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_82])).
% 2.04/1.28  tff(c_94, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), A_45) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.28  tff(c_44, plain, (![C_22]: (C_22='#skF_5' | ~r2_hidden(C_22, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.04/1.28  tff(c_104, plain, (![B_46]: ('#skF_1'('#skF_4', B_46)='#skF_5' | r1_tarski('#skF_4', B_46))), inference(resolution, [status(thm)], [c_94, c_44])).
% 2.04/1.28  tff(c_166, plain, (![B_63, A_64]: (k1_tarski(B_63)=A_64 | k1_xboole_0=A_64 | ~r1_tarski(A_64, k1_tarski(B_63)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.28  tff(c_170, plain, (![B_63]: (k1_tarski(B_63)='#skF_4' | k1_xboole_0='#skF_4' | '#skF_1'('#skF_4', k1_tarski(B_63))='#skF_5')), inference(resolution, [status(thm)], [c_104, c_166])).
% 2.04/1.28  tff(c_185, plain, (![B_65]: (k1_tarski(B_65)='#skF_4' | '#skF_1'('#skF_4', k1_tarski(B_65))='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_170])).
% 2.04/1.28  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.28  tff(c_335, plain, (![B_90]: (~r2_hidden('#skF_5', k1_tarski(B_90)) | r1_tarski('#skF_4', k1_tarski(B_90)) | k1_tarski(B_90)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_185, c_4])).
% 2.04/1.28  tff(c_345, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5')) | k1_tarski('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_85, c_335])).
% 2.04/1.28  tff(c_350, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_48, c_345])).
% 2.04/1.28  tff(c_38, plain, (![B_20, A_19]: (k1_tarski(B_20)=A_19 | k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_tarski(B_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.28  tff(c_355, plain, (k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_350, c_38])).
% 2.04/1.28  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_48, c_355])).
% 2.04/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  Inference rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Ref     : 0
% 2.04/1.28  #Sup     : 66
% 2.04/1.28  #Fact    : 0
% 2.04/1.28  #Define  : 0
% 2.04/1.28  #Split   : 2
% 2.04/1.28  #Chain   : 0
% 2.04/1.28  #Close   : 0
% 2.04/1.28  
% 2.04/1.28  Ordering : KBO
% 2.04/1.28  
% 2.04/1.28  Simplification rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Subsume      : 8
% 2.04/1.28  #Demod        : 15
% 2.04/1.28  #Tautology    : 31
% 2.04/1.28  #SimpNegUnit  : 5
% 2.04/1.28  #BackRed      : 0
% 2.04/1.28  
% 2.04/1.28  #Partial instantiations: 0
% 2.04/1.28  #Strategies tried      : 1
% 2.04/1.28  
% 2.04/1.28  Timing (in seconds)
% 2.04/1.28  ----------------------
% 2.04/1.28  Preprocessing        : 0.30
% 2.04/1.28  Parsing              : 0.15
% 2.04/1.28  CNF conversion       : 0.02
% 2.04/1.28  Main loop            : 0.21
% 2.04/1.28  Inferencing          : 0.08
% 2.04/1.28  Reduction            : 0.06
% 2.04/1.28  Demodulation         : 0.05
% 2.04/1.28  BG Simplification    : 0.02
% 2.04/1.28  Subsumption          : 0.04
% 2.04/1.29  Abstraction          : 0.01
% 2.04/1.29  MUC search           : 0.00
% 2.04/1.29  Cooper               : 0.00
% 2.04/1.29  Total                : 0.54
% 2.04/1.29  Index Insertion      : 0.00
% 2.04/1.29  Index Deletion       : 0.00
% 2.04/1.29  Index Matching       : 0.00
% 2.04/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
