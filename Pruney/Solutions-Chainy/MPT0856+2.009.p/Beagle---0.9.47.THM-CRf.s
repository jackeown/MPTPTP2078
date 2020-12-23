%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:53 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  65 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_ordinal1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_36,plain,(
    ! [A_19] : r2_hidden(A_19,k1_ordinal1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5')
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_65,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_165,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden(A_62,k4_xboole_0(B_63,k1_tarski(C_64)))
      | C_64 = A_62
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_109,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden(k1_mcart_1(A_45),B_46)
      | ~ r2_hidden(A_45,k2_zfmisc_1(B_46,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_112,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_109])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(k1_tarski(A_13),B_14) = B_14
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    ! [D_32,A_33,B_34] :
      ( ~ r2_hidden(D_32,A_33)
      | r2_hidden(D_32,k2_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_130,plain,(
    ! [D_54,A_55,B_56] :
      ( ~ r2_hidden(D_54,k1_tarski(A_55))
      | r2_hidden(D_54,B_56)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_92])).

tff(c_134,plain,(
    ! [B_57] :
      ( r2_hidden(k1_mcart_1('#skF_3'),B_57)
      | ~ r2_hidden('#skF_4',B_57) ) ),
    inference(resolution,[status(thm)],[c_112,c_130])).

tff(c_30,plain,(
    ! [C_17,B_16] : ~ r2_hidden(C_17,k4_xboole_0(B_16,k1_tarski(C_17))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_161,plain,(
    ! [B_16] : ~ r2_hidden('#skF_4',k4_xboole_0(B_16,k1_tarski(k1_mcart_1('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_134,c_30])).

tff(c_173,plain,(
    ! [B_63] :
      ( k1_mcart_1('#skF_3') = '#skF_4'
      | ~ r2_hidden('#skF_4',B_63) ) ),
    inference(resolution,[status(thm)],[c_165,c_161])).

tff(c_188,plain,(
    ! [B_65] : ~ r2_hidden('#skF_4',B_65) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_173])).

tff(c_213,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_36,c_188])).

tff(c_214,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_262,plain,(
    ! [A_80,C_81,B_82] :
      ( r2_hidden(k2_mcart_1(A_80),C_81)
      | ~ r2_hidden(A_80,k2_zfmisc_1(B_82,C_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_264,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_262])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.25  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_ordinal1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.08/1.25  
% 2.08/1.25  %Foreground sorts:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Background operators:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Foreground operators:
% 2.08/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.08/1.25  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.25  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.08/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.25  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.08/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.25  
% 2.08/1.26  tff(f_55, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.08/1.26  tff(f_68, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 2.08/1.26  tff(f_51, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.08/1.26  tff(f_61, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.08/1.26  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.08/1.26  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.08/1.26  tff(c_36, plain, (![A_19]: (r2_hidden(A_19, k1_ordinal1(A_19)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.08/1.26  tff(c_42, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5') | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.26  tff(c_65, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_42])).
% 2.08/1.26  tff(c_165, plain, (![A_62, B_63, C_64]: (r2_hidden(A_62, k4_xboole_0(B_63, k1_tarski(C_64))) | C_64=A_62 | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.26  tff(c_44, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.26  tff(c_109, plain, (![A_45, B_46, C_47]: (r2_hidden(k1_mcart_1(A_45), B_46) | ~r2_hidden(A_45, k2_zfmisc_1(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.26  tff(c_112, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_109])).
% 2.08/1.26  tff(c_26, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), B_14)=B_14 | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.26  tff(c_92, plain, (![D_32, A_33, B_34]: (~r2_hidden(D_32, A_33) | r2_hidden(D_32, k2_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.08/1.26  tff(c_130, plain, (![D_54, A_55, B_56]: (~r2_hidden(D_54, k1_tarski(A_55)) | r2_hidden(D_54, B_56) | ~r2_hidden(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_26, c_92])).
% 2.08/1.26  tff(c_134, plain, (![B_57]: (r2_hidden(k1_mcart_1('#skF_3'), B_57) | ~r2_hidden('#skF_4', B_57))), inference(resolution, [status(thm)], [c_112, c_130])).
% 2.08/1.26  tff(c_30, plain, (![C_17, B_16]: (~r2_hidden(C_17, k4_xboole_0(B_16, k1_tarski(C_17))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.26  tff(c_161, plain, (![B_16]: (~r2_hidden('#skF_4', k4_xboole_0(B_16, k1_tarski(k1_mcart_1('#skF_3')))))), inference(resolution, [status(thm)], [c_134, c_30])).
% 2.08/1.26  tff(c_173, plain, (![B_63]: (k1_mcart_1('#skF_3')='#skF_4' | ~r2_hidden('#skF_4', B_63))), inference(resolution, [status(thm)], [c_165, c_161])).
% 2.08/1.26  tff(c_188, plain, (![B_65]: (~r2_hidden('#skF_4', B_65))), inference(negUnitSimplification, [status(thm)], [c_65, c_173])).
% 2.08/1.26  tff(c_213, plain, $false, inference(resolution, [status(thm)], [c_36, c_188])).
% 2.08/1.26  tff(c_214, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 2.08/1.26  tff(c_262, plain, (![A_80, C_81, B_82]: (r2_hidden(k2_mcart_1(A_80), C_81) | ~r2_hidden(A_80, k2_zfmisc_1(B_82, C_81)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.26  tff(c_264, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_44, c_262])).
% 2.08/1.26  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_264])).
% 2.08/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  Inference rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Ref     : 0
% 2.08/1.26  #Sup     : 48
% 2.08/1.26  #Fact    : 0
% 2.08/1.26  #Define  : 0
% 2.08/1.26  #Split   : 1
% 2.08/1.26  #Chain   : 0
% 2.08/1.26  #Close   : 0
% 2.08/1.26  
% 2.08/1.26  Ordering : KBO
% 2.08/1.26  
% 2.08/1.26  Simplification rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Subsume      : 9
% 2.08/1.26  #Demod        : 0
% 2.08/1.26  #Tautology    : 20
% 2.08/1.26  #SimpNegUnit  : 2
% 2.08/1.26  #BackRed      : 0
% 2.08/1.26  
% 2.08/1.26  #Partial instantiations: 0
% 2.08/1.26  #Strategies tried      : 1
% 2.08/1.26  
% 2.08/1.26  Timing (in seconds)
% 2.08/1.26  ----------------------
% 2.08/1.27  Preprocessing        : 0.30
% 2.08/1.27  Parsing              : 0.15
% 2.08/1.27  CNF conversion       : 0.02
% 2.08/1.27  Main loop            : 0.19
% 2.08/1.27  Inferencing          : 0.07
% 2.08/1.27  Reduction            : 0.05
% 2.08/1.27  Demodulation         : 0.03
% 2.08/1.27  BG Simplification    : 0.01
% 2.08/1.27  Subsumption          : 0.03
% 2.08/1.27  Abstraction          : 0.01
% 2.08/1.27  MUC search           : 0.00
% 2.08/1.27  Cooper               : 0.00
% 2.08/1.27  Total                : 0.51
% 2.08/1.27  Index Insertion      : 0.00
% 2.08/1.27  Index Deletion       : 0.00
% 2.08/1.27  Index Matching       : 0.00
% 2.08/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
