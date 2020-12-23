%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:53 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   37 (  62 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_36,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5')
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden(k1_mcart_1(A_36),B_37)
      | ~ r2_hidden(A_36,k2_zfmisc_1(B_37,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_77,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_78,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden(A_39,k4_xboole_0(B_40,k1_tarski(C_41)))
      | C_41 = A_39
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_93,plain,(
    ! [A_42,C_43,B_44] :
      ( ~ r2_hidden(A_42,k1_tarski(C_43))
      | C_43 = A_42
      | ~ r2_hidden(A_42,B_44) ) ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_95,plain,(
    ! [B_44] :
      ( k1_mcart_1('#skF_3') = '#skF_4'
      | ~ r2_hidden(k1_mcart_1('#skF_3'),B_44) ) ),
    inference(resolution,[status(thm)],[c_77,c_93])).

tff(c_98,plain,(
    ! [B_44] : ~ r2_hidden(k1_mcart_1('#skF_3'),B_44) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_95])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_77])).

tff(c_115,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_132,plain,(
    ! [A_57,C_58,B_59] :
      ( r2_hidden(k2_mcart_1(A_57),C_58)
      | ~ r2_hidden(A_57,k2_zfmisc_1(B_59,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_134,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:50:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.16  
% 1.85/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.16  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.85/1.16  
% 1.85/1.16  %Foreground sorts:
% 1.85/1.16  
% 1.85/1.16  
% 1.85/1.16  %Background operators:
% 1.85/1.16  
% 1.85/1.16  
% 1.85/1.16  %Foreground operators:
% 1.85/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.85/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.85/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.85/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.85/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.16  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.85/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.85/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.85/1.16  
% 1.85/1.17  tff(f_61, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.85/1.17  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.85/1.17  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.85/1.17  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.85/1.17  tff(c_36, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5') | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.17  tff(c_58, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_36])).
% 1.85/1.17  tff(c_38, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.17  tff(c_74, plain, (![A_36, B_37, C_38]: (r2_hidden(k1_mcart_1(A_36), B_37) | ~r2_hidden(A_36, k2_zfmisc_1(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.85/1.17  tff(c_77, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_74])).
% 1.85/1.17  tff(c_78, plain, (![A_39, B_40, C_41]: (r2_hidden(A_39, k4_xboole_0(B_40, k1_tarski(C_41))) | C_41=A_39 | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.85/1.17  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.85/1.17  tff(c_93, plain, (![A_42, C_43, B_44]: (~r2_hidden(A_42, k1_tarski(C_43)) | C_43=A_42 | ~r2_hidden(A_42, B_44))), inference(resolution, [status(thm)], [c_78, c_4])).
% 1.85/1.17  tff(c_95, plain, (![B_44]: (k1_mcart_1('#skF_3')='#skF_4' | ~r2_hidden(k1_mcart_1('#skF_3'), B_44))), inference(resolution, [status(thm)], [c_77, c_93])).
% 1.85/1.17  tff(c_98, plain, (![B_44]: (~r2_hidden(k1_mcart_1('#skF_3'), B_44))), inference(negUnitSimplification, [status(thm)], [c_58, c_95])).
% 1.85/1.17  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_77])).
% 1.85/1.17  tff(c_115, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_36])).
% 1.85/1.17  tff(c_132, plain, (![A_57, C_58, B_59]: (r2_hidden(k2_mcart_1(A_57), C_58) | ~r2_hidden(A_57, k2_zfmisc_1(B_59, C_58)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.85/1.17  tff(c_134, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_38, c_132])).
% 1.85/1.17  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_134])).
% 1.85/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.17  
% 1.85/1.17  Inference rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Ref     : 0
% 1.85/1.17  #Sup     : 20
% 1.85/1.17  #Fact    : 0
% 1.85/1.17  #Define  : 0
% 1.85/1.17  #Split   : 1
% 1.85/1.17  #Chain   : 0
% 1.85/1.17  #Close   : 0
% 1.85/1.17  
% 1.85/1.17  Ordering : KBO
% 1.85/1.17  
% 1.85/1.17  Simplification rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Subsume      : 1
% 1.85/1.17  #Demod        : 0
% 1.85/1.17  #Tautology    : 14
% 1.85/1.17  #SimpNegUnit  : 3
% 1.85/1.17  #BackRed      : 1
% 1.85/1.17  
% 1.85/1.17  #Partial instantiations: 0
% 1.85/1.17  #Strategies tried      : 1
% 1.85/1.17  
% 1.85/1.17  Timing (in seconds)
% 1.85/1.17  ----------------------
% 1.93/1.17  Preprocessing        : 0.29
% 1.93/1.17  Parsing              : 0.15
% 1.93/1.17  CNF conversion       : 0.02
% 1.93/1.17  Main loop            : 0.12
% 1.93/1.17  Inferencing          : 0.04
% 1.93/1.17  Reduction            : 0.04
% 1.93/1.17  Demodulation         : 0.02
% 1.93/1.17  BG Simplification    : 0.01
% 1.93/1.17  Subsumption          : 0.02
% 1.93/1.17  Abstraction          : 0.01
% 1.93/1.17  MUC search           : 0.00
% 1.93/1.17  Cooper               : 0.00
% 1.93/1.17  Total                : 0.44
% 1.93/1.17  Index Insertion      : 0.00
% 1.93/1.17  Index Deletion       : 0.00
% 1.93/1.17  Index Matching       : 0.00
% 1.93/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
