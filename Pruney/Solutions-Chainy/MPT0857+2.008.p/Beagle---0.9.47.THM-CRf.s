%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:55 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_59,axiom,(
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

tff(c_40,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_53,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_92,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden(k1_mcart_1(A_39),B_40)
      | ~ r2_hidden(A_39,k2_zfmisc_1(B_40,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_94,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_92])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_94])).

tff(c_99,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_135,plain,(
    ! [A_54,C_55,B_56] :
      ( r2_hidden(k2_mcart_1(A_54),C_55)
      | ~ r2_hidden(A_54,k2_zfmisc_1(B_56,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_138,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_135])).

tff(c_157,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden(A_66,k4_xboole_0(B_67,k1_tarski(C_68)))
      | C_68 = A_66
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_188,plain,(
    ! [A_70,C_71,B_72] :
      ( ~ r2_hidden(A_70,k1_tarski(C_71))
      | C_71 = A_70
      | ~ r2_hidden(A_70,B_72) ) ),
    inference(resolution,[status(thm)],[c_157,c_4])).

tff(c_192,plain,(
    ! [B_72] :
      ( k2_mcart_1('#skF_3') = '#skF_5'
      | ~ r2_hidden(k2_mcart_1('#skF_3'),B_72) ) ),
    inference(resolution,[status(thm)],[c_138,c_188])).

tff(c_197,plain,(
    ! [B_72] : ~ r2_hidden(k2_mcart_1('#skF_3'),B_72) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_192])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:40:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.24  
% 1.96/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.24  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.96/1.24  
% 1.96/1.24  %Foreground sorts:
% 1.96/1.24  
% 1.96/1.24  
% 1.96/1.24  %Background operators:
% 1.96/1.24  
% 1.96/1.24  
% 1.96/1.24  %Foreground operators:
% 1.96/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.24  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.96/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.24  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.96/1.24  
% 1.96/1.25  tff(f_66, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.96/1.25  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.96/1.25  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.96/1.25  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.96/1.25  tff(c_40, plain, (k2_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.25  tff(c_53, plain, (~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 1.96/1.25  tff(c_42, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.25  tff(c_92, plain, (![A_39, B_40, C_41]: (r2_hidden(k1_mcart_1(A_39), B_40) | ~r2_hidden(A_39, k2_zfmisc_1(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.96/1.25  tff(c_94, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_42, c_92])).
% 1.96/1.25  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_94])).
% 1.96/1.25  tff(c_99, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_40])).
% 1.96/1.25  tff(c_135, plain, (![A_54, C_55, B_56]: (r2_hidden(k2_mcart_1(A_54), C_55) | ~r2_hidden(A_54, k2_zfmisc_1(B_56, C_55)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.96/1.25  tff(c_138, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_135])).
% 1.96/1.25  tff(c_157, plain, (![A_66, B_67, C_68]: (r2_hidden(A_66, k4_xboole_0(B_67, k1_tarski(C_68))) | C_68=A_66 | ~r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.96/1.25  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.25  tff(c_188, plain, (![A_70, C_71, B_72]: (~r2_hidden(A_70, k1_tarski(C_71)) | C_71=A_70 | ~r2_hidden(A_70, B_72))), inference(resolution, [status(thm)], [c_157, c_4])).
% 1.96/1.25  tff(c_192, plain, (![B_72]: (k2_mcart_1('#skF_3')='#skF_5' | ~r2_hidden(k2_mcart_1('#skF_3'), B_72))), inference(resolution, [status(thm)], [c_138, c_188])).
% 1.96/1.25  tff(c_197, plain, (![B_72]: (~r2_hidden(k2_mcart_1('#skF_3'), B_72))), inference(negUnitSimplification, [status(thm)], [c_99, c_192])).
% 1.96/1.25  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_138])).
% 1.96/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.25  
% 1.96/1.25  Inference rules
% 1.96/1.25  ----------------------
% 1.96/1.25  #Ref     : 0
% 1.96/1.25  #Sup     : 34
% 1.96/1.25  #Fact    : 0
% 1.96/1.25  #Define  : 0
% 1.96/1.25  #Split   : 1
% 1.96/1.25  #Chain   : 0
% 1.96/1.25  #Close   : 0
% 1.96/1.25  
% 1.96/1.25  Ordering : KBO
% 1.96/1.25  
% 1.96/1.25  Simplification rules
% 1.96/1.25  ----------------------
% 1.96/1.25  #Subsume      : 2
% 1.96/1.25  #Demod        : 1
% 1.96/1.25  #Tautology    : 24
% 1.96/1.25  #SimpNegUnit  : 3
% 1.96/1.25  #BackRed      : 1
% 1.96/1.25  
% 1.96/1.25  #Partial instantiations: 0
% 1.96/1.25  #Strategies tried      : 1
% 1.96/1.25  
% 1.96/1.25  Timing (in seconds)
% 1.96/1.25  ----------------------
% 1.96/1.25  Preprocessing        : 0.29
% 1.96/1.25  Parsing              : 0.15
% 1.96/1.25  CNF conversion       : 0.02
% 1.96/1.25  Main loop            : 0.16
% 1.96/1.25  Inferencing          : 0.06
% 1.96/1.25  Reduction            : 0.04
% 1.96/1.25  Demodulation         : 0.03
% 1.96/1.25  BG Simplification    : 0.01
% 1.96/1.25  Subsumption          : 0.03
% 1.96/1.25  Abstraction          : 0.01
% 1.96/1.25  MUC search           : 0.00
% 2.04/1.25  Cooper               : 0.00
% 2.04/1.25  Total                : 0.47
% 2.04/1.25  Index Insertion      : 0.00
% 2.04/1.25  Index Deletion       : 0.00
% 2.04/1.25  Index Matching       : 0.00
% 2.04/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
