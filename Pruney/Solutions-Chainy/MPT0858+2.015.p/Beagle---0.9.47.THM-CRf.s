%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:58 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  52 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_30,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_mcart_1(A_45) = B_46
      | ~ r2_hidden(A_45,k2_zfmisc_1(k1_tarski(B_46),C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_73,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_73])).

tff(c_78,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_109,plain,(
    ! [A_60,C_61,B_62] :
      ( r2_hidden(k2_mcart_1(A_60),C_61)
      | ~ r2_hidden(A_60,k2_zfmisc_1(k1_tarski(B_62),C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_109])).

tff(c_26,plain,(
    ! [A_36,B_37] : k1_mcart_1(k4_tarski(A_36,B_37)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_114,plain,(
    ! [A_63,D_64,C_65] :
      ( r2_hidden(k4_tarski(A_63,D_64),k2_zfmisc_1(C_65,k1_tarski(D_64)))
      | ~ r2_hidden(A_63,C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_33,B_34,C_35] :
      ( k1_mcart_1(A_33) = B_34
      | ~ r2_hidden(A_33,k2_zfmisc_1(k1_tarski(B_34),C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_125,plain,(
    ! [A_63,D_64,B_34] :
      ( k1_mcart_1(k4_tarski(A_63,D_64)) = B_34
      | ~ r2_hidden(A_63,k1_tarski(B_34)) ) ),
    inference(resolution,[status(thm)],[c_114,c_24])).

tff(c_132,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r2_hidden(A_67,k1_tarski(B_66)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_125])).

tff(c_135,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_113,c_132])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.29  
% 1.89/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.29  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.29  
% 1.89/1.29  %Foreground sorts:
% 1.89/1.29  
% 1.89/1.29  
% 1.89/1.29  %Background operators:
% 1.89/1.29  
% 1.89/1.29  
% 1.89/1.29  %Foreground operators:
% 1.89/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.89/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.89/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.89/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.89/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.29  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.89/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.29  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.89/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.89/1.29  
% 1.89/1.30  tff(f_62, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.89/1.30  tff(f_51, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.89/1.30  tff(f_55, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.89/1.30  tff(f_45, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 1.89/1.30  tff(c_30, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.30  tff(c_60, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 1.89/1.30  tff(c_32, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.30  tff(c_70, plain, (![A_45, B_46, C_47]: (k1_mcart_1(A_45)=B_46 | ~r2_hidden(A_45, k2_zfmisc_1(k1_tarski(B_46), C_47)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.89/1.30  tff(c_73, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_32, c_70])).
% 1.89/1.30  tff(c_77, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_73])).
% 1.89/1.30  tff(c_78, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 1.89/1.30  tff(c_109, plain, (![A_60, C_61, B_62]: (r2_hidden(k2_mcart_1(A_60), C_61) | ~r2_hidden(A_60, k2_zfmisc_1(k1_tarski(B_62), C_61)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.89/1.30  tff(c_113, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_109])).
% 1.89/1.30  tff(c_26, plain, (![A_36, B_37]: (k1_mcart_1(k4_tarski(A_36, B_37))=A_36)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.89/1.30  tff(c_114, plain, (![A_63, D_64, C_65]: (r2_hidden(k4_tarski(A_63, D_64), k2_zfmisc_1(C_65, k1_tarski(D_64))) | ~r2_hidden(A_63, C_65))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.30  tff(c_24, plain, (![A_33, B_34, C_35]: (k1_mcart_1(A_33)=B_34 | ~r2_hidden(A_33, k2_zfmisc_1(k1_tarski(B_34), C_35)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.89/1.30  tff(c_125, plain, (![A_63, D_64, B_34]: (k1_mcart_1(k4_tarski(A_63, D_64))=B_34 | ~r2_hidden(A_63, k1_tarski(B_34)))), inference(resolution, [status(thm)], [c_114, c_24])).
% 1.89/1.30  tff(c_132, plain, (![B_66, A_67]: (B_66=A_67 | ~r2_hidden(A_67, k1_tarski(B_66)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_125])).
% 1.89/1.30  tff(c_135, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_113, c_132])).
% 1.89/1.30  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_135])).
% 1.89/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.30  
% 1.89/1.30  Inference rules
% 1.89/1.30  ----------------------
% 1.89/1.30  #Ref     : 0
% 1.89/1.30  #Sup     : 21
% 1.89/1.30  #Fact    : 0
% 1.89/1.30  #Define  : 0
% 1.89/1.30  #Split   : 1
% 1.89/1.30  #Chain   : 0
% 1.89/1.30  #Close   : 0
% 1.89/1.30  
% 1.89/1.30  Ordering : KBO
% 1.89/1.30  
% 1.89/1.30  Simplification rules
% 1.89/1.30  ----------------------
% 1.89/1.30  #Subsume      : 0
% 1.89/1.30  #Demod        : 3
% 1.89/1.30  #Tautology    : 16
% 1.89/1.30  #SimpNegUnit  : 2
% 1.89/1.30  #BackRed      : 0
% 1.89/1.30  
% 1.89/1.30  #Partial instantiations: 0
% 1.89/1.30  #Strategies tried      : 1
% 1.89/1.30  
% 1.89/1.30  Timing (in seconds)
% 1.89/1.30  ----------------------
% 1.89/1.30  Preprocessing        : 0.35
% 1.89/1.30  Parsing              : 0.18
% 1.89/1.30  CNF conversion       : 0.02
% 1.89/1.30  Main loop            : 0.11
% 1.89/1.30  Inferencing          : 0.04
% 1.89/1.30  Reduction            : 0.04
% 1.89/1.30  Demodulation         : 0.02
% 1.89/1.30  BG Simplification    : 0.01
% 1.89/1.30  Subsumption          : 0.01
% 1.89/1.30  Abstraction          : 0.01
% 1.89/1.30  MUC search           : 0.00
% 1.89/1.30  Cooper               : 0.00
% 1.89/1.30  Total                : 0.49
% 1.89/1.30  Index Insertion      : 0.00
% 1.89/1.30  Index Deletion       : 0.00
% 1.89/1.30  Index Matching       : 0.00
% 1.89/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
