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
% DateTime   : Thu Dec  3 10:09:06 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   45 (  60 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    5
%              Number of atoms          :   55 (  98 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(c_42,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_71,plain,(
    ! [A_37,B_38,C_39] :
      ( r2_hidden(k1_mcart_1(A_37),B_38)
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_38,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_74,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_71])).

tff(c_98,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden(A_46,k4_xboole_0(B_47,k1_tarski(C_48)))
      | C_48 = A_46
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_141,plain,(
    ! [A_51,C_52,B_53] :
      ( ~ r2_hidden(A_51,k1_tarski(C_52))
      | C_52 = A_51
      | ~ r2_hidden(A_51,B_53) ) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_149,plain,(
    ! [B_53] :
      ( k1_mcart_1('#skF_3') = '#skF_4'
      | ~ r2_hidden(k1_mcart_1('#skF_3'),B_53) ) ),
    inference(resolution,[status(thm)],[c_74,c_141])).

tff(c_158,plain,(
    ! [B_53] : ~ r2_hidden(k1_mcart_1('#skF_3'),B_53) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_149])).

tff(c_84,plain,(
    ! [D_43,A_44,B_45] :
      ( r2_hidden(D_43,k4_xboole_0(A_44,B_45))
      | r2_hidden(D_43,B_45)
      | ~ r2_hidden(D_43,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [C_15,B_14] : ~ r2_hidden(C_15,k4_xboole_0(B_14,k1_tarski(C_15))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    ! [D_49,A_50] :
      ( r2_hidden(D_49,k1_tarski(D_49))
      | ~ r2_hidden(D_49,A_50) ) ),
    inference(resolution,[status(thm)],[c_84,c_28])).

tff(c_126,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_74,c_113])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_126])).

tff(c_163,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_170,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_44])).

tff(c_162,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_267,plain,(
    ! [A_84,D_85,C_86,B_87] :
      ( k2_mcart_1(A_84) = D_85
      | k2_mcart_1(A_84) = C_86
      | ~ r2_hidden(A_84,k2_zfmisc_1(B_87,k2_tarski(C_86,D_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_270,plain,
    ( k2_mcart_1('#skF_3') = '#skF_6'
    | k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_267])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_162,c_270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:42:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.29  
% 2.01/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.29  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.01/1.29  
% 2.01/1.29  %Foreground sorts:
% 2.01/1.29  
% 2.01/1.29  
% 2.01/1.29  %Background operators:
% 2.01/1.29  
% 2.01/1.29  
% 2.01/1.29  %Foreground operators:
% 2.01/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.01/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.01/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.01/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.29  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.01/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.01/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.29  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.01/1.29  
% 2.01/1.30  tff(f_71, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 2.01/1.30  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.01/1.30  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.01/1.30  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.01/1.30  tff(f_62, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 2.01/1.30  tff(c_42, plain, (k2_mcart_1('#skF_3')!='#skF_6' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.01/1.30  tff(c_54, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_42])).
% 2.01/1.30  tff(c_40, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.01/1.30  tff(c_71, plain, (![A_37, B_38, C_39]: (r2_hidden(k1_mcart_1(A_37), B_38) | ~r2_hidden(A_37, k2_zfmisc_1(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.01/1.30  tff(c_74, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_71])).
% 2.01/1.30  tff(c_98, plain, (![A_46, B_47, C_48]: (r2_hidden(A_46, k4_xboole_0(B_47, k1_tarski(C_48))) | C_48=A_46 | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.01/1.30  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.30  tff(c_141, plain, (![A_51, C_52, B_53]: (~r2_hidden(A_51, k1_tarski(C_52)) | C_52=A_51 | ~r2_hidden(A_51, B_53))), inference(resolution, [status(thm)], [c_98, c_4])).
% 2.01/1.30  tff(c_149, plain, (![B_53]: (k1_mcart_1('#skF_3')='#skF_4' | ~r2_hidden(k1_mcart_1('#skF_3'), B_53))), inference(resolution, [status(thm)], [c_74, c_141])).
% 2.01/1.30  tff(c_158, plain, (![B_53]: (~r2_hidden(k1_mcart_1('#skF_3'), B_53))), inference(negUnitSimplification, [status(thm)], [c_54, c_149])).
% 2.01/1.30  tff(c_84, plain, (![D_43, A_44, B_45]: (r2_hidden(D_43, k4_xboole_0(A_44, B_45)) | r2_hidden(D_43, B_45) | ~r2_hidden(D_43, A_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.30  tff(c_28, plain, (![C_15, B_14]: (~r2_hidden(C_15, k4_xboole_0(B_14, k1_tarski(C_15))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.01/1.30  tff(c_113, plain, (![D_49, A_50]: (r2_hidden(D_49, k1_tarski(D_49)) | ~r2_hidden(D_49, A_50))), inference(resolution, [status(thm)], [c_84, c_28])).
% 2.01/1.30  tff(c_126, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski(k1_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_74, c_113])).
% 2.23/1.30  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_126])).
% 2.23/1.30  tff(c_163, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 2.23/1.30  tff(c_44, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.23/1.30  tff(c_170, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_44])).
% 2.23/1.30  tff(c_162, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 2.23/1.30  tff(c_267, plain, (![A_84, D_85, C_86, B_87]: (k2_mcart_1(A_84)=D_85 | k2_mcart_1(A_84)=C_86 | ~r2_hidden(A_84, k2_zfmisc_1(B_87, k2_tarski(C_86, D_85))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.30  tff(c_270, plain, (k2_mcart_1('#skF_3')='#skF_6' | k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_40, c_267])).
% 2.23/1.30  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_162, c_270])).
% 2.23/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  Inference rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Ref     : 0
% 2.23/1.30  #Sup     : 52
% 2.23/1.30  #Fact    : 0
% 2.23/1.30  #Define  : 0
% 2.23/1.30  #Split   : 1
% 2.23/1.30  #Chain   : 0
% 2.23/1.30  #Close   : 0
% 2.23/1.30  
% 2.23/1.30  Ordering : KBO
% 2.23/1.30  
% 2.23/1.30  Simplification rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Subsume      : 7
% 2.23/1.30  #Demod        : 8
% 2.23/1.30  #Tautology    : 32
% 2.23/1.30  #SimpNegUnit  : 4
% 2.23/1.30  #BackRed      : 2
% 2.23/1.30  
% 2.23/1.30  #Partial instantiations: 0
% 2.23/1.30  #Strategies tried      : 1
% 2.23/1.30  
% 2.23/1.30  Timing (in seconds)
% 2.23/1.30  ----------------------
% 2.23/1.31  Preprocessing        : 0.32
% 2.23/1.31  Parsing              : 0.17
% 2.23/1.31  CNF conversion       : 0.02
% 2.23/1.31  Main loop            : 0.20
% 2.23/1.31  Inferencing          : 0.08
% 2.23/1.31  Reduction            : 0.06
% 2.23/1.31  Demodulation         : 0.04
% 2.23/1.31  BG Simplification    : 0.01
% 2.23/1.31  Subsumption          : 0.03
% 2.23/1.31  Abstraction          : 0.01
% 2.23/1.31  MUC search           : 0.00
% 2.23/1.31  Cooper               : 0.00
% 2.23/1.31  Total                : 0.55
% 2.23/1.31  Index Insertion      : 0.00
% 2.23/1.31  Index Deletion       : 0.00
% 2.23/1.31  Index Matching       : 0.00
% 2.23/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
