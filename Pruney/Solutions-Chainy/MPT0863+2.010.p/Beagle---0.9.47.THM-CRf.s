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
% DateTime   : Thu Dec  3 10:09:08 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   38 (  55 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :    4
%              Number of atoms          :   48 ( 112 expanded)
%              Number of equality atoms :   36 (  86 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k2_tarski(D,E)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & ( k2_mcart_1(A) = D
            | k2_mcart_1(A) = E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(c_18,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_12,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    k2_mcart_1('#skF_1') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_10,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k2_tarski('#skF_2','#skF_3'),k2_tarski('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_31,plain,(
    ! [A_17,D_18,C_19,B_20] :
      ( k2_mcart_1(A_17) = D_18
      | k2_mcart_1(A_17) = C_19
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_20,k2_tarski(C_19,D_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,
    ( k2_mcart_1('#skF_1') = '#skF_5'
    | k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_31])).

tff(c_38,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_20,c_34])).

tff(c_40,plain,(
    k2_mcart_1('#skF_1') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_14,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_47,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_39,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_66,plain,(
    ! [A_33,C_34,B_35,D_36] :
      ( k1_mcart_1(A_33) = C_34
      | k1_mcart_1(A_33) = B_35
      | ~ r2_hidden(A_33,k2_zfmisc_1(k2_tarski(B_35,C_34),D_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_66])).

tff(c_73,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_39,c_69])).

tff(c_74,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_75,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_16,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_84,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_16])).

tff(c_96,plain,(
    ! [A_45,C_46,B_47,D_48] :
      ( k1_mcart_1(A_45) = C_46
      | k1_mcart_1(A_45) = B_47
      | ~ r2_hidden(A_45,k2_zfmisc_1(k2_tarski(B_47,C_46),D_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_84,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:16:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.14  
% 1.76/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.14  %$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.76/1.14  
% 1.76/1.14  %Foreground sorts:
% 1.76/1.14  
% 1.76/1.14  
% 1.76/1.14  %Background operators:
% 1.76/1.14  
% 1.76/1.14  
% 1.76/1.14  %Foreground operators:
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.76/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.14  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.76/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.76/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.14  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.76/1.14  
% 1.76/1.15  tff(f_52, negated_conjecture, ~(![A, B, C, D, E]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k2_tarski(D, E))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & ((k2_mcart_1(A) = D) | (k2_mcart_1(A) = E))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_mcart_1)).
% 1.76/1.15  tff(f_41, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 1.76/1.15  tff(f_33, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 1.76/1.15  tff(c_18, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.76/1.15  tff(c_19, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_18])).
% 1.76/1.15  tff(c_12, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.76/1.15  tff(c_20, plain, (k2_mcart_1('#skF_1')!='#skF_5'), inference(splitLeft, [status(thm)], [c_12])).
% 1.76/1.15  tff(c_10, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k2_tarski('#skF_2', '#skF_3'), k2_tarski('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.76/1.15  tff(c_31, plain, (![A_17, D_18, C_19, B_20]: (k2_mcart_1(A_17)=D_18 | k2_mcart_1(A_17)=C_19 | ~r2_hidden(A_17, k2_zfmisc_1(B_20, k2_tarski(C_19, D_18))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.76/1.15  tff(c_34, plain, (k2_mcart_1('#skF_1')='#skF_5' | k2_mcart_1('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_10, c_31])).
% 1.76/1.15  tff(c_38, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19, c_20, c_34])).
% 1.76/1.15  tff(c_40, plain, (k2_mcart_1('#skF_1')='#skF_5'), inference(splitRight, [status(thm)], [c_12])).
% 1.76/1.15  tff(c_14, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.76/1.15  tff(c_47, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 1.76/1.15  tff(c_39, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_12])).
% 1.76/1.15  tff(c_66, plain, (![A_33, C_34, B_35, D_36]: (k1_mcart_1(A_33)=C_34 | k1_mcart_1(A_33)=B_35 | ~r2_hidden(A_33, k2_zfmisc_1(k2_tarski(B_35, C_34), D_36)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.76/1.15  tff(c_69, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_10, c_66])).
% 1.76/1.15  tff(c_73, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_39, c_69])).
% 1.76/1.15  tff(c_74, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitRight, [status(thm)], [c_18])).
% 1.76/1.15  tff(c_75, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_18])).
% 1.76/1.15  tff(c_16, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.76/1.15  tff(c_84, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_16])).
% 1.76/1.15  tff(c_96, plain, (![A_45, C_46, B_47, D_48]: (k1_mcart_1(A_45)=C_46 | k1_mcart_1(A_45)=B_47 | ~r2_hidden(A_45, k2_zfmisc_1(k2_tarski(B_47, C_46), D_48)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.76/1.15  tff(c_99, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_10, c_96])).
% 1.76/1.15  tff(c_103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_84, c_99])).
% 1.76/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.15  
% 1.76/1.15  Inference rules
% 1.76/1.15  ----------------------
% 1.76/1.15  #Ref     : 0
% 1.76/1.15  #Sup     : 14
% 1.76/1.15  #Fact    : 0
% 1.76/1.15  #Define  : 0
% 1.76/1.15  #Split   : 3
% 1.76/1.15  #Chain   : 0
% 1.76/1.15  #Close   : 0
% 1.76/1.15  
% 1.76/1.15  Ordering : KBO
% 1.76/1.15  
% 1.76/1.15  Simplification rules
% 1.76/1.15  ----------------------
% 1.76/1.15  #Subsume      : 3
% 1.76/1.15  #Demod        : 9
% 1.76/1.15  #Tautology    : 5
% 1.76/1.15  #SimpNegUnit  : 4
% 1.76/1.15  #BackRed      : 1
% 1.76/1.15  
% 1.76/1.15  #Partial instantiations: 0
% 1.76/1.15  #Strategies tried      : 1
% 1.76/1.15  
% 1.76/1.15  Timing (in seconds)
% 1.76/1.15  ----------------------
% 1.76/1.15  Preprocessing        : 0.26
% 1.76/1.15  Parsing              : 0.14
% 1.76/1.15  CNF conversion       : 0.02
% 1.76/1.15  Main loop            : 0.13
% 1.76/1.15  Inferencing          : 0.05
% 1.76/1.15  Reduction            : 0.04
% 1.76/1.15  Demodulation         : 0.02
% 1.76/1.15  BG Simplification    : 0.01
% 1.76/1.15  Subsumption          : 0.02
% 1.76/1.15  Abstraction          : 0.00
% 1.76/1.15  MUC search           : 0.00
% 1.76/1.15  Cooper               : 0.00
% 1.76/1.15  Total                : 0.42
% 1.76/1.15  Index Insertion      : 0.00
% 1.76/1.15  Index Deletion       : 0.00
% 1.76/1.15  Index Matching       : 0.00
% 1.76/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
