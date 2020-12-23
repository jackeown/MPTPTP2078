%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:03 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   45 (  73 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 ( 132 expanded)
%              Number of equality atoms :   30 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

tff(c_26,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_47,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,(
    ! [A_26,C_27,B_28] :
      ( k2_mcart_1(A_26) = C_27
      | ~ r2_hidden(A_26,k2_zfmisc_1(B_28,k1_tarski(C_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_66])).

tff(c_73,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_69])).

tff(c_75,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_76,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_82,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_76])).

tff(c_83,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_74,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_116,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden(k1_mcart_1(A_44),B_45)
      | ~ r2_hidden(A_44,k2_zfmisc_1(B_45,k1_tarski(C_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_120,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k2_tarski('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_116])).

tff(c_22,plain,(
    ! [A_16,B_17] : k2_mcart_1(k4_tarski(A_16,B_17)) = B_17 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( r2_hidden(k4_tarski(A_3,B_4),k2_zfmisc_1(C_5,D_6))
      | ~ r2_hidden(B_4,D_6)
      | ~ r2_hidden(A_3,C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_159,plain,(
    ! [A_55,D_56,C_57,B_58] :
      ( k2_mcart_1(A_55) = D_56
      | k2_mcart_1(A_55) = C_57
      | ~ r2_hidden(A_55,k2_zfmisc_1(B_58,k2_tarski(C_57,D_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_163,plain,(
    ! [A_3,D_56,C_57,C_5,B_4] :
      ( k2_mcart_1(k4_tarski(A_3,B_4)) = D_56
      | k2_mcart_1(k4_tarski(A_3,B_4)) = C_57
      | ~ r2_hidden(B_4,k2_tarski(C_57,D_56))
      | ~ r2_hidden(A_3,C_5) ) ),
    inference(resolution,[status(thm)],[c_4,c_159])).

tff(c_165,plain,(
    ! [A_3,D_56,C_57,C_5,B_4] :
      ( D_56 = B_4
      | C_57 = B_4
      | ~ r2_hidden(B_4,k2_tarski(C_57,D_56))
      | ~ r2_hidden(A_3,C_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_163])).

tff(c_167,plain,(
    ! [A_3,C_5] : ~ r2_hidden(A_3,C_5) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_120])).

tff(c_177,plain,(
    ! [D_61,B_62,C_63] :
      ( D_61 = B_62
      | C_63 = B_62
      | ~ r2_hidden(B_62,k2_tarski(C_63,D_61)) ) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_180,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_120,c_177])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_74,c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.19  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.84/1.19  
% 1.84/1.19  %Foreground sorts:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Background operators:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Foreground operators:
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.84/1.19  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.84/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.19  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.84/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.84/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.19  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.84/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.19  
% 1.91/1.21  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_mcart_1)).
% 1.91/1.21  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.91/1.21  tff(f_53, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.91/1.21  tff(f_33, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.91/1.21  tff(f_49, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_mcart_1)).
% 1.91/1.21  tff(c_26, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.21  tff(c_47, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_26])).
% 1.91/1.21  tff(c_24, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.21  tff(c_66, plain, (![A_26, C_27, B_28]: (k2_mcart_1(A_26)=C_27 | ~r2_hidden(A_26, k2_zfmisc_1(B_28, k1_tarski(C_27))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.21  tff(c_69, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_24, c_66])).
% 1.91/1.21  tff(c_73, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_69])).
% 1.91/1.21  tff(c_75, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 1.91/1.21  tff(c_28, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.21  tff(c_76, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_28])).
% 1.91/1.21  tff(c_82, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_76])).
% 1.91/1.21  tff(c_83, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 1.91/1.21  tff(c_74, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 1.91/1.21  tff(c_116, plain, (![A_44, B_45, C_46]: (r2_hidden(k1_mcart_1(A_44), B_45) | ~r2_hidden(A_44, k2_zfmisc_1(B_45, k1_tarski(C_46))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.21  tff(c_120, plain, (r2_hidden(k1_mcart_1('#skF_1'), k2_tarski('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_116])).
% 1.91/1.21  tff(c_22, plain, (![A_16, B_17]: (k2_mcart_1(k4_tarski(A_16, B_17))=B_17)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.21  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (r2_hidden(k4_tarski(A_3, B_4), k2_zfmisc_1(C_5, D_6)) | ~r2_hidden(B_4, D_6) | ~r2_hidden(A_3, C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.21  tff(c_159, plain, (![A_55, D_56, C_57, B_58]: (k2_mcart_1(A_55)=D_56 | k2_mcart_1(A_55)=C_57 | ~r2_hidden(A_55, k2_zfmisc_1(B_58, k2_tarski(C_57, D_56))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.91/1.21  tff(c_163, plain, (![A_3, D_56, C_57, C_5, B_4]: (k2_mcart_1(k4_tarski(A_3, B_4))=D_56 | k2_mcart_1(k4_tarski(A_3, B_4))=C_57 | ~r2_hidden(B_4, k2_tarski(C_57, D_56)) | ~r2_hidden(A_3, C_5))), inference(resolution, [status(thm)], [c_4, c_159])).
% 1.91/1.21  tff(c_165, plain, (![A_3, D_56, C_57, C_5, B_4]: (D_56=B_4 | C_57=B_4 | ~r2_hidden(B_4, k2_tarski(C_57, D_56)) | ~r2_hidden(A_3, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_163])).
% 1.91/1.21  tff(c_167, plain, (![A_3, C_5]: (~r2_hidden(A_3, C_5))), inference(splitLeft, [status(thm)], [c_165])).
% 1.91/1.21  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_120])).
% 1.91/1.21  tff(c_177, plain, (![D_61, B_62, C_63]: (D_61=B_62 | C_63=B_62 | ~r2_hidden(B_62, k2_tarski(C_63, D_61)))), inference(splitRight, [status(thm)], [c_165])).
% 1.91/1.21  tff(c_180, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_120, c_177])).
% 1.91/1.21  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_74, c_180])).
% 1.91/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.21  
% 1.91/1.21  Inference rules
% 1.91/1.21  ----------------------
% 1.91/1.21  #Ref     : 0
% 1.91/1.21  #Sup     : 26
% 1.91/1.21  #Fact    : 0
% 1.91/1.21  #Define  : 0
% 1.91/1.21  #Split   : 4
% 1.91/1.21  #Chain   : 0
% 1.91/1.21  #Close   : 0
% 1.91/1.21  
% 1.91/1.21  Ordering : KBO
% 1.91/1.21  
% 1.91/1.21  Simplification rules
% 1.91/1.21  ----------------------
% 1.91/1.21  #Subsume      : 15
% 1.91/1.21  #Demod        : 8
% 1.91/1.21  #Tautology    : 22
% 1.91/1.21  #SimpNegUnit  : 16
% 1.91/1.21  #BackRed      : 4
% 1.91/1.21  
% 1.91/1.21  #Partial instantiations: 0
% 1.91/1.21  #Strategies tried      : 1
% 1.91/1.21  
% 1.91/1.21  Timing (in seconds)
% 1.91/1.21  ----------------------
% 1.91/1.21  Preprocessing        : 0.29
% 1.91/1.21  Parsing              : 0.16
% 1.91/1.21  CNF conversion       : 0.02
% 1.91/1.21  Main loop            : 0.15
% 1.91/1.21  Inferencing          : 0.06
% 1.91/1.21  Reduction            : 0.05
% 1.91/1.21  Demodulation         : 0.03
% 1.91/1.21  BG Simplification    : 0.01
% 1.91/1.21  Subsumption          : 0.02
% 1.91/1.21  Abstraction          : 0.01
% 1.91/1.21  MUC search           : 0.00
% 1.91/1.21  Cooper               : 0.00
% 1.91/1.21  Total                : 0.48
% 1.91/1.21  Index Insertion      : 0.00
% 1.91/1.21  Index Deletion       : 0.00
% 1.91/1.21  Index Matching       : 0.00
% 1.91/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
