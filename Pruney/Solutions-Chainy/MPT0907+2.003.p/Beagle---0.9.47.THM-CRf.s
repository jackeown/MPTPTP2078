%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:55 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   37 (  53 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   51 (  88 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(c_8,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    r2_hidden('#skF_4',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_2,plain,(
    ! [A_1,B_16] :
      ( k4_tarski('#skF_2'(A_1,B_16),'#skF_3'(A_1,B_16)) = B_16
      | ~ r2_hidden(B_16,A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_27,plain,(
    ! [A_36,B_37] :
      ( k4_tarski('#skF_2'(A_36,B_37),'#skF_3'(A_36,B_37)) = B_37
      | ~ r2_hidden(B_37,A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [B_24,C_25] : k1_mcart_1(k4_tarski(B_24,C_25)) != k4_tarski(B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_53,plain,(
    ! [A_43,B_44] :
      ( k4_tarski('#skF_2'(A_43,B_44),'#skF_3'(A_43,B_44)) != k1_mcart_1(B_44)
      | ~ r2_hidden(B_44,A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_12])).

tff(c_57,plain,(
    ! [B_45,A_46] :
      ( k1_mcart_1(B_45) != B_45
      | ~ r2_hidden(B_45,A_46)
      | ~ v1_relat_1(A_46)
      | ~ r2_hidden(B_45,A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_53])).

tff(c_61,plain,
    ( k1_mcart_1('#skF_4') != '#skF_4'
    | ~ r2_hidden('#skF_4',k2_zfmisc_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_16,c_57])).

tff(c_66,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16,c_18,c_61])).

tff(c_67,plain,(
    k2_mcart_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_77,plain,(
    ! [A_55,B_56] :
      ( k4_tarski('#skF_2'(A_55,B_56),'#skF_3'(A_55,B_56)) = B_56
      | ~ r2_hidden(B_56,A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [B_24,C_25] : k2_mcart_1(k4_tarski(B_24,C_25)) != k4_tarski(B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_116,plain,(
    ! [A_66,B_67] :
      ( k4_tarski('#skF_2'(A_66,B_67),'#skF_3'(A_66,B_67)) != k2_mcart_1(B_67)
      | ~ r2_hidden(B_67,A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_10])).

tff(c_120,plain,(
    ! [B_68,A_69] :
      ( k2_mcart_1(B_68) != B_68
      | ~ r2_hidden(B_68,A_69)
      | ~ v1_relat_1(A_69)
      | ~ r2_hidden(B_68,A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_116])).

tff(c_124,plain,
    ( k2_mcart_1('#skF_4') != '#skF_4'
    | ~ r2_hidden('#skF_4',k2_zfmisc_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_16,c_120])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16,c_67,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:27:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.21  
% 1.80/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.21  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 1.80/1.21  
% 1.80/1.21  %Foreground sorts:
% 1.80/1.21  
% 1.80/1.21  
% 1.80/1.21  %Background operators:
% 1.80/1.21  
% 1.80/1.21  
% 1.80/1.21  %Foreground operators:
% 1.80/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.80/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.80/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.80/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.80/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.21  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.80/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.80/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.80/1.21  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.80/1.21  
% 1.80/1.22  tff(f_37, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.80/1.22  tff(f_55, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_mcart_1)).
% 1.80/1.22  tff(f_35, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.80/1.22  tff(f_46, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.80/1.22  tff(c_8, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.80/1.22  tff(c_16, plain, (r2_hidden('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.80/1.22  tff(c_14, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.80/1.22  tff(c_18, plain, (k1_mcart_1('#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_14])).
% 1.80/1.22  tff(c_2, plain, (![A_1, B_16]: (k4_tarski('#skF_2'(A_1, B_16), '#skF_3'(A_1, B_16))=B_16 | ~r2_hidden(B_16, A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.22  tff(c_27, plain, (![A_36, B_37]: (k4_tarski('#skF_2'(A_36, B_37), '#skF_3'(A_36, B_37))=B_37 | ~r2_hidden(B_37, A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.22  tff(c_12, plain, (![B_24, C_25]: (k1_mcart_1(k4_tarski(B_24, C_25))!=k4_tarski(B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.80/1.22  tff(c_53, plain, (![A_43, B_44]: (k4_tarski('#skF_2'(A_43, B_44), '#skF_3'(A_43, B_44))!=k1_mcart_1(B_44) | ~r2_hidden(B_44, A_43) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_27, c_12])).
% 1.80/1.22  tff(c_57, plain, (![B_45, A_46]: (k1_mcart_1(B_45)!=B_45 | ~r2_hidden(B_45, A_46) | ~v1_relat_1(A_46) | ~r2_hidden(B_45, A_46) | ~v1_relat_1(A_46))), inference(superposition, [status(thm), theory('equality')], [c_2, c_53])).
% 1.80/1.22  tff(c_61, plain, (k1_mcart_1('#skF_4')!='#skF_4' | ~r2_hidden('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6')) | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_16, c_57])).
% 1.80/1.22  tff(c_66, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_16, c_18, c_61])).
% 1.80/1.22  tff(c_67, plain, (k2_mcart_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_14])).
% 1.80/1.22  tff(c_77, plain, (![A_55, B_56]: (k4_tarski('#skF_2'(A_55, B_56), '#skF_3'(A_55, B_56))=B_56 | ~r2_hidden(B_56, A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.22  tff(c_10, plain, (![B_24, C_25]: (k2_mcart_1(k4_tarski(B_24, C_25))!=k4_tarski(B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.80/1.22  tff(c_116, plain, (![A_66, B_67]: (k4_tarski('#skF_2'(A_66, B_67), '#skF_3'(A_66, B_67))!=k2_mcart_1(B_67) | ~r2_hidden(B_67, A_66) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_77, c_10])).
% 1.80/1.22  tff(c_120, plain, (![B_68, A_69]: (k2_mcart_1(B_68)!=B_68 | ~r2_hidden(B_68, A_69) | ~v1_relat_1(A_69) | ~r2_hidden(B_68, A_69) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_2, c_116])).
% 1.80/1.22  tff(c_124, plain, (k2_mcart_1('#skF_4')!='#skF_4' | ~r2_hidden('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6')) | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_16, c_120])).
% 1.80/1.22  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_16, c_67, c_124])).
% 1.80/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.22  
% 1.80/1.22  Inference rules
% 1.80/1.22  ----------------------
% 1.80/1.22  #Ref     : 2
% 1.80/1.22  #Sup     : 25
% 1.80/1.22  #Fact    : 0
% 1.80/1.22  #Define  : 0
% 1.80/1.22  #Split   : 1
% 1.80/1.22  #Chain   : 0
% 1.80/1.22  #Close   : 0
% 1.80/1.22  
% 1.80/1.22  Ordering : KBO
% 1.80/1.23  
% 1.80/1.23  Simplification rules
% 1.80/1.23  ----------------------
% 1.80/1.23  #Subsume      : 4
% 1.80/1.23  #Demod        : 8
% 1.80/1.23  #Tautology    : 10
% 1.80/1.23  #SimpNegUnit  : 0
% 1.80/1.23  #BackRed      : 0
% 1.80/1.23  
% 1.80/1.23  #Partial instantiations: 0
% 1.80/1.23  #Strategies tried      : 1
% 1.80/1.23  
% 1.80/1.23  Timing (in seconds)
% 1.80/1.23  ----------------------
% 1.80/1.23  Preprocessing        : 0.24
% 1.80/1.23  Parsing              : 0.13
% 1.80/1.23  CNF conversion       : 0.02
% 1.80/1.23  Main loop            : 0.14
% 1.80/1.23  Inferencing          : 0.07
% 1.80/1.23  Reduction            : 0.04
% 1.80/1.23  Demodulation         : 0.03
% 1.80/1.23  BG Simplification    : 0.01
% 1.80/1.23  Subsumption          : 0.02
% 1.80/1.23  Abstraction          : 0.01
% 1.80/1.23  MUC search           : 0.00
% 1.80/1.23  Cooper               : 0.00
% 1.80/1.23  Total                : 0.41
% 1.80/1.23  Index Insertion      : 0.00
% 1.80/1.23  Index Deletion       : 0.00
% 1.80/1.23  Index Matching       : 0.00
% 1.80/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
