%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:55 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   37 (  51 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   40 (  80 expanded)
%              Number of equality atoms :   22 (  44 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(c_32,plain,(
    r2_hidden('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,
    ( k2_mcart_1('#skF_7') = '#skF_7'
    | k1_mcart_1('#skF_7') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_33,plain,(
    k1_mcart_1('#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_4,plain,(
    ! [A_1,B_2,D_28] :
      ( k4_tarski('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),'#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28)) = D_28
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ! [A_63,B_64,D_65] :
      ( k4_tarski('#skF_5'(A_63,B_64,k2_zfmisc_1(A_63,B_64),D_65),'#skF_6'(A_63,B_64,k2_zfmisc_1(A_63,B_64),D_65)) = D_65
      | ~ r2_hidden(D_65,k2_zfmisc_1(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [B_38,C_39] : k1_mcart_1(k4_tarski(B_38,C_39)) != k4_tarski(B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    ! [A_66,B_67,D_68] :
      ( k4_tarski('#skF_5'(A_66,B_67,k2_zfmisc_1(A_66,B_67),D_68),'#skF_6'(A_66,B_67,k2_zfmisc_1(A_66,B_67),D_68)) != k1_mcart_1(D_68)
      | ~ r2_hidden(D_68,k2_zfmisc_1(A_66,B_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_28])).

tff(c_68,plain,(
    ! [D_69,A_70,B_71] :
      ( k1_mcart_1(D_69) != D_69
      | ~ r2_hidden(D_69,k2_zfmisc_1(A_70,B_71))
      | ~ r2_hidden(D_69,k2_zfmisc_1(A_70,B_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_90,plain,
    ( k1_mcart_1('#skF_7') != '#skF_7'
    | ~ r2_hidden('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_33,c_90])).

tff(c_102,plain,(
    k2_mcart_1('#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_116,plain,(
    ! [A_95,B_96,D_97] :
      ( k4_tarski('#skF_5'(A_95,B_96,k2_zfmisc_1(A_95,B_96),D_97),'#skF_6'(A_95,B_96,k2_zfmisc_1(A_95,B_96),D_97)) = D_97
      | ~ r2_hidden(D_97,k2_zfmisc_1(A_95,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [B_38,C_39] : k2_mcart_1(k4_tarski(B_38,C_39)) != k4_tarski(B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_152,plain,(
    ! [A_101,B_102,D_103] :
      ( k4_tarski('#skF_5'(A_101,B_102,k2_zfmisc_1(A_101,B_102),D_103),'#skF_6'(A_101,B_102,k2_zfmisc_1(A_101,B_102),D_103)) != k2_mcart_1(D_103)
      | ~ r2_hidden(D_103,k2_zfmisc_1(A_101,B_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_26])).

tff(c_156,plain,(
    ! [D_104,A_105,B_106] :
      ( k2_mcart_1(D_104) != D_104
      | ~ r2_hidden(D_104,k2_zfmisc_1(A_105,B_106))
      | ~ r2_hidden(D_104,k2_zfmisc_1(A_105,B_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_152])).

tff(c_178,plain,
    ( k2_mcart_1('#skF_7') != '#skF_7'
    | ~ r2_hidden('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_32,c_156])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_102,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:54:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.28  
% 1.79/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.28  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 1.79/1.28  
% 1.79/1.28  %Foreground sorts:
% 1.79/1.28  
% 1.79/1.28  
% 1.79/1.28  %Background operators:
% 1.79/1.28  
% 1.79/1.28  
% 1.79/1.28  %Foreground operators:
% 1.79/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.79/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.79/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.79/1.28  tff('#skF_7', type, '#skF_7': $i).
% 1.79/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.79/1.28  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 1.79/1.28  tff('#skF_9', type, '#skF_9': $i).
% 1.79/1.28  tff('#skF_8', type, '#skF_8': $i).
% 1.79/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.28  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.79/1.28  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 1.79/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.79/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.79/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.28  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.79/1.28  
% 2.10/1.29  tff(f_55, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_mcart_1)).
% 2.10/1.29  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.10/1.29  tff(f_46, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.10/1.29  tff(c_32, plain, (r2_hidden('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.10/1.29  tff(c_30, plain, (k2_mcart_1('#skF_7')='#skF_7' | k1_mcart_1('#skF_7')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.10/1.29  tff(c_33, plain, (k1_mcart_1('#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_30])).
% 2.10/1.29  tff(c_4, plain, (![A_1, B_2, D_28]: (k4_tarski('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), '#skF_6'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28))=D_28 | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.29  tff(c_46, plain, (![A_63, B_64, D_65]: (k4_tarski('#skF_5'(A_63, B_64, k2_zfmisc_1(A_63, B_64), D_65), '#skF_6'(A_63, B_64, k2_zfmisc_1(A_63, B_64), D_65))=D_65 | ~r2_hidden(D_65, k2_zfmisc_1(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.29  tff(c_28, plain, (![B_38, C_39]: (k1_mcart_1(k4_tarski(B_38, C_39))!=k4_tarski(B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.10/1.29  tff(c_64, plain, (![A_66, B_67, D_68]: (k4_tarski('#skF_5'(A_66, B_67, k2_zfmisc_1(A_66, B_67), D_68), '#skF_6'(A_66, B_67, k2_zfmisc_1(A_66, B_67), D_68))!=k1_mcart_1(D_68) | ~r2_hidden(D_68, k2_zfmisc_1(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_28])).
% 2.10/1.29  tff(c_68, plain, (![D_69, A_70, B_71]: (k1_mcart_1(D_69)!=D_69 | ~r2_hidden(D_69, k2_zfmisc_1(A_70, B_71)) | ~r2_hidden(D_69, k2_zfmisc_1(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_64])).
% 2.10/1.29  tff(c_90, plain, (k1_mcart_1('#skF_7')!='#skF_7' | ~r2_hidden('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_32, c_68])).
% 2.10/1.29  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_33, c_90])).
% 2.10/1.29  tff(c_102, plain, (k2_mcart_1('#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_30])).
% 2.10/1.29  tff(c_116, plain, (![A_95, B_96, D_97]: (k4_tarski('#skF_5'(A_95, B_96, k2_zfmisc_1(A_95, B_96), D_97), '#skF_6'(A_95, B_96, k2_zfmisc_1(A_95, B_96), D_97))=D_97 | ~r2_hidden(D_97, k2_zfmisc_1(A_95, B_96)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.29  tff(c_26, plain, (![B_38, C_39]: (k2_mcart_1(k4_tarski(B_38, C_39))!=k4_tarski(B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.10/1.29  tff(c_152, plain, (![A_101, B_102, D_103]: (k4_tarski('#skF_5'(A_101, B_102, k2_zfmisc_1(A_101, B_102), D_103), '#skF_6'(A_101, B_102, k2_zfmisc_1(A_101, B_102), D_103))!=k2_mcart_1(D_103) | ~r2_hidden(D_103, k2_zfmisc_1(A_101, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_26])).
% 2.10/1.29  tff(c_156, plain, (![D_104, A_105, B_106]: (k2_mcart_1(D_104)!=D_104 | ~r2_hidden(D_104, k2_zfmisc_1(A_105, B_106)) | ~r2_hidden(D_104, k2_zfmisc_1(A_105, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_152])).
% 2.10/1.29  tff(c_178, plain, (k2_mcart_1('#skF_7')!='#skF_7' | ~r2_hidden('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_32, c_156])).
% 2.10/1.29  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_102, c_178])).
% 2.10/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  Inference rules
% 2.10/1.29  ----------------------
% 2.10/1.29  #Ref     : 0
% 2.10/1.29  #Sup     : 37
% 2.10/1.29  #Fact    : 0
% 2.10/1.29  #Define  : 0
% 2.10/1.29  #Split   : 1
% 2.10/1.29  #Chain   : 0
% 2.10/1.29  #Close   : 0
% 2.10/1.29  
% 2.10/1.29  Ordering : KBO
% 2.10/1.29  
% 2.10/1.29  Simplification rules
% 2.10/1.29  ----------------------
% 2.10/1.29  #Subsume      : 2
% 2.10/1.29  #Demod        : 4
% 2.10/1.29  #Tautology    : 10
% 2.10/1.29  #SimpNegUnit  : 0
% 2.10/1.29  #BackRed      : 0
% 2.10/1.29  
% 2.10/1.29  #Partial instantiations: 0
% 2.10/1.29  #Strategies tried      : 1
% 2.10/1.29  
% 2.10/1.30  Timing (in seconds)
% 2.10/1.30  ----------------------
% 2.10/1.30  Preprocessing        : 0.32
% 2.10/1.30  Parsing              : 0.16
% 2.10/1.30  CNF conversion       : 0.03
% 2.10/1.30  Main loop            : 0.19
% 2.10/1.30  Inferencing          : 0.08
% 2.10/1.30  Reduction            : 0.04
% 2.10/1.30  Demodulation         : 0.03
% 2.10/1.30  BG Simplification    : 0.02
% 2.10/1.30  Subsumption          : 0.03
% 2.10/1.30  Abstraction          : 0.02
% 2.10/1.30  MUC search           : 0.00
% 2.10/1.30  Cooper               : 0.00
% 2.10/1.30  Total                : 0.54
% 2.10/1.30  Index Insertion      : 0.00
% 2.10/1.30  Index Deletion       : 0.00
% 2.10/1.30  Index Matching       : 0.00
% 2.10/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
