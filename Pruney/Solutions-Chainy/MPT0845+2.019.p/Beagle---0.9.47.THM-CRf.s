%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:47 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   43 (  46 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  68 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_76,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_180,plain,(
    ! [A_74,B_75] :
      ( r2_hidden(k4_tarski('#skF_3'(A_74,B_75),'#skF_4'(A_74,B_75)),A_74)
      | r2_hidden('#skF_5'(A_74,B_75),B_75)
      | k1_relat_1(A_74) = B_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_69,plain,(
    ! [A_40,B_41] : ~ r2_hidden(A_40,k2_zfmisc_1(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_72,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_195,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_75),B_75)
      | k1_relat_1(k1_xboole_0) = B_75 ) ),
    inference(resolution,[status(thm)],[c_180,c_72])).

tff(c_200,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_75),B_75)
      | k1_xboole_0 = B_75 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_195])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,(
    ! [D_63,A_64,B_65] :
      ( ~ r2_hidden(D_63,'#skF_2'(A_64,B_65))
      | ~ r2_hidden(D_63,B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_248,plain,(
    ! [A_85,B_86,B_87] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_85,B_86),B_87),B_86)
      | ~ r2_hidden(A_85,B_86)
      | r1_xboole_0('#skF_2'(A_85,B_86),B_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_135])).

tff(c_254,plain,(
    ! [A_88,B_89] :
      ( ~ r2_hidden(A_88,B_89)
      | r1_xboole_0('#skF_2'(A_88,B_89),B_89) ) ),
    inference(resolution,[status(thm)],[c_4,c_248])).

tff(c_113,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [B_37] :
      ( ~ r1_xboole_0(B_37,'#skF_7')
      | ~ r2_hidden(B_37,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_122,plain,(
    ! [A_52] :
      ( ~ r1_xboole_0('#skF_2'(A_52,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_52,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_113,c_36])).

tff(c_263,plain,(
    ! [A_90] : ~ r2_hidden(A_90,'#skF_7') ),
    inference(resolution,[status(thm)],[c_254,c_122])).

tff(c_269,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_200,c_263])).

tff(c_293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.71  
% 2.36/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.71  %$ r2_hidden > r1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.36/1.71  
% 2.36/1.71  %Foreground sorts:
% 2.36/1.71  
% 2.36/1.71  
% 2.36/1.71  %Background operators:
% 2.36/1.71  
% 2.36/1.71  
% 2.36/1.71  %Foreground operators:
% 2.36/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.71  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.36/1.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.36/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.71  tff('#skF_7', type, '#skF_7': $i).
% 2.36/1.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.36/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.36/1.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.36/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.36/1.71  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.36/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.71  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.36/1.71  
% 2.36/1.73  tff(f_87, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.36/1.73  tff(f_76, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.36/1.73  tff(f_73, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.36/1.73  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.36/1.73  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.36/1.73  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.36/1.73  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 2.36/1.73  tff(c_38, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.36/1.73  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.36/1.73  tff(c_180, plain, (![A_74, B_75]: (r2_hidden(k4_tarski('#skF_3'(A_74, B_75), '#skF_4'(A_74, B_75)), A_74) | r2_hidden('#skF_5'(A_74, B_75), B_75) | k1_relat_1(A_74)=B_75)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.36/1.73  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.36/1.73  tff(c_69, plain, (![A_40, B_41]: (~r2_hidden(A_40, k2_zfmisc_1(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.36/1.73  tff(c_72, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_69])).
% 2.36/1.73  tff(c_195, plain, (![B_75]: (r2_hidden('#skF_5'(k1_xboole_0, B_75), B_75) | k1_relat_1(k1_xboole_0)=B_75)), inference(resolution, [status(thm)], [c_180, c_72])).
% 2.36/1.73  tff(c_200, plain, (![B_75]: (r2_hidden('#skF_5'(k1_xboole_0, B_75), B_75) | k1_xboole_0=B_75)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_195])).
% 2.36/1.73  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.73  tff(c_135, plain, (![D_63, A_64, B_65]: (~r2_hidden(D_63, '#skF_2'(A_64, B_65)) | ~r2_hidden(D_63, B_65) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.36/1.73  tff(c_248, plain, (![A_85, B_86, B_87]: (~r2_hidden('#skF_1'('#skF_2'(A_85, B_86), B_87), B_86) | ~r2_hidden(A_85, B_86) | r1_xboole_0('#skF_2'(A_85, B_86), B_87))), inference(resolution, [status(thm)], [c_6, c_135])).
% 2.36/1.73  tff(c_254, plain, (![A_88, B_89]: (~r2_hidden(A_88, B_89) | r1_xboole_0('#skF_2'(A_88, B_89), B_89))), inference(resolution, [status(thm)], [c_4, c_248])).
% 2.36/1.73  tff(c_113, plain, (![A_52, B_53]: (r2_hidden('#skF_2'(A_52, B_53), B_53) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.36/1.73  tff(c_36, plain, (![B_37]: (~r1_xboole_0(B_37, '#skF_7') | ~r2_hidden(B_37, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.36/1.73  tff(c_122, plain, (![A_52]: (~r1_xboole_0('#skF_2'(A_52, '#skF_7'), '#skF_7') | ~r2_hidden(A_52, '#skF_7'))), inference(resolution, [status(thm)], [c_113, c_36])).
% 2.36/1.73  tff(c_263, plain, (![A_90]: (~r2_hidden(A_90, '#skF_7'))), inference(resolution, [status(thm)], [c_254, c_122])).
% 2.36/1.73  tff(c_269, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_200, c_263])).
% 2.36/1.73  tff(c_293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_269])).
% 2.36/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.73  
% 2.36/1.73  Inference rules
% 2.36/1.73  ----------------------
% 2.36/1.73  #Ref     : 0
% 2.36/1.73  #Sup     : 50
% 2.36/1.73  #Fact    : 0
% 2.36/1.73  #Define  : 0
% 2.36/1.73  #Split   : 0
% 2.36/1.73  #Chain   : 0
% 2.36/1.73  #Close   : 0
% 2.36/1.73  
% 2.36/1.73  Ordering : KBO
% 2.36/1.73  
% 2.36/1.73  Simplification rules
% 2.36/1.73  ----------------------
% 2.36/1.73  #Subsume      : 11
% 2.36/1.73  #Demod        : 4
% 2.36/1.73  #Tautology    : 15
% 2.36/1.73  #SimpNegUnit  : 4
% 2.36/1.73  #BackRed      : 0
% 2.36/1.73  
% 2.36/1.73  #Partial instantiations: 0
% 2.36/1.73  #Strategies tried      : 1
% 2.36/1.73  
% 2.36/1.73  Timing (in seconds)
% 2.36/1.73  ----------------------
% 2.36/1.73  Preprocessing        : 0.47
% 2.36/1.73  Parsing              : 0.25
% 2.36/1.73  CNF conversion       : 0.04
% 2.36/1.73  Main loop            : 0.29
% 2.36/1.73  Inferencing          : 0.12
% 2.36/1.73  Reduction            : 0.07
% 2.36/1.73  Demodulation         : 0.05
% 2.36/1.73  BG Simplification    : 0.02
% 2.36/1.73  Subsumption          : 0.05
% 2.36/1.73  Abstraction          : 0.01
% 2.36/1.73  MUC search           : 0.00
% 2.36/1.73  Cooper               : 0.00
% 2.36/1.74  Total                : 0.81
% 2.36/1.74  Index Insertion      : 0.00
% 2.36/1.74  Index Deletion       : 0.00
% 2.36/1.74  Index Matching       : 0.00
% 2.36/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
