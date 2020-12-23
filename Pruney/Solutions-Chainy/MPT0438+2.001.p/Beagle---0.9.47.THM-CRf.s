%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:17 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  66 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_2 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_3 > #skF_7

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

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

tff(c_38,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_57,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(k4_tarski('#skF_7'(A_70,B_71),'#skF_8'(A_70,B_71)),A_70)
      | r1_tarski(A_70,B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    ! [A_52,C_54,B_53] :
      ( r2_hidden(A_52,k1_relat_1(C_54))
      | ~ r2_hidden(k4_tarski(A_52,B_53),C_54)
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_69,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_7'(A_70,B_71),k1_relat_1(A_70))
      | r1_tarski(A_70,B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_57,c_34])).

tff(c_32,plain,(
    ! [B_53,C_54,A_52] :
      ( r2_hidden(B_53,k2_relat_1(C_54))
      | ~ r2_hidden(k4_tarski(A_52,B_53),C_54)
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_8'(A_70,B_71),k2_relat_1(A_70))
      | r1_tarski(A_70,B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_57,c_32])).

tff(c_2,plain,(
    ! [E_33,F_34,A_1,B_2] :
      ( r2_hidden(k4_tarski(E_33,F_34),k2_zfmisc_1(A_1,B_2))
      | ~ r2_hidden(F_34,B_2)
      | ~ r2_hidden(E_33,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    ! [A_68,B_69] :
      ( ~ r2_hidden(k4_tarski('#skF_7'(A_68,B_69),'#skF_8'(A_68,B_69)),B_69)
      | r1_tarski(A_68,B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1073,plain,(
    ! [A_241,A_242,B_243] :
      ( r1_tarski(A_241,k2_zfmisc_1(A_242,B_243))
      | ~ v1_relat_1(A_241)
      | ~ r2_hidden('#skF_8'(A_241,k2_zfmisc_1(A_242,B_243)),B_243)
      | ~ r2_hidden('#skF_7'(A_241,k2_zfmisc_1(A_242,B_243)),A_242) ) ),
    inference(resolution,[status(thm)],[c_2,c_51])).

tff(c_1114,plain,(
    ! [A_244,A_245] :
      ( ~ r2_hidden('#skF_7'(A_244,k2_zfmisc_1(A_245,k2_relat_1(A_244))),A_245)
      | r1_tarski(A_244,k2_zfmisc_1(A_245,k2_relat_1(A_244)))
      | ~ v1_relat_1(A_244) ) ),
    inference(resolution,[status(thm)],[c_70,c_1073])).

tff(c_1165,plain,(
    ! [A_246] :
      ( r1_tarski(A_246,k2_zfmisc_1(k1_relat_1(A_246),k2_relat_1(A_246)))
      | ~ v1_relat_1(A_246) ) ),
    inference(resolution,[status(thm)],[c_69,c_1114])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_9',k2_zfmisc_1(k1_relat_1('#skF_9'),k2_relat_1('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1171,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1165,c_36])).

tff(c_1176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:16:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.57  
% 3.45/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.57  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_2 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_3 > #skF_7
% 3.45/1.57  
% 3.45/1.57  %Foreground sorts:
% 3.45/1.57  
% 3.45/1.57  
% 3.45/1.57  %Background operators:
% 3.45/1.57  
% 3.45/1.57  
% 3.45/1.57  %Foreground operators:
% 3.45/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.45/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.45/1.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.45/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.45/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.45/1.57  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.45/1.57  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.45/1.57  tff('#skF_9', type, '#skF_9': $i).
% 3.45/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.57  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.45/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.45/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.45/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.45/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.57  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.45/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.45/1.57  
% 3.45/1.58  tff(f_60, negated_conjecture, ~(![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.45/1.58  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 3.45/1.58  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 3.45/1.58  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.45/1.58  tff(c_38, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.45/1.58  tff(c_57, plain, (![A_70, B_71]: (r2_hidden(k4_tarski('#skF_7'(A_70, B_71), '#skF_8'(A_70, B_71)), A_70) | r1_tarski(A_70, B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.45/1.58  tff(c_34, plain, (![A_52, C_54, B_53]: (r2_hidden(A_52, k1_relat_1(C_54)) | ~r2_hidden(k4_tarski(A_52, B_53), C_54) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.45/1.58  tff(c_69, plain, (![A_70, B_71]: (r2_hidden('#skF_7'(A_70, B_71), k1_relat_1(A_70)) | r1_tarski(A_70, B_71) | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_57, c_34])).
% 3.45/1.58  tff(c_32, plain, (![B_53, C_54, A_52]: (r2_hidden(B_53, k2_relat_1(C_54)) | ~r2_hidden(k4_tarski(A_52, B_53), C_54) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.45/1.58  tff(c_70, plain, (![A_70, B_71]: (r2_hidden('#skF_8'(A_70, B_71), k2_relat_1(A_70)) | r1_tarski(A_70, B_71) | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_57, c_32])).
% 3.45/1.58  tff(c_2, plain, (![E_33, F_34, A_1, B_2]: (r2_hidden(k4_tarski(E_33, F_34), k2_zfmisc_1(A_1, B_2)) | ~r2_hidden(F_34, B_2) | ~r2_hidden(E_33, A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.45/1.58  tff(c_51, plain, (![A_68, B_69]: (~r2_hidden(k4_tarski('#skF_7'(A_68, B_69), '#skF_8'(A_68, B_69)), B_69) | r1_tarski(A_68, B_69) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.45/1.58  tff(c_1073, plain, (![A_241, A_242, B_243]: (r1_tarski(A_241, k2_zfmisc_1(A_242, B_243)) | ~v1_relat_1(A_241) | ~r2_hidden('#skF_8'(A_241, k2_zfmisc_1(A_242, B_243)), B_243) | ~r2_hidden('#skF_7'(A_241, k2_zfmisc_1(A_242, B_243)), A_242))), inference(resolution, [status(thm)], [c_2, c_51])).
% 3.45/1.58  tff(c_1114, plain, (![A_244, A_245]: (~r2_hidden('#skF_7'(A_244, k2_zfmisc_1(A_245, k2_relat_1(A_244))), A_245) | r1_tarski(A_244, k2_zfmisc_1(A_245, k2_relat_1(A_244))) | ~v1_relat_1(A_244))), inference(resolution, [status(thm)], [c_70, c_1073])).
% 3.45/1.58  tff(c_1165, plain, (![A_246]: (r1_tarski(A_246, k2_zfmisc_1(k1_relat_1(A_246), k2_relat_1(A_246))) | ~v1_relat_1(A_246))), inference(resolution, [status(thm)], [c_69, c_1114])).
% 3.45/1.58  tff(c_36, plain, (~r1_tarski('#skF_9', k2_zfmisc_1(k1_relat_1('#skF_9'), k2_relat_1('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.45/1.58  tff(c_1171, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1165, c_36])).
% 3.45/1.58  tff(c_1176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1171])).
% 3.45/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.58  
% 3.45/1.58  Inference rules
% 3.45/1.58  ----------------------
% 3.45/1.58  #Ref     : 0
% 3.45/1.58  #Sup     : 279
% 3.45/1.58  #Fact    : 0
% 3.45/1.58  #Define  : 0
% 3.45/1.58  #Split   : 0
% 3.45/1.58  #Chain   : 0
% 3.45/1.58  #Close   : 0
% 3.45/1.58  
% 3.45/1.58  Ordering : KBO
% 3.45/1.58  
% 3.45/1.58  Simplification rules
% 3.45/1.58  ----------------------
% 3.45/1.58  #Subsume      : 13
% 3.45/1.58  #Demod        : 3
% 3.45/1.58  #Tautology    : 5
% 3.45/1.58  #SimpNegUnit  : 0
% 3.45/1.58  #BackRed      : 0
% 3.45/1.58  
% 3.45/1.58  #Partial instantiations: 0
% 3.45/1.58  #Strategies tried      : 1
% 3.45/1.58  
% 3.45/1.58  Timing (in seconds)
% 3.45/1.58  ----------------------
% 3.45/1.58  Preprocessing        : 0.30
% 3.45/1.58  Parsing              : 0.15
% 3.45/1.58  CNF conversion       : 0.03
% 3.45/1.58  Main loop            : 0.53
% 3.45/1.58  Inferencing          : 0.20
% 3.45/1.58  Reduction            : 0.11
% 3.45/1.58  Demodulation         : 0.07
% 3.45/1.58  BG Simplification    : 0.03
% 3.45/1.58  Subsumption          : 0.14
% 3.45/1.58  Abstraction          : 0.03
% 3.45/1.58  MUC search           : 0.00
% 3.45/1.58  Cooper               : 0.00
% 3.45/1.58  Total                : 0.85
% 3.45/1.58  Index Insertion      : 0.00
% 3.45/1.58  Index Deletion       : 0.00
% 3.45/1.58  Index Matching       : 0.00
% 3.45/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
