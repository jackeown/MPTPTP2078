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

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  64 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(k4_tarski('#skF_1'(A_45,B_46),'#skF_2'(A_45,B_46)),A_45)
      | r1_tarski(A_45,B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_22,C_24,B_23] :
      ( r2_hidden(A_22,k1_relat_1(C_24))
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),k1_relat_1(A_45))
      | r1_tarski(A_45,B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_48,c_16])).

tff(c_14,plain,(
    ! [B_23,C_24,A_22] :
      ( r2_hidden(B_23,k2_relat_1(C_24))
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_69,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_2'(A_45,B_46),k2_relat_1(A_45))
      | r1_tarski(A_45,B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_48,c_14])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4))
      | ~ r2_hidden(B_2,D_4)
      | ~ r2_hidden(A_1,C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_43,B_44),'#skF_2'(A_43,B_44)),B_44)
      | r1_tarski(A_43,B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_522,plain,(
    ! [A_123,C_124,D_125] :
      ( r1_tarski(A_123,k2_zfmisc_1(C_124,D_125))
      | ~ v1_relat_1(A_123)
      | ~ r2_hidden('#skF_2'(A_123,k2_zfmisc_1(C_124,D_125)),D_125)
      | ~ r2_hidden('#skF_1'(A_123,k2_zfmisc_1(C_124,D_125)),C_124) ) ),
    inference(resolution,[status(thm)],[c_2,c_42])).

tff(c_567,plain,(
    ! [A_126,C_127] :
      ( ~ r2_hidden('#skF_1'(A_126,k2_zfmisc_1(C_127,k2_relat_1(A_126))),C_127)
      | r1_tarski(A_126,k2_zfmisc_1(C_127,k2_relat_1(A_126)))
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_69,c_522])).

tff(c_623,plain,(
    ! [A_128] :
      ( r1_tarski(A_128,k2_zfmisc_1(k1_relat_1(A_128),k2_relat_1(A_128)))
      | ~ v1_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_68,c_567])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_633,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_623,c_18])).

tff(c_640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.44  
% 2.50/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.44  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1
% 2.50/1.44  
% 2.50/1.44  %Foreground sorts:
% 2.50/1.44  
% 2.50/1.44  
% 2.50/1.44  %Background operators:
% 2.50/1.44  
% 2.50/1.44  
% 2.50/1.44  %Foreground operators:
% 2.50/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.50/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.50/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.44  
% 2.50/1.45  tff(f_54, negated_conjecture, ~(![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.50/1.45  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 2.50/1.45  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 2.50/1.45  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.50/1.45  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.50/1.45  tff(c_48, plain, (![A_45, B_46]: (r2_hidden(k4_tarski('#skF_1'(A_45, B_46), '#skF_2'(A_45, B_46)), A_45) | r1_tarski(A_45, B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.50/1.45  tff(c_16, plain, (![A_22, C_24, B_23]: (r2_hidden(A_22, k1_relat_1(C_24)) | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.50/1.45  tff(c_68, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), k1_relat_1(A_45)) | r1_tarski(A_45, B_46) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_48, c_16])).
% 2.50/1.45  tff(c_14, plain, (![B_23, C_24, A_22]: (r2_hidden(B_23, k2_relat_1(C_24)) | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.50/1.45  tff(c_69, plain, (![A_45, B_46]: (r2_hidden('#skF_2'(A_45, B_46), k2_relat_1(A_45)) | r1_tarski(A_45, B_46) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_48, c_14])).
% 2.50/1.45  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)) | ~r2_hidden(B_2, D_4) | ~r2_hidden(A_1, C_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.45  tff(c_42, plain, (![A_43, B_44]: (~r2_hidden(k4_tarski('#skF_1'(A_43, B_44), '#skF_2'(A_43, B_44)), B_44) | r1_tarski(A_43, B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.50/1.45  tff(c_522, plain, (![A_123, C_124, D_125]: (r1_tarski(A_123, k2_zfmisc_1(C_124, D_125)) | ~v1_relat_1(A_123) | ~r2_hidden('#skF_2'(A_123, k2_zfmisc_1(C_124, D_125)), D_125) | ~r2_hidden('#skF_1'(A_123, k2_zfmisc_1(C_124, D_125)), C_124))), inference(resolution, [status(thm)], [c_2, c_42])).
% 2.50/1.45  tff(c_567, plain, (![A_126, C_127]: (~r2_hidden('#skF_1'(A_126, k2_zfmisc_1(C_127, k2_relat_1(A_126))), C_127) | r1_tarski(A_126, k2_zfmisc_1(C_127, k2_relat_1(A_126))) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_69, c_522])).
% 2.50/1.45  tff(c_623, plain, (![A_128]: (r1_tarski(A_128, k2_zfmisc_1(k1_relat_1(A_128), k2_relat_1(A_128))) | ~v1_relat_1(A_128))), inference(resolution, [status(thm)], [c_68, c_567])).
% 2.50/1.45  tff(c_18, plain, (~r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.50/1.45  tff(c_633, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_623, c_18])).
% 2.50/1.45  tff(c_640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_633])).
% 2.50/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.45  
% 2.50/1.45  Inference rules
% 2.50/1.45  ----------------------
% 2.50/1.45  #Ref     : 0
% 2.50/1.45  #Sup     : 144
% 2.50/1.45  #Fact    : 0
% 2.50/1.45  #Define  : 0
% 2.50/1.45  #Split   : 0
% 2.50/1.45  #Chain   : 0
% 2.50/1.45  #Close   : 0
% 2.50/1.45  
% 2.50/1.45  Ordering : KBO
% 2.50/1.45  
% 2.50/1.45  Simplification rules
% 2.50/1.45  ----------------------
% 2.50/1.45  #Subsume      : 17
% 2.50/1.45  #Demod        : 3
% 2.50/1.45  #Tautology    : 3
% 2.50/1.45  #SimpNegUnit  : 0
% 2.50/1.45  #BackRed      : 0
% 2.50/1.45  
% 2.50/1.45  #Partial instantiations: 0
% 2.50/1.45  #Strategies tried      : 1
% 2.50/1.45  
% 2.50/1.45  Timing (in seconds)
% 2.50/1.45  ----------------------
% 2.50/1.46  Preprocessing        : 0.29
% 2.50/1.46  Parsing              : 0.17
% 2.50/1.46  CNF conversion       : 0.02
% 2.50/1.46  Main loop            : 0.38
% 2.50/1.46  Inferencing          : 0.16
% 2.50/1.46  Reduction            : 0.08
% 2.50/1.46  Demodulation         : 0.05
% 2.50/1.46  BG Simplification    : 0.02
% 2.50/1.46  Subsumption          : 0.09
% 2.50/1.46  Abstraction          : 0.02
% 2.50/1.46  MUC search           : 0.00
% 2.50/1.46  Cooper               : 0.00
% 2.50/1.46  Total                : 0.69
% 2.50/1.46  Index Insertion      : 0.00
% 2.50/1.46  Index Deletion       : 0.00
% 2.50/1.46  Index Matching       : 0.00
% 2.50/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
