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
% DateTime   : Thu Dec  3 10:02:08 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  47 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [A_18] :
      ( k10_relat_1(A_18,k2_relat_1(A_18)) = k1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden(k4_tarski(A_55,'#skF_2'(A_55,B_56,C_57)),C_57)
      | ~ r2_hidden(A_55,k10_relat_1(C_57,B_56))
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_92,plain,(
    ! [A_55,C_8,D_9,B_56] :
      ( r2_hidden(A_55,C_8)
      | ~ r2_hidden(A_55,k10_relat_1(k2_zfmisc_1(C_8,D_9),B_56))
      | ~ v1_relat_1(k2_zfmisc_1(C_8,D_9)) ) ),
    inference(resolution,[status(thm)],[c_84,c_12])).

tff(c_121,plain,(
    ! [A_62,C_63,D_64,B_65] :
      ( r2_hidden(A_62,C_63)
      | ~ r2_hidden(A_62,k10_relat_1(k2_zfmisc_1(C_63,D_64),B_65)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_92])).

tff(c_141,plain,(
    ! [A_62,C_63,D_64] :
      ( r2_hidden(A_62,C_63)
      | ~ r2_hidden(A_62,k1_relat_1(k2_zfmisc_1(C_63,D_64)))
      | ~ v1_relat_1(k2_zfmisc_1(C_63,D_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_121])).

tff(c_148,plain,(
    ! [A_66,C_67,D_68] :
      ( r2_hidden(A_66,C_67)
      | ~ r2_hidden(A_66,k1_relat_1(k2_zfmisc_1(C_67,D_68))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_141])).

tff(c_174,plain,(
    ! [C_73,D_74,B_75] :
      ( r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(C_73,D_74)),B_75),C_73)
      | r1_tarski(k1_relat_1(k2_zfmisc_1(C_73,D_74)),B_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_195,plain,(
    ! [C_73,D_74] : r1_tarski(k1_relat_1(k2_zfmisc_1(C_73,D_74)),C_73) ),
    inference(resolution,[status(thm)],[c_174,c_4])).

tff(c_26,plain,(
    ~ r1_tarski(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.17  
% 1.95/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 1.95/1.18  
% 1.95/1.18  %Foreground sorts:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Background operators:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Foreground operators:
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.95/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.95/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.95/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.18  
% 1.95/1.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.95/1.18  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.95/1.18  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 1.95/1.18  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.95/1.18  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.95/1.18  tff(f_58, negated_conjecture, ~(![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 1.95/1.18  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.18  tff(c_14, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.95/1.18  tff(c_24, plain, (![A_18]: (k10_relat_1(A_18, k2_relat_1(A_18))=k1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.18  tff(c_84, plain, (![A_55, B_56, C_57]: (r2_hidden(k4_tarski(A_55, '#skF_2'(A_55, B_56, C_57)), C_57) | ~r2_hidden(A_55, k10_relat_1(C_57, B_56)) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.18  tff(c_12, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.95/1.18  tff(c_92, plain, (![A_55, C_8, D_9, B_56]: (r2_hidden(A_55, C_8) | ~r2_hidden(A_55, k10_relat_1(k2_zfmisc_1(C_8, D_9), B_56)) | ~v1_relat_1(k2_zfmisc_1(C_8, D_9)))), inference(resolution, [status(thm)], [c_84, c_12])).
% 1.95/1.18  tff(c_121, plain, (![A_62, C_63, D_64, B_65]: (r2_hidden(A_62, C_63) | ~r2_hidden(A_62, k10_relat_1(k2_zfmisc_1(C_63, D_64), B_65)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_92])).
% 1.95/1.18  tff(c_141, plain, (![A_62, C_63, D_64]: (r2_hidden(A_62, C_63) | ~r2_hidden(A_62, k1_relat_1(k2_zfmisc_1(C_63, D_64))) | ~v1_relat_1(k2_zfmisc_1(C_63, D_64)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_121])).
% 1.95/1.18  tff(c_148, plain, (![A_66, C_67, D_68]: (r2_hidden(A_66, C_67) | ~r2_hidden(A_66, k1_relat_1(k2_zfmisc_1(C_67, D_68))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_141])).
% 1.95/1.18  tff(c_174, plain, (![C_73, D_74, B_75]: (r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(C_73, D_74)), B_75), C_73) | r1_tarski(k1_relat_1(k2_zfmisc_1(C_73, D_74)), B_75))), inference(resolution, [status(thm)], [c_6, c_148])).
% 1.95/1.18  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.18  tff(c_195, plain, (![C_73, D_74]: (r1_tarski(k1_relat_1(k2_zfmisc_1(C_73, D_74)), C_73))), inference(resolution, [status(thm)], [c_174, c_4])).
% 1.95/1.18  tff(c_26, plain, (~r1_tarski(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.95/1.18  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_195, c_26])).
% 1.95/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  
% 1.95/1.18  Inference rules
% 1.95/1.18  ----------------------
% 1.95/1.18  #Ref     : 0
% 1.95/1.18  #Sup     : 36
% 1.95/1.18  #Fact    : 0
% 1.95/1.18  #Define  : 0
% 1.95/1.19  #Split   : 0
% 1.95/1.19  #Chain   : 0
% 1.95/1.19  #Close   : 0
% 1.95/1.19  
% 1.95/1.19  Ordering : KBO
% 1.95/1.19  
% 1.95/1.19  Simplification rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Subsume      : 1
% 1.95/1.19  #Demod        : 4
% 1.95/1.19  #Tautology    : 5
% 1.95/1.19  #SimpNegUnit  : 0
% 1.95/1.19  #BackRed      : 1
% 1.95/1.19  
% 1.95/1.19  #Partial instantiations: 0
% 1.95/1.19  #Strategies tried      : 1
% 1.95/1.19  
% 1.95/1.19  Timing (in seconds)
% 1.95/1.19  ----------------------
% 1.95/1.19  Preprocessing        : 0.27
% 1.95/1.19  Parsing              : 0.15
% 1.95/1.19  CNF conversion       : 0.02
% 1.95/1.19  Main loop            : 0.17
% 1.95/1.19  Inferencing          : 0.07
% 1.95/1.19  Reduction            : 0.04
% 1.95/1.19  Demodulation         : 0.03
% 1.95/1.19  BG Simplification    : 0.01
% 1.95/1.19  Subsumption          : 0.04
% 1.95/1.19  Abstraction          : 0.01
% 1.95/1.19  MUC search           : 0.00
% 1.95/1.19  Cooper               : 0.00
% 1.95/1.19  Total                : 0.47
% 1.95/1.19  Index Insertion      : 0.00
% 1.95/1.19  Index Deletion       : 0.00
% 1.95/1.19  Index Matching       : 0.00
% 1.95/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
