%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:36 EST 2020

% Result     : Theorem 16.75s
% Output     : CNFRefutation 16.84s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  46 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_6 > #skF_3 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [C_42,A_43,D_44] :
      ( r2_hidden(C_42,k3_tarski(A_43))
      | ~ r2_hidden(D_44,A_43)
      | ~ r2_hidden(C_42,D_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_147,plain,(
    ! [C_64,A_65,B_66] :
      ( r2_hidden(C_64,k3_tarski(A_65))
      | ~ r2_hidden(C_64,'#skF_1'(A_65,B_66))
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_29414,plain,(
    ! [A_788,B_789,B_790] :
      ( r2_hidden('#skF_1'('#skF_1'(A_788,B_789),B_790),k3_tarski(A_788))
      | r1_tarski(A_788,B_789)
      | r1_tarski('#skF_1'(A_788,B_789),B_790) ) ),
    inference(resolution,[status(thm)],[c_6,c_147])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_29480,plain,(
    ! [A_791,B_792] :
      ( r1_tarski(A_791,B_792)
      | r1_tarski('#skF_1'(A_791,B_792),k3_tarski(A_791)) ) ),
    inference(resolution,[status(thm)],[c_29414,c_4])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden('#skF_1'(A_36,B_37),B_37)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [A_36,A_6] :
      ( r1_tarski(A_36,k1_zfmisc_1(A_6))
      | ~ r1_tarski('#skF_1'(A_36,k1_zfmisc_1(A_6)),A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_51])).

tff(c_29526,plain,(
    ! [A_791] : r1_tarski(A_791,k1_zfmisc_1(k3_tarski(A_791))) ),
    inference(resolution,[status(thm)],[c_29480,c_61])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_8',k1_zfmisc_1(k3_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_29530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29526,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:48:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.75/7.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.84/7.86  
% 16.84/7.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.84/7.86  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_6 > #skF_3 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 16.84/7.86  
% 16.84/7.86  %Foreground sorts:
% 16.84/7.86  
% 16.84/7.86  
% 16.84/7.86  %Background operators:
% 16.84/7.86  
% 16.84/7.86  
% 16.84/7.86  %Foreground operators:
% 16.84/7.86  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 16.84/7.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.84/7.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.84/7.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.84/7.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.84/7.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.84/7.86  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 16.84/7.86  tff('#skF_8', type, '#skF_8': $i).
% 16.84/7.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.84/7.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.84/7.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.84/7.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.84/7.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.84/7.86  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 16.84/7.86  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 16.84/7.86  
% 16.84/7.87  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 16.84/7.87  tff(f_49, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 16.84/7.87  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 16.84/7.87  tff(f_52, negated_conjecture, ~(![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 16.84/7.87  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.84/7.87  tff(c_70, plain, (![C_42, A_43, D_44]: (r2_hidden(C_42, k3_tarski(A_43)) | ~r2_hidden(D_44, A_43) | ~r2_hidden(C_42, D_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.84/7.87  tff(c_147, plain, (![C_64, A_65, B_66]: (r2_hidden(C_64, k3_tarski(A_65)) | ~r2_hidden(C_64, '#skF_1'(A_65, B_66)) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_6, c_70])).
% 16.84/7.87  tff(c_29414, plain, (![A_788, B_789, B_790]: (r2_hidden('#skF_1'('#skF_1'(A_788, B_789), B_790), k3_tarski(A_788)) | r1_tarski(A_788, B_789) | r1_tarski('#skF_1'(A_788, B_789), B_790))), inference(resolution, [status(thm)], [c_6, c_147])).
% 16.84/7.87  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.84/7.87  tff(c_29480, plain, (![A_791, B_792]: (r1_tarski(A_791, B_792) | r1_tarski('#skF_1'(A_791, B_792), k3_tarski(A_791)))), inference(resolution, [status(thm)], [c_29414, c_4])).
% 16.84/7.87  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.84/7.87  tff(c_51, plain, (![A_36, B_37]: (~r2_hidden('#skF_1'(A_36, B_37), B_37) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.84/7.87  tff(c_61, plain, (![A_36, A_6]: (r1_tarski(A_36, k1_zfmisc_1(A_6)) | ~r1_tarski('#skF_1'(A_36, k1_zfmisc_1(A_6)), A_6))), inference(resolution, [status(thm)], [c_10, c_51])).
% 16.84/7.87  tff(c_29526, plain, (![A_791]: (r1_tarski(A_791, k1_zfmisc_1(k3_tarski(A_791))))), inference(resolution, [status(thm)], [c_29480, c_61])).
% 16.84/7.87  tff(c_38, plain, (~r1_tarski('#skF_8', k1_zfmisc_1(k3_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.84/7.87  tff(c_29530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29526, c_38])).
% 16.84/7.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.84/7.87  
% 16.84/7.87  Inference rules
% 16.84/7.87  ----------------------
% 16.84/7.87  #Ref     : 0
% 16.84/7.87  #Sup     : 7245
% 16.84/7.87  #Fact    : 0
% 16.84/7.87  #Define  : 0
% 16.84/7.87  #Split   : 0
% 16.84/7.87  #Chain   : 0
% 16.84/7.87  #Close   : 0
% 16.84/7.87  
% 16.84/7.87  Ordering : KBO
% 16.84/7.87  
% 16.89/7.87  Simplification rules
% 16.89/7.87  ----------------------
% 16.89/7.87  #Subsume      : 395
% 16.89/7.87  #Demod        : 265
% 16.89/7.87  #Tautology    : 293
% 16.89/7.87  #SimpNegUnit  : 0
% 16.89/7.87  #BackRed      : 1
% 16.89/7.87  
% 16.89/7.87  #Partial instantiations: 0
% 16.89/7.87  #Strategies tried      : 1
% 16.89/7.87  
% 16.89/7.87  Timing (in seconds)
% 16.89/7.87  ----------------------
% 16.89/7.87  Preprocessing        : 0.28
% 16.89/7.87  Parsing              : 0.14
% 16.89/7.87  CNF conversion       : 0.03
% 16.89/7.87  Main loop            : 6.82
% 16.89/7.87  Inferencing          : 0.93
% 16.89/7.87  Reduction            : 1.35
% 16.89/7.87  Demodulation         : 1.05
% 16.89/7.87  BG Simplification    : 0.15
% 16.89/7.87  Subsumption          : 3.95
% 16.89/7.87  Abstraction          : 0.21
% 16.89/7.88  MUC search           : 0.00
% 16.89/7.88  Cooper               : 0.00
% 16.89/7.88  Total                : 7.12
% 16.89/7.88  Index Insertion      : 0.00
% 16.89/7.88  Index Deletion       : 0.00
% 16.89/7.88  Index Matching       : 0.00
% 16.89/7.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
