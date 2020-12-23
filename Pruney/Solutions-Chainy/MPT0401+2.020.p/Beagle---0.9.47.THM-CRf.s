%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:40 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  40 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_45,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_25] : k3_tarski(k1_tarski(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    r1_setfam_1('#skF_2',k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,k3_tarski(B_27))
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k3_tarski(A_28),k3_tarski(B_29))
      | ~ r1_setfam_1(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_84,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(A_50,C_51)
      | ~ r1_tarski(B_52,C_51)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_60,B_61,A_62] :
      ( r1_tarski(A_60,k3_tarski(B_61))
      | ~ r1_tarski(A_60,k3_tarski(A_62))
      | ~ r1_setfam_1(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_20,c_84])).

tff(c_135,plain,(
    ! [A_63,B_64,B_65] :
      ( r1_tarski(A_63,k3_tarski(B_64))
      | ~ r1_setfam_1(B_65,B_64)
      | ~ r2_hidden(A_63,B_65) ) ),
    inference(resolution,[status(thm)],[c_18,c_119])).

tff(c_137,plain,(
    ! [A_63] :
      ( r1_tarski(A_63,k3_tarski(k1_tarski('#skF_1')))
      | ~ r2_hidden(A_63,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_135])).

tff(c_140,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,'#skF_1')
      | ~ r2_hidden(A_66,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_137])).

tff(c_143,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_140])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:50:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  %$ r2_hidden > r1_tarski > r1_setfam_1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.90/1.18  
% 1.90/1.18  %Foreground sorts:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Background operators:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Foreground operators:
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.18  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.90/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.90/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.90/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.18  
% 1.94/1.19  tff(f_61, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_setfam_1)).
% 1.94/1.19  tff(f_45, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 1.94/1.19  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 1.94/1.19  tff(f_53, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 1.94/1.19  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.94/1.19  tff(c_22, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.94/1.19  tff(c_24, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.94/1.19  tff(c_16, plain, (![A_25]: (k3_tarski(k1_tarski(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.19  tff(c_26, plain, (r1_setfam_1('#skF_2', k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.94/1.19  tff(c_18, plain, (![A_26, B_27]: (r1_tarski(A_26, k3_tarski(B_27)) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.94/1.19  tff(c_20, plain, (![A_28, B_29]: (r1_tarski(k3_tarski(A_28), k3_tarski(B_29)) | ~r1_setfam_1(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.94/1.19  tff(c_84, plain, (![A_50, C_51, B_52]: (r1_tarski(A_50, C_51) | ~r1_tarski(B_52, C_51) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.19  tff(c_119, plain, (![A_60, B_61, A_62]: (r1_tarski(A_60, k3_tarski(B_61)) | ~r1_tarski(A_60, k3_tarski(A_62)) | ~r1_setfam_1(A_62, B_61))), inference(resolution, [status(thm)], [c_20, c_84])).
% 1.94/1.19  tff(c_135, plain, (![A_63, B_64, B_65]: (r1_tarski(A_63, k3_tarski(B_64)) | ~r1_setfam_1(B_65, B_64) | ~r2_hidden(A_63, B_65))), inference(resolution, [status(thm)], [c_18, c_119])).
% 1.94/1.19  tff(c_137, plain, (![A_63]: (r1_tarski(A_63, k3_tarski(k1_tarski('#skF_1'))) | ~r2_hidden(A_63, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_135])).
% 1.94/1.19  tff(c_140, plain, (![A_66]: (r1_tarski(A_66, '#skF_1') | ~r2_hidden(A_66, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_137])).
% 1.94/1.19  tff(c_143, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_140])).
% 1.94/1.19  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_143])).
% 1.94/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  Inference rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Ref     : 0
% 1.94/1.19  #Sup     : 30
% 1.94/1.19  #Fact    : 0
% 1.94/1.19  #Define  : 0
% 1.94/1.19  #Split   : 0
% 1.94/1.19  #Chain   : 0
% 1.94/1.19  #Close   : 0
% 1.94/1.19  
% 1.94/1.19  Ordering : KBO
% 1.94/1.19  
% 1.94/1.19  Simplification rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Subsume      : 1
% 1.94/1.19  #Demod        : 1
% 1.94/1.19  #Tautology    : 10
% 1.94/1.19  #SimpNegUnit  : 1
% 1.94/1.19  #BackRed      : 0
% 1.94/1.19  
% 1.94/1.19  #Partial instantiations: 0
% 1.94/1.19  #Strategies tried      : 1
% 1.94/1.19  
% 1.94/1.19  Timing (in seconds)
% 1.94/1.19  ----------------------
% 1.94/1.19  Preprocessing        : 0.29
% 1.94/1.19  Parsing              : 0.16
% 1.94/1.19  CNF conversion       : 0.02
% 1.94/1.19  Main loop            : 0.14
% 1.94/1.19  Inferencing          : 0.06
% 1.94/1.19  Reduction            : 0.04
% 1.94/1.19  Demodulation         : 0.03
% 1.94/1.19  BG Simplification    : 0.01
% 1.94/1.19  Subsumption          : 0.03
% 1.94/1.19  Abstraction          : 0.01
% 1.94/1.19  MUC search           : 0.00
% 1.94/1.19  Cooper               : 0.00
% 1.94/1.19  Total                : 0.46
% 1.94/1.19  Index Insertion      : 0.00
% 1.94/1.20  Index Deletion       : 0.00
% 1.94/1.20  Index Matching       : 0.00
% 1.94/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
