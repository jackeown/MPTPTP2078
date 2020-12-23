%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:37 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   37 (  37 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_36,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_26,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_26])).

tff(c_128,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden(k4_tarski('#skF_2'(A_45,B_46,C_47),A_45),C_47)
      | ~ r2_hidden(A_45,k9_relat_1(C_47,B_46))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_41,plain,(
    ! [A_24,C_25,B_26] :
      ( ~ r2_hidden(A_24,C_25)
      | ~ r1_xboole_0(k2_tarski(A_24,B_26),C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    ! [A_24] : ~ r2_hidden(A_24,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_140,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden(A_45,k9_relat_1(k1_xboole_0,B_46))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_128,c_46])).

tff(c_146,plain,(
    ! [A_48,B_49] : ~ r2_hidden(A_48,k9_relat_1(k1_xboole_0,B_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_140])).

tff(c_169,plain,(
    ! [B_49] : k9_relat_1(k1_xboole_0,B_49) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_146])).

tff(c_24,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:38:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.17  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.89/1.17  
% 1.89/1.17  %Foreground sorts:
% 1.89/1.17  
% 1.89/1.17  
% 1.89/1.17  %Background operators:
% 1.89/1.17  
% 1.89/1.17  
% 1.89/1.17  %Foreground operators:
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.89/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.89/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.89/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.17  
% 1.89/1.18  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.89/1.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.89/1.18  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.89/1.18  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 1.89/1.18  tff(f_36, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.89/1.18  tff(f_45, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.89/1.18  tff(f_63, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.89/1.18  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.89/1.18  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.89/1.18  tff(c_26, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.18  tff(c_30, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_26])).
% 1.89/1.18  tff(c_128, plain, (![A_45, B_46, C_47]: (r2_hidden(k4_tarski('#skF_2'(A_45, B_46, C_47), A_45), C_47) | ~r2_hidden(A_45, k9_relat_1(C_47, B_46)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.89/1.18  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.89/1.18  tff(c_41, plain, (![A_24, C_25, B_26]: (~r2_hidden(A_24, C_25) | ~r1_xboole_0(k2_tarski(A_24, B_26), C_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.18  tff(c_46, plain, (![A_24]: (~r2_hidden(A_24, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_41])).
% 1.89/1.18  tff(c_140, plain, (![A_45, B_46]: (~r2_hidden(A_45, k9_relat_1(k1_xboole_0, B_46)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_128, c_46])).
% 1.89/1.18  tff(c_146, plain, (![A_48, B_49]: (~r2_hidden(A_48, k9_relat_1(k1_xboole_0, B_49)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_140])).
% 1.89/1.18  tff(c_169, plain, (![B_49]: (k9_relat_1(k1_xboole_0, B_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_146])).
% 1.89/1.18  tff(c_24, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.89/1.18  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_24])).
% 1.89/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.18  
% 1.89/1.18  Inference rules
% 1.89/1.18  ----------------------
% 1.89/1.18  #Ref     : 0
% 1.89/1.18  #Sup     : 33
% 1.89/1.18  #Fact    : 0
% 1.89/1.18  #Define  : 0
% 1.89/1.18  #Split   : 0
% 1.89/1.18  #Chain   : 0
% 1.89/1.18  #Close   : 0
% 1.89/1.18  
% 1.89/1.18  Ordering : KBO
% 1.89/1.18  
% 1.89/1.18  Simplification rules
% 1.89/1.18  ----------------------
% 1.89/1.18  #Subsume      : 7
% 1.89/1.18  #Demod        : 8
% 1.89/1.18  #Tautology    : 10
% 1.89/1.18  #SimpNegUnit  : 0
% 1.89/1.18  #BackRed      : 2
% 1.89/1.18  
% 1.89/1.18  #Partial instantiations: 0
% 1.89/1.18  #Strategies tried      : 1
% 1.89/1.18  
% 1.89/1.18  Timing (in seconds)
% 1.89/1.18  ----------------------
% 1.89/1.18  Preprocessing        : 0.27
% 1.89/1.18  Parsing              : 0.14
% 1.89/1.18  CNF conversion       : 0.02
% 1.89/1.18  Main loop            : 0.15
% 1.89/1.18  Inferencing          : 0.06
% 1.89/1.18  Reduction            : 0.04
% 1.89/1.18  Demodulation         : 0.03
% 1.89/1.18  BG Simplification    : 0.01
% 1.89/1.18  Subsumption          : 0.03
% 1.89/1.18  Abstraction          : 0.01
% 1.89/1.18  MUC search           : 0.00
% 1.89/1.18  Cooper               : 0.00
% 1.89/1.18  Total                : 0.45
% 1.89/1.18  Index Insertion      : 0.00
% 1.89/1.18  Index Deletion       : 0.00
% 1.89/1.18  Index Matching       : 0.00
% 1.89/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
