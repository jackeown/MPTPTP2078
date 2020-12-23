%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:48 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_43,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k5_relat_1(k6_relat_1(A_5),B_6) = k7_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_21,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_10,B_11)),k2_relat_1(B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_6,A_5)),k2_relat_1(B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(k6_relat_1(A_5))
      | ~ v1_relat_1(B_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_21])).

tff(c_27,plain,(
    ! [B_12,A_13] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_12,A_13)),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_8,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2','#skF_1')),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_27,c_8])).

tff(c_34,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 09:49:41 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.08  
% 1.53/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.09  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_1
% 1.58/1.09  
% 1.58/1.09  %Foreground sorts:
% 1.58/1.09  
% 1.58/1.09  
% 1.58/1.09  %Background operators:
% 1.58/1.09  
% 1.58/1.09  
% 1.58/1.09  %Foreground operators:
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.58/1.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.58/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.58/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.58/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.58/1.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.09  
% 1.58/1.09  tff(f_43, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 1.58/1.09  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.58/1.09  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.58/1.09  tff(f_34, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 1.58/1.09  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.58/1.09  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.58/1.09  tff(c_6, plain, (![A_5, B_6]: (k5_relat_1(k6_relat_1(A_5), B_6)=k7_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.58/1.09  tff(c_21, plain, (![A_10, B_11]: (r1_tarski(k2_relat_1(k5_relat_1(A_10, B_11)), k2_relat_1(B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.09  tff(c_24, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(k7_relat_1(B_6, A_5)), k2_relat_1(B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(k6_relat_1(A_5)) | ~v1_relat_1(B_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_21])).
% 1.58/1.09  tff(c_27, plain, (![B_12, A_13]: (r1_tarski(k2_relat_1(k7_relat_1(B_12, A_13)), k2_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 1.58/1.09  tff(c_8, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', '#skF_1')), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.58/1.09  tff(c_30, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_27, c_8])).
% 1.58/1.09  tff(c_34, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_30])).
% 1.58/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.09  
% 1.58/1.09  Inference rules
% 1.58/1.09  ----------------------
% 1.58/1.09  #Ref     : 0
% 1.58/1.09  #Sup     : 4
% 1.58/1.09  #Fact    : 0
% 1.58/1.09  #Define  : 0
% 1.58/1.09  #Split   : 0
% 1.58/1.10  #Chain   : 0
% 1.58/1.10  #Close   : 0
% 1.58/1.10  
% 1.58/1.10  Ordering : KBO
% 1.58/1.10  
% 1.58/1.10  Simplification rules
% 1.58/1.10  ----------------------
% 1.58/1.10  #Subsume      : 0
% 1.58/1.10  #Demod        : 2
% 1.58/1.10  #Tautology    : 2
% 1.58/1.10  #SimpNegUnit  : 0
% 1.58/1.10  #BackRed      : 0
% 1.58/1.10  
% 1.58/1.10  #Partial instantiations: 0
% 1.58/1.10  #Strategies tried      : 1
% 1.58/1.10  
% 1.58/1.10  Timing (in seconds)
% 1.58/1.10  ----------------------
% 1.58/1.10  Preprocessing        : 0.24
% 1.58/1.10  Parsing              : 0.13
% 1.58/1.10  CNF conversion       : 0.01
% 1.58/1.10  Main loop            : 0.07
% 1.58/1.10  Inferencing          : 0.03
% 1.58/1.10  Reduction            : 0.02
% 1.58/1.10  Demodulation         : 0.02
% 1.58/1.10  BG Simplification    : 0.01
% 1.58/1.10  Subsumption          : 0.01
% 1.58/1.10  Abstraction          : 0.00
% 1.58/1.10  MUC search           : 0.00
% 1.58/1.10  Cooper               : 0.00
% 1.58/1.10  Total                : 0.34
% 1.58/1.10  Index Insertion      : 0.00
% 1.58/1.10  Index Deletion       : 0.00
% 1.58/1.10  Index Matching       : 0.00
% 1.58/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
