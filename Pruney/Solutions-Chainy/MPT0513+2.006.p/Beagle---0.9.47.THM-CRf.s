%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:59 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  42 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_23,plain,(
    ! [A_14] :
      ( v1_relat_1(A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_23])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( v1_xboole_0(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_2'(A_25,B_26),A_25)
      | r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_28,B_29] :
      ( ~ v1_xboole_0(A_28)
      | r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_42,c_2])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_65,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_59,c_14])).

tff(c_82,plain,(
    ! [A_34,B_35] :
      ( k7_relat_1(A_34,B_35) = k1_xboole_0
      | ~ v1_relat_1(A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_86,plain,(
    ! [B_35] :
      ( k7_relat_1(k1_xboole_0,B_35) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_82])).

tff(c_90,plain,(
    ! [B_35] : k7_relat_1(k1_xboole_0,B_35) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_86])).

tff(c_22,plain,(
    k7_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:58:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.14  
% 1.80/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.14  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.80/1.14  
% 1.80/1.14  %Foreground sorts:
% 1.80/1.14  
% 1.80/1.14  
% 1.80/1.14  %Background operators:
% 1.80/1.14  
% 1.80/1.14  
% 1.80/1.14  %Foreground operators:
% 1.80/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.80/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.80/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.80/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.80/1.14  
% 1.80/1.15  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.80/1.15  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.80/1.15  tff(f_55, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(A)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc17_relat_1)).
% 1.80/1.15  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.80/1.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.80/1.15  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.80/1.15  tff(f_58, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.80/1.15  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.15  tff(c_23, plain, (![A_14]: (v1_relat_1(A_14) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.80/1.15  tff(c_27, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_23])).
% 1.80/1.15  tff(c_20, plain, (![A_12, B_13]: (v1_xboole_0(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.80/1.15  tff(c_42, plain, (![A_25, B_26]: (r2_hidden('#skF_2'(A_25, B_26), A_25) | r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.80/1.15  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.15  tff(c_59, plain, (![A_28, B_29]: (~v1_xboole_0(A_28) | r1_tarski(A_28, B_29))), inference(resolution, [status(thm)], [c_42, c_2])).
% 1.80/1.15  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.80/1.15  tff(c_65, plain, (![A_30]: (k1_xboole_0=A_30 | ~v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_59, c_14])).
% 1.80/1.15  tff(c_82, plain, (![A_34, B_35]: (k7_relat_1(A_34, B_35)=k1_xboole_0 | ~v1_relat_1(A_34) | ~v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_20, c_65])).
% 1.80/1.15  tff(c_86, plain, (![B_35]: (k7_relat_1(k1_xboole_0, B_35)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_82])).
% 1.80/1.15  tff(c_90, plain, (![B_35]: (k7_relat_1(k1_xboole_0, B_35)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_27, c_86])).
% 1.80/1.15  tff(c_22, plain, (k7_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.80/1.15  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_22])).
% 1.80/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.15  
% 1.80/1.15  Inference rules
% 1.80/1.15  ----------------------
% 1.80/1.15  #Ref     : 0
% 1.80/1.15  #Sup     : 13
% 1.80/1.15  #Fact    : 0
% 1.80/1.15  #Define  : 0
% 1.80/1.15  #Split   : 0
% 1.80/1.15  #Chain   : 0
% 1.80/1.15  #Close   : 0
% 1.80/1.15  
% 1.80/1.15  Ordering : KBO
% 1.80/1.15  
% 1.80/1.15  Simplification rules
% 1.80/1.15  ----------------------
% 1.80/1.15  #Subsume      : 1
% 1.80/1.15  #Demod        : 2
% 1.80/1.15  #Tautology    : 3
% 1.80/1.15  #SimpNegUnit  : 0
% 1.80/1.15  #BackRed      : 1
% 1.80/1.15  
% 1.80/1.15  #Partial instantiations: 0
% 1.80/1.15  #Strategies tried      : 1
% 1.80/1.15  
% 1.80/1.15  Timing (in seconds)
% 1.80/1.15  ----------------------
% 1.80/1.15  Preprocessing        : 0.26
% 1.80/1.15  Parsing              : 0.15
% 1.80/1.15  CNF conversion       : 0.02
% 1.80/1.15  Main loop            : 0.12
% 1.80/1.15  Inferencing          : 0.06
% 1.80/1.15  Reduction            : 0.03
% 1.80/1.15  Demodulation         : 0.02
% 1.80/1.15  BG Simplification    : 0.01
% 1.80/1.15  Subsumption          : 0.02
% 1.80/1.15  Abstraction          : 0.00
% 1.80/1.15  MUC search           : 0.00
% 1.80/1.15  Cooper               : 0.00
% 1.80/1.15  Total                : 0.40
% 1.80/1.15  Index Insertion      : 0.00
% 1.80/1.15  Index Deletion       : 0.00
% 1.80/1.15  Index Matching       : 0.00
% 1.80/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
