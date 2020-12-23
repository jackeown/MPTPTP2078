%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:33 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   34 (  43 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  52 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k6_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_55,negated_conjecture,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(c_28,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_5'(A_13),A_13)
      | v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(k1_tarski(A_37),B_38) = B_38
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),B_4) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [B_42,A_43] :
      ( k1_xboole_0 != B_42
      | ~ r2_hidden(A_43,B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_51,plain,(
    ! [A_13] :
      ( k1_xboole_0 != A_13
      | v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_28,c_47])).

tff(c_103,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59,B_60),A_59)
      | r2_hidden(k4_tarski('#skF_3'(A_59,B_60),'#skF_4'(A_59,B_60)),B_60)
      | k6_relat_1(A_59) = B_60
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_39,plain,(
    ! [B_38,A_37] :
      ( k1_xboole_0 != B_38
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_127,plain,(
    ! [B_63,A_64] :
      ( k1_xboole_0 != B_63
      | r2_hidden('#skF_1'(A_64,B_63),A_64)
      | k6_relat_1(A_64) = B_63
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_103,c_39])).

tff(c_136,plain,(
    ! [A_65,B_66] :
      ( k1_xboole_0 != A_65
      | k1_xboole_0 != B_66
      | k6_relat_1(A_65) = B_66
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_127,c_39])).

tff(c_161,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_136])).

tff(c_30,plain,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:14:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.20  
% 1.80/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.20  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k6_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_4
% 1.80/1.20  
% 1.80/1.20  %Foreground sorts:
% 1.80/1.20  
% 1.80/1.20  
% 1.80/1.20  %Background operators:
% 1.80/1.20  
% 1.80/1.20  
% 1.80/1.20  %Foreground operators:
% 1.80/1.20  tff('#skF_5', type, '#skF_5': $i > $i).
% 1.80/1.20  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.80/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.80/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.80/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.80/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.80/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.80/1.20  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.80/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.80/1.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.80/1.20  
% 1.80/1.21  tff(f_53, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.80/1.21  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 1.80/1.21  tff(f_32, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.80/1.21  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_relat_1)).
% 1.80/1.21  tff(f_55, negated_conjecture, ~(k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.80/1.21  tff(c_28, plain, (![A_13]: (r2_hidden('#skF_5'(A_13), A_13) | v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.80/1.21  tff(c_34, plain, (![A_37, B_38]: (k2_xboole_0(k1_tarski(A_37), B_38)=B_38 | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.21  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.80/1.21  tff(c_47, plain, (![B_42, A_43]: (k1_xboole_0!=B_42 | ~r2_hidden(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4])).
% 1.80/1.21  tff(c_51, plain, (![A_13]: (k1_xboole_0!=A_13 | v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_28, c_47])).
% 1.80/1.21  tff(c_103, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59, B_60), A_59) | r2_hidden(k4_tarski('#skF_3'(A_59, B_60), '#skF_4'(A_59, B_60)), B_60) | k6_relat_1(A_59)=B_60 | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.80/1.21  tff(c_39, plain, (![B_38, A_37]: (k1_xboole_0!=B_38 | ~r2_hidden(A_37, B_38))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4])).
% 1.80/1.21  tff(c_127, plain, (![B_63, A_64]: (k1_xboole_0!=B_63 | r2_hidden('#skF_1'(A_64, B_63), A_64) | k6_relat_1(A_64)=B_63 | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_103, c_39])).
% 1.80/1.21  tff(c_136, plain, (![A_65, B_66]: (k1_xboole_0!=A_65 | k1_xboole_0!=B_66 | k6_relat_1(A_65)=B_66 | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_127, c_39])).
% 1.80/1.21  tff(c_161, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_136])).
% 1.80/1.21  tff(c_30, plain, (k6_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.80/1.21  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_30])).
% 1.80/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.21  
% 1.80/1.21  Inference rules
% 1.80/1.21  ----------------------
% 1.80/1.21  #Ref     : 1
% 1.80/1.21  #Sup     : 28
% 1.80/1.21  #Fact    : 0
% 1.80/1.21  #Define  : 0
% 1.80/1.21  #Split   : 0
% 1.80/1.21  #Chain   : 0
% 1.80/1.21  #Close   : 0
% 1.80/1.21  
% 1.80/1.21  Ordering : KBO
% 1.80/1.21  
% 1.80/1.21  Simplification rules
% 1.80/1.21  ----------------------
% 1.80/1.21  #Subsume      : 2
% 1.80/1.21  #Demod        : 1
% 1.80/1.21  #Tautology    : 7
% 1.80/1.21  #SimpNegUnit  : 0
% 1.80/1.21  #BackRed      : 1
% 1.80/1.21  
% 1.80/1.21  #Partial instantiations: 0
% 1.80/1.21  #Strategies tried      : 1
% 1.80/1.21  
% 1.80/1.21  Timing (in seconds)
% 1.80/1.21  ----------------------
% 1.80/1.21  Preprocessing        : 0.28
% 1.80/1.21  Parsing              : 0.14
% 1.80/1.21  CNF conversion       : 0.02
% 1.80/1.21  Main loop            : 0.15
% 1.80/1.21  Inferencing          : 0.06
% 1.80/1.21  Reduction            : 0.03
% 1.80/1.21  Demodulation         : 0.02
% 1.80/1.21  BG Simplification    : 0.01
% 1.80/1.21  Subsumption          : 0.03
% 1.80/1.21  Abstraction          : 0.01
% 1.80/1.21  MUC search           : 0.00
% 1.80/1.21  Cooper               : 0.00
% 1.80/1.21  Total                : 0.46
% 1.80/1.21  Index Insertion      : 0.00
% 1.80/1.21  Index Deletion       : 0.00
% 1.80/1.21  Index Matching       : 0.00
% 1.80/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
