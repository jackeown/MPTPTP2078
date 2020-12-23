%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:29 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   43 (  47 expanded)
%              Number of leaves         :   30 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  39 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_2'(A_34),A_34)
      | v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden(A_62,B_63)
      | ~ r1_xboole_0(k1_tarski(A_62),B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_55,plain,(
    ! [A_64] : ~ r2_hidden(A_64,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_49])).

tff(c_64,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_55])).

tff(c_308,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden(k4_tarski(A_109,'#skF_5'(A_109,B_110,C_111)),C_111)
      | ~ r2_hidden(A_109,k10_relat_1(C_111,B_110))
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    ! [A_62] : ~ r2_hidden(A_62,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_49])).

tff(c_320,plain,(
    ! [A_109,B_110] :
      ( ~ r2_hidden(A_109,k10_relat_1(k1_xboole_0,B_110))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_308,c_54])).

tff(c_326,plain,(
    ! [A_112,B_113] : ~ r2_hidden(A_112,k10_relat_1(k1_xboole_0,B_113)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_320])).

tff(c_354,plain,(
    ! [B_113] : k10_relat_1(k1_xboole_0,B_113) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_326])).

tff(c_36,plain,(
    k10_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.74  
% 2.64/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.75  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_4
% 2.64/1.75  
% 2.64/1.75  %Foreground sorts:
% 2.64/1.75  
% 2.64/1.75  
% 2.64/1.75  %Background operators:
% 2.64/1.75  
% 2.64/1.75  
% 2.64/1.75  %Foreground operators:
% 2.64/1.75  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.64/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.64/1.75  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.64/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.64/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.75  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.64/1.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.64/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.64/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.64/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.75  tff('#skF_6', type, '#skF_6': $i).
% 2.64/1.75  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.64/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.64/1.75  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.75  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.75  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.64/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.64/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.75  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.75  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.64/1.75  
% 2.64/1.76  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.64/1.76  tff(f_64, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.64/1.76  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.64/1.76  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.64/1.76  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.64/1.76  tff(f_78, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.64/1.76  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.76  tff(c_26, plain, (![A_34]: (r2_hidden('#skF_2'(A_34), A_34) | v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.64/1.76  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.76  tff(c_49, plain, (![A_62, B_63]: (~r2_hidden(A_62, B_63) | ~r1_xboole_0(k1_tarski(A_62), B_63))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.64/1.76  tff(c_55, plain, (![A_64]: (~r2_hidden(A_64, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_49])).
% 2.64/1.76  tff(c_64, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_55])).
% 2.64/1.76  tff(c_308, plain, (![A_109, B_110, C_111]: (r2_hidden(k4_tarski(A_109, '#skF_5'(A_109, B_110, C_111)), C_111) | ~r2_hidden(A_109, k10_relat_1(C_111, B_110)) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.64/1.76  tff(c_54, plain, (![A_62]: (~r2_hidden(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_49])).
% 2.64/1.76  tff(c_320, plain, (![A_109, B_110]: (~r2_hidden(A_109, k10_relat_1(k1_xboole_0, B_110)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_308, c_54])).
% 2.64/1.76  tff(c_326, plain, (![A_112, B_113]: (~r2_hidden(A_112, k10_relat_1(k1_xboole_0, B_113)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_320])).
% 2.64/1.76  tff(c_354, plain, (![B_113]: (k10_relat_1(k1_xboole_0, B_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_326])).
% 2.64/1.76  tff(c_36, plain, (k10_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.64/1.76  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_354, c_36])).
% 2.64/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.76  
% 2.64/1.76  Inference rules
% 2.64/1.76  ----------------------
% 2.64/1.76  #Ref     : 1
% 2.64/1.76  #Sup     : 75
% 2.64/1.76  #Fact    : 0
% 2.64/1.76  #Define  : 0
% 2.64/1.76  #Split   : 0
% 2.64/1.76  #Chain   : 0
% 2.64/1.76  #Close   : 0
% 2.64/1.76  
% 2.64/1.76  Ordering : KBO
% 2.64/1.76  
% 2.64/1.76  Simplification rules
% 2.64/1.76  ----------------------
% 2.64/1.76  #Subsume      : 20
% 2.64/1.76  #Demod        : 26
% 2.64/1.76  #Tautology    : 37
% 2.64/1.76  #SimpNegUnit  : 0
% 2.64/1.76  #BackRed      : 3
% 2.64/1.76  
% 2.64/1.76  #Partial instantiations: 0
% 2.64/1.76  #Strategies tried      : 1
% 2.64/1.76  
% 2.64/1.76  Timing (in seconds)
% 2.64/1.76  ----------------------
% 2.64/1.77  Preprocessing        : 0.49
% 2.64/1.77  Parsing              : 0.25
% 2.64/1.77  CNF conversion       : 0.04
% 2.64/1.77  Main loop            : 0.35
% 2.64/1.77  Inferencing          : 0.15
% 2.64/1.77  Reduction            : 0.09
% 2.64/1.77  Demodulation         : 0.06
% 2.64/1.77  BG Simplification    : 0.03
% 2.64/1.77  Subsumption          : 0.07
% 2.64/1.77  Abstraction          : 0.02
% 2.64/1.77  MUC search           : 0.00
% 2.64/1.77  Cooper               : 0.00
% 2.64/1.77  Total                : 0.88
% 2.64/1.77  Index Insertion      : 0.00
% 2.64/1.77  Index Deletion       : 0.00
% 2.64/1.77  Index Matching       : 0.00
% 2.64/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
