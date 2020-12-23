%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:34 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   43 (  64 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  75 expanded)
%              Number of equality atoms :   23 (  51 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k2_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(c_56,plain,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_54,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_5'(A_23),A_23)
      | v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_120,plain,(
    ! [A_56,B_57] : k2_enumset1(A_56,A_56,A_56,B_57) = k2_tarski(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_enumset1(A_3,A_3,A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_136,plain,(
    ! [B_58] : k2_tarski(B_58,B_58) = k1_tarski(B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_4])).

tff(c_30,plain,(
    ! [B_13,C_14] : k4_xboole_0(k1_xboole_0,k2_tarski(B_13,C_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_154,plain,(
    ! [B_59] : k4_xboole_0(k1_xboole_0,k1_tarski(B_59)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_30])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( ~ r2_hidden(B_11,A_10)
      | k4_xboole_0(A_10,k1_tarski(B_11)) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_165,plain,(
    ! [B_60] : ~ r2_hidden(B_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_18])).

tff(c_170,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_54,c_165])).

tff(c_385,plain,(
    ! [A_110,B_111] :
      ( r2_hidden('#skF_1'(A_110,B_111),A_110)
      | r2_hidden(k4_tarski('#skF_3'(A_110,B_111),'#skF_4'(A_110,B_111)),B_111)
      | k6_relat_1(A_110) = B_111
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_163,plain,(
    ! [B_59] : ~ r2_hidden(B_59,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_18])).

tff(c_411,plain,(
    ! [A_110] :
      ( r2_hidden('#skF_1'(A_110,k1_xboole_0),A_110)
      | k6_relat_1(A_110) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_385,c_163])).

tff(c_421,plain,(
    ! [A_112] :
      ( r2_hidden('#skF_1'(A_112,k1_xboole_0),A_112)
      | k6_relat_1(A_112) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_411])).

tff(c_431,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_421,c_163])).

tff(c_437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:27:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.33  
% 2.04/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.33  %$ r2_hidden > v1_relat_1 > k2_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_4
% 2.04/1.33  
% 2.04/1.33  %Foreground sorts:
% 2.04/1.33  
% 2.04/1.33  
% 2.04/1.33  %Background operators:
% 2.04/1.33  
% 2.04/1.33  
% 2.04/1.33  %Foreground operators:
% 2.04/1.33  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.04/1.33  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.04/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.04/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.04/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.04/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.04/1.33  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.04/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.04/1.33  
% 2.43/1.34  tff(f_84, negated_conjecture, ~(k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.43/1.34  tff(f_82, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.43/1.34  tff(f_27, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 2.43/1.34  tff(f_29, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 2.43/1.34  tff(f_61, axiom, (![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 2.43/1.34  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.43/1.34  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 2.43/1.34  tff(c_56, plain, (k6_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.43/1.34  tff(c_54, plain, (![A_23]: (r2_hidden('#skF_5'(A_23), A_23) | v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.43/1.34  tff(c_120, plain, (![A_56, B_57]: (k2_enumset1(A_56, A_56, A_56, B_57)=k2_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.43/1.34  tff(c_4, plain, (![A_3]: (k2_enumset1(A_3, A_3, A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.34  tff(c_136, plain, (![B_58]: (k2_tarski(B_58, B_58)=k1_tarski(B_58))), inference(superposition, [status(thm), theory('equality')], [c_120, c_4])).
% 2.43/1.34  tff(c_30, plain, (![B_13, C_14]: (k4_xboole_0(k1_xboole_0, k2_tarski(B_13, C_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.34  tff(c_154, plain, (![B_59]: (k4_xboole_0(k1_xboole_0, k1_tarski(B_59))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_136, c_30])).
% 2.43/1.34  tff(c_18, plain, (![B_11, A_10]: (~r2_hidden(B_11, A_10) | k4_xboole_0(A_10, k1_tarski(B_11))!=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.43/1.34  tff(c_165, plain, (![B_60]: (~r2_hidden(B_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_154, c_18])).
% 2.43/1.34  tff(c_170, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_165])).
% 2.43/1.34  tff(c_385, plain, (![A_110, B_111]: (r2_hidden('#skF_1'(A_110, B_111), A_110) | r2_hidden(k4_tarski('#skF_3'(A_110, B_111), '#skF_4'(A_110, B_111)), B_111) | k6_relat_1(A_110)=B_111 | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.43/1.34  tff(c_163, plain, (![B_59]: (~r2_hidden(B_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_154, c_18])).
% 2.43/1.34  tff(c_411, plain, (![A_110]: (r2_hidden('#skF_1'(A_110, k1_xboole_0), A_110) | k6_relat_1(A_110)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_385, c_163])).
% 2.43/1.34  tff(c_421, plain, (![A_112]: (r2_hidden('#skF_1'(A_112, k1_xboole_0), A_112) | k6_relat_1(A_112)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_170, c_411])).
% 2.43/1.34  tff(c_431, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_421, c_163])).
% 2.43/1.34  tff(c_437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_431])).
% 2.43/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.34  
% 2.43/1.34  Inference rules
% 2.43/1.34  ----------------------
% 2.43/1.34  #Ref     : 1
% 2.43/1.34  #Sup     : 87
% 2.43/1.34  #Fact    : 0
% 2.43/1.34  #Define  : 0
% 2.43/1.34  #Split   : 0
% 2.43/1.34  #Chain   : 0
% 2.43/1.34  #Close   : 0
% 2.43/1.34  
% 2.43/1.34  Ordering : KBO
% 2.43/1.34  
% 2.43/1.34  Simplification rules
% 2.43/1.34  ----------------------
% 2.43/1.34  #Subsume      : 8
% 2.43/1.34  #Demod        : 7
% 2.43/1.34  #Tautology    : 52
% 2.43/1.34  #SimpNegUnit  : 6
% 2.43/1.34  #BackRed      : 0
% 2.43/1.34  
% 2.43/1.34  #Partial instantiations: 0
% 2.43/1.34  #Strategies tried      : 1
% 2.43/1.34  
% 2.43/1.34  Timing (in seconds)
% 2.43/1.34  ----------------------
% 2.43/1.35  Preprocessing        : 0.30
% 2.43/1.35  Parsing              : 0.14
% 2.43/1.35  CNF conversion       : 0.02
% 2.43/1.35  Main loop            : 0.22
% 2.43/1.35  Inferencing          : 0.09
% 2.43/1.35  Reduction            : 0.07
% 2.43/1.35  Demodulation         : 0.05
% 2.43/1.35  BG Simplification    : 0.02
% 2.43/1.35  Subsumption          : 0.04
% 2.43/1.35  Abstraction          : 0.02
% 2.43/1.35  MUC search           : 0.00
% 2.43/1.35  Cooper               : 0.00
% 2.43/1.35  Total                : 0.55
% 2.43/1.35  Index Insertion      : 0.00
% 2.43/1.35  Index Deletion       : 0.00
% 2.43/1.35  Index Matching       : 0.00
% 2.43/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
