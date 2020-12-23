%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:34 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   37 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  45 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_9 > #skF_11 > #skF_6 > #skF_2 > #skF_1 > #skF_3 > #skF_10 > #skF_8 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_71,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(c_64,plain,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_62,plain,(
    ! [A_98] :
      ( r2_hidden('#skF_9'(A_98),A_98)
      | v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_141,plain,(
    ! [B_131,A_132] :
      ( ~ r2_hidden(B_131,A_132)
      | k4_xboole_0(A_132,k1_tarski(B_131)) != A_132 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_148,plain,(
    ! [B_133] : ~ r2_hidden(B_133,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_141])).

tff(c_159,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_62,c_148])).

tff(c_488,plain,(
    ! [A_207,B_208] :
      ( r2_hidden('#skF_5'(A_207,B_208),A_207)
      | r2_hidden(k4_tarski('#skF_7'(A_207,B_208),'#skF_8'(A_207,B_208)),B_208)
      | k6_relat_1(A_207) = B_208
      | ~ v1_relat_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_146,plain,(
    ! [B_131] : ~ r2_hidden(B_131,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_141])).

tff(c_509,plain,(
    ! [A_207] :
      ( r2_hidden('#skF_5'(A_207,k1_xboole_0),A_207)
      | k6_relat_1(A_207) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_488,c_146])).

tff(c_518,plain,(
    ! [A_209] :
      ( r2_hidden('#skF_5'(A_209,k1_xboole_0),A_209)
      | k6_relat_1(A_209) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_509])).

tff(c_531,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_518,c_146])).

tff(c_538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_531])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:37:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.34  
% 2.45/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.35  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_9 > #skF_11 > #skF_6 > #skF_2 > #skF_1 > #skF_3 > #skF_10 > #skF_8 > #skF_7 > #skF_5 > #skF_4
% 2.45/1.35  
% 2.45/1.35  %Foreground sorts:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Background operators:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Foreground operators:
% 2.45/1.35  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.45/1.35  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 2.45/1.35  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.45/1.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.45/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.45/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.45/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.45/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.45/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.45/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.45/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.45/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.45/1.35  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 2.45/1.35  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.45/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.45/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.45/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.35  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.45/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.45/1.35  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.45/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.45/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.45/1.35  
% 2.45/1.36  tff(f_96, negated_conjecture, ~(k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.45/1.36  tff(f_94, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.45/1.36  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.45/1.36  tff(f_71, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.45/1.36  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 2.45/1.36  tff(c_64, plain, (k6_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.45/1.36  tff(c_62, plain, (![A_98]: (r2_hidden('#skF_9'(A_98), A_98) | v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.45/1.36  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.36  tff(c_141, plain, (![B_131, A_132]: (~r2_hidden(B_131, A_132) | k4_xboole_0(A_132, k1_tarski(B_131))!=A_132)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.45/1.36  tff(c_148, plain, (![B_133]: (~r2_hidden(B_133, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_141])).
% 2.45/1.36  tff(c_159, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_148])).
% 2.45/1.36  tff(c_488, plain, (![A_207, B_208]: (r2_hidden('#skF_5'(A_207, B_208), A_207) | r2_hidden(k4_tarski('#skF_7'(A_207, B_208), '#skF_8'(A_207, B_208)), B_208) | k6_relat_1(A_207)=B_208 | ~v1_relat_1(B_208))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.45/1.36  tff(c_146, plain, (![B_131]: (~r2_hidden(B_131, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_141])).
% 2.45/1.36  tff(c_509, plain, (![A_207]: (r2_hidden('#skF_5'(A_207, k1_xboole_0), A_207) | k6_relat_1(A_207)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_488, c_146])).
% 2.45/1.36  tff(c_518, plain, (![A_209]: (r2_hidden('#skF_5'(A_209, k1_xboole_0), A_209) | k6_relat_1(A_209)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_159, c_509])).
% 2.45/1.36  tff(c_531, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_518, c_146])).
% 2.45/1.36  tff(c_538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_531])).
% 2.45/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.36  
% 2.45/1.36  Inference rules
% 2.45/1.36  ----------------------
% 2.45/1.36  #Ref     : 1
% 2.45/1.36  #Sup     : 104
% 2.45/1.36  #Fact    : 0
% 2.45/1.36  #Define  : 0
% 2.45/1.36  #Split   : 0
% 2.45/1.36  #Chain   : 0
% 2.45/1.36  #Close   : 0
% 2.45/1.36  
% 2.45/1.36  Ordering : KBO
% 2.45/1.36  
% 2.45/1.36  Simplification rules
% 2.45/1.36  ----------------------
% 2.45/1.36  #Subsume      : 8
% 2.45/1.36  #Demod        : 29
% 2.45/1.36  #Tautology    : 55
% 2.45/1.36  #SimpNegUnit  : 9
% 2.45/1.36  #BackRed      : 2
% 2.45/1.36  
% 2.45/1.36  #Partial instantiations: 0
% 2.45/1.36  #Strategies tried      : 1
% 2.45/1.36  
% 2.45/1.36  Timing (in seconds)
% 2.45/1.36  ----------------------
% 2.45/1.36  Preprocessing        : 0.34
% 2.45/1.36  Parsing              : 0.17
% 2.45/1.36  CNF conversion       : 0.03
% 2.45/1.36  Main loop            : 0.25
% 2.45/1.36  Inferencing          : 0.10
% 2.45/1.36  Reduction            : 0.07
% 2.45/1.36  Demodulation         : 0.04
% 2.45/1.36  BG Simplification    : 0.02
% 2.45/1.36  Subsumption          : 0.05
% 2.45/1.36  Abstraction          : 0.02
% 2.45/1.36  MUC search           : 0.00
% 2.45/1.36  Cooper               : 0.00
% 2.45/1.36  Total                : 0.61
% 2.45/1.36  Index Insertion      : 0.00
% 2.45/1.36  Index Deletion       : 0.00
% 2.45/1.36  Index Matching       : 0.00
% 2.45/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
