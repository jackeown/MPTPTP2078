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
% DateTime   : Thu Dec  3 10:01:31 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   43 (  50 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  55 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_310,plain,(
    ! [A_79,B_80,C_81] :
      ( r2_hidden('#skF_1'(A_79,B_80,C_81),A_79)
      | r2_hidden('#skF_2'(A_79,B_80,C_81),C_81)
      | k4_xboole_0(A_79,B_80) = C_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    ! [B_34,A_35] :
      ( ~ r2_hidden(B_34,A_35)
      | k4_xboole_0(A_35,k1_tarski(B_34)) != A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_147,plain,(
    ! [B_34] : ~ r2_hidden(B_34,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_138])).

tff(c_353,plain,(
    ! [B_80,C_81] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_80,C_81),C_81)
      | k4_xboole_0(k1_xboole_0,B_80) = C_81 ) ),
    inference(resolution,[status(thm)],[c_310,c_147])).

tff(c_427,plain,(
    ! [B_82,C_83] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_82,C_83),C_83)
      | k1_xboole_0 = C_83 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_353])).

tff(c_58,plain,(
    ! [B_23] : k2_zfmisc_1(k1_xboole_0,B_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_34])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_193,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_3'(A_49,B_50,C_51),k2_relat_1(C_51))
      | ~ r2_hidden(A_49,k10_relat_1(C_51,B_50))
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_196,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_3'(A_49,B_50,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_49,k10_relat_1(k1_xboole_0,B_50))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_193])).

tff(c_198,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_3'(A_49,B_50,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_49,k10_relat_1(k1_xboole_0,B_50)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_196])).

tff(c_199,plain,(
    ! [A_49,B_50] : ~ r2_hidden(A_49,k10_relat_1(k1_xboole_0,B_50)) ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_198])).

tff(c_482,plain,(
    ! [B_50] : k10_relat_1(k1_xboole_0,B_50) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_427,c_199])).

tff(c_48,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:03:51 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.38  
% 2.13/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.38  %$ r2_hidden > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 2.13/1.38  
% 2.13/1.38  %Foreground sorts:
% 2.13/1.38  
% 2.13/1.38  
% 2.13/1.38  %Background operators:
% 2.13/1.38  
% 2.13/1.38  
% 2.13/1.38  %Foreground operators:
% 2.13/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.13/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.13/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.13/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.38  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.13/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.13/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.38  
% 2.42/1.39  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.42/1.39  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.42/1.39  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.42/1.39  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.42/1.39  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.42/1.39  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.42/1.39  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.42/1.39  tff(f_69, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.42/1.39  tff(c_20, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.39  tff(c_310, plain, (![A_79, B_80, C_81]: (r2_hidden('#skF_1'(A_79, B_80, C_81), A_79) | r2_hidden('#skF_2'(A_79, B_80, C_81), C_81) | k4_xboole_0(A_79, B_80)=C_81)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.42/1.39  tff(c_138, plain, (![B_34, A_35]: (~r2_hidden(B_34, A_35) | k4_xboole_0(A_35, k1_tarski(B_34))!=A_35)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.42/1.39  tff(c_147, plain, (![B_34]: (~r2_hidden(B_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_138])).
% 2.42/1.39  tff(c_353, plain, (![B_80, C_81]: (r2_hidden('#skF_2'(k1_xboole_0, B_80, C_81), C_81) | k4_xboole_0(k1_xboole_0, B_80)=C_81)), inference(resolution, [status(thm)], [c_310, c_147])).
% 2.42/1.39  tff(c_427, plain, (![B_82, C_83]: (r2_hidden('#skF_2'(k1_xboole_0, B_82, C_83), C_83) | k1_xboole_0=C_83)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_353])).
% 2.42/1.39  tff(c_58, plain, (![B_23]: (k2_zfmisc_1(k1_xboole_0, B_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.42/1.39  tff(c_34, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.42/1.39  tff(c_62, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_34])).
% 2.42/1.39  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.42/1.39  tff(c_193, plain, (![A_49, B_50, C_51]: (r2_hidden('#skF_3'(A_49, B_50, C_51), k2_relat_1(C_51)) | ~r2_hidden(A_49, k10_relat_1(C_51, B_50)) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.42/1.39  tff(c_196, plain, (![A_49, B_50]: (r2_hidden('#skF_3'(A_49, B_50, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_49, k10_relat_1(k1_xboole_0, B_50)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_193])).
% 2.42/1.39  tff(c_198, plain, (![A_49, B_50]: (r2_hidden('#skF_3'(A_49, B_50, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_49, k10_relat_1(k1_xboole_0, B_50)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_196])).
% 2.42/1.39  tff(c_199, plain, (![A_49, B_50]: (~r2_hidden(A_49, k10_relat_1(k1_xboole_0, B_50)))), inference(negUnitSimplification, [status(thm)], [c_147, c_198])).
% 2.42/1.39  tff(c_482, plain, (![B_50]: (k10_relat_1(k1_xboole_0, B_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_427, c_199])).
% 2.42/1.39  tff(c_48, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.42/1.39  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_482, c_48])).
% 2.42/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.39  
% 2.42/1.39  Inference rules
% 2.42/1.39  ----------------------
% 2.42/1.39  #Ref     : 0
% 2.42/1.39  #Sup     : 92
% 2.42/1.39  #Fact    : 0
% 2.42/1.39  #Define  : 0
% 2.42/1.39  #Split   : 0
% 2.42/1.39  #Chain   : 0
% 2.42/1.39  #Close   : 0
% 2.42/1.39  
% 2.42/1.39  Ordering : KBO
% 2.42/1.39  
% 2.42/1.39  Simplification rules
% 2.42/1.39  ----------------------
% 2.42/1.39  #Subsume      : 8
% 2.42/1.39  #Demod        : 16
% 2.42/1.39  #Tautology    : 28
% 2.42/1.39  #SimpNegUnit  : 2
% 2.42/1.39  #BackRed      : 6
% 2.42/1.39  
% 2.42/1.39  #Partial instantiations: 0
% 2.42/1.39  #Strategies tried      : 1
% 2.42/1.39  
% 2.42/1.39  Timing (in seconds)
% 2.42/1.39  ----------------------
% 2.42/1.39  Preprocessing        : 0.37
% 2.42/1.39  Parsing              : 0.18
% 2.42/1.39  CNF conversion       : 0.03
% 2.42/1.40  Main loop            : 0.24
% 2.42/1.40  Inferencing          : 0.08
% 2.42/1.40  Reduction            : 0.06
% 2.42/1.40  Demodulation         : 0.04
% 2.42/1.40  BG Simplification    : 0.02
% 2.42/1.40  Subsumption          : 0.06
% 2.42/1.40  Abstraction          : 0.02
% 2.42/1.40  MUC search           : 0.00
% 2.42/1.40  Cooper               : 0.00
% 2.42/1.40  Total                : 0.63
% 2.42/1.40  Index Insertion      : 0.00
% 2.42/1.40  Index Deletion       : 0.00
% 2.42/1.40  Index Matching       : 0.00
% 2.42/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
