%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:34 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :   38 (  57 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 123 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_32,plain,(
    k1_wellord1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_340,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden(k4_tarski('#skF_2'(A_96,B_97,C_98),B_97),A_96)
      | r2_hidden('#skF_3'(A_96,B_97,C_98),C_98)
      | k1_wellord1(A_96,B_97) = C_98
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [B_8,C_9,A_7] :
      ( r2_hidden(B_8,k3_relat_1(C_9))
      | ~ r2_hidden(k4_tarski(A_7,B_8),C_9)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_394,plain,(
    ! [B_104,A_105,C_106] :
      ( r2_hidden(B_104,k3_relat_1(A_105))
      | r2_hidden('#skF_3'(A_105,B_104,C_106),C_106)
      | k1_wellord1(A_105,B_104) = C_106
      | ~ v1_relat_1(A_105) ) ),
    inference(resolution,[status(thm)],[c_340,c_10])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1623,plain,(
    ! [A_185,B_186,C_187,B_188] :
      ( r2_hidden('#skF_3'(A_185,B_186,C_187),B_188)
      | ~ r1_tarski(C_187,B_188)
      | r2_hidden(B_186,k3_relat_1(A_185))
      | k1_wellord1(A_185,B_186) = C_187
      | ~ v1_relat_1(A_185) ) ),
    inference(resolution,[status(thm)],[c_394,c_2])).

tff(c_18,plain,(
    ! [D_21,A_10] :
      ( ~ r2_hidden(D_21,k1_wellord1(A_10,D_21))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2161,plain,(
    ! [A_240,C_241,A_242,B_243] :
      ( ~ v1_relat_1(A_240)
      | ~ r1_tarski(C_241,k1_wellord1(A_240,'#skF_3'(A_242,B_243,C_241)))
      | r2_hidden(B_243,k3_relat_1(A_242))
      | k1_wellord1(A_242,B_243) = C_241
      | ~ v1_relat_1(A_242) ) ),
    inference(resolution,[status(thm)],[c_1623,c_18])).

tff(c_2219,plain,(
    ! [A_240,B_243,A_242] :
      ( ~ v1_relat_1(A_240)
      | r2_hidden(B_243,k3_relat_1(A_242))
      | k1_wellord1(A_242,B_243) = k1_xboole_0
      | ~ v1_relat_1(A_242) ) ),
    inference(resolution,[status(thm)],[c_8,c_2161])).

tff(c_2351,plain,(
    ! [A_240] : ~ v1_relat_1(A_240) ),
    inference(splitLeft,[status(thm)],[c_2219])).

tff(c_2353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2351,c_36])).

tff(c_2355,plain,(
    ! [B_247,A_248] :
      ( r2_hidden(B_247,k3_relat_1(A_248))
      | k1_wellord1(A_248,B_247) = k1_xboole_0
      | ~ v1_relat_1(A_248) ) ),
    inference(splitRight,[status(thm)],[c_2219])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_4',k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2387,plain,
    ( k1_wellord1('#skF_5','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2355,c_34])).

tff(c_2398,plain,(
    k1_wellord1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2387])).

tff(c_2400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:36:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.84  
% 4.90/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.84  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.90/1.84  
% 4.90/1.84  %Foreground sorts:
% 4.90/1.84  
% 4.90/1.84  
% 4.90/1.84  %Background operators:
% 4.90/1.84  
% 4.90/1.84  
% 4.90/1.84  %Foreground operators:
% 4.90/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.90/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.90/1.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.90/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.90/1.84  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.90/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.90/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.90/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.90/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.90/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.90/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.90/1.84  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 4.90/1.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.90/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.90/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.90/1.84  
% 4.90/1.85  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k3_relat_1(B)) | (k1_wellord1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord1)).
% 4.90/1.85  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.90/1.85  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 4.90/1.85  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 4.90/1.85  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.90/1.85  tff(c_32, plain, (k1_wellord1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.90/1.85  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.90/1.85  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.90/1.85  tff(c_340, plain, (![A_96, B_97, C_98]: (r2_hidden(k4_tarski('#skF_2'(A_96, B_97, C_98), B_97), A_96) | r2_hidden('#skF_3'(A_96, B_97, C_98), C_98) | k1_wellord1(A_96, B_97)=C_98 | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.90/1.85  tff(c_10, plain, (![B_8, C_9, A_7]: (r2_hidden(B_8, k3_relat_1(C_9)) | ~r2_hidden(k4_tarski(A_7, B_8), C_9) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.90/1.85  tff(c_394, plain, (![B_104, A_105, C_106]: (r2_hidden(B_104, k3_relat_1(A_105)) | r2_hidden('#skF_3'(A_105, B_104, C_106), C_106) | k1_wellord1(A_105, B_104)=C_106 | ~v1_relat_1(A_105))), inference(resolution, [status(thm)], [c_340, c_10])).
% 4.90/1.85  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.90/1.85  tff(c_1623, plain, (![A_185, B_186, C_187, B_188]: (r2_hidden('#skF_3'(A_185, B_186, C_187), B_188) | ~r1_tarski(C_187, B_188) | r2_hidden(B_186, k3_relat_1(A_185)) | k1_wellord1(A_185, B_186)=C_187 | ~v1_relat_1(A_185))), inference(resolution, [status(thm)], [c_394, c_2])).
% 4.90/1.85  tff(c_18, plain, (![D_21, A_10]: (~r2_hidden(D_21, k1_wellord1(A_10, D_21)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.90/1.85  tff(c_2161, plain, (![A_240, C_241, A_242, B_243]: (~v1_relat_1(A_240) | ~r1_tarski(C_241, k1_wellord1(A_240, '#skF_3'(A_242, B_243, C_241))) | r2_hidden(B_243, k3_relat_1(A_242)) | k1_wellord1(A_242, B_243)=C_241 | ~v1_relat_1(A_242))), inference(resolution, [status(thm)], [c_1623, c_18])).
% 4.90/1.85  tff(c_2219, plain, (![A_240, B_243, A_242]: (~v1_relat_1(A_240) | r2_hidden(B_243, k3_relat_1(A_242)) | k1_wellord1(A_242, B_243)=k1_xboole_0 | ~v1_relat_1(A_242))), inference(resolution, [status(thm)], [c_8, c_2161])).
% 4.90/1.85  tff(c_2351, plain, (![A_240]: (~v1_relat_1(A_240))), inference(splitLeft, [status(thm)], [c_2219])).
% 4.90/1.85  tff(c_2353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2351, c_36])).
% 4.90/1.85  tff(c_2355, plain, (![B_247, A_248]: (r2_hidden(B_247, k3_relat_1(A_248)) | k1_wellord1(A_248, B_247)=k1_xboole_0 | ~v1_relat_1(A_248))), inference(splitRight, [status(thm)], [c_2219])).
% 4.90/1.85  tff(c_34, plain, (~r2_hidden('#skF_4', k3_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.90/1.85  tff(c_2387, plain, (k1_wellord1('#skF_5', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2355, c_34])).
% 4.90/1.85  tff(c_2398, plain, (k1_wellord1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2387])).
% 4.90/1.85  tff(c_2400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_2398])).
% 4.90/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.85  
% 4.90/1.85  Inference rules
% 4.90/1.85  ----------------------
% 4.90/1.85  #Ref     : 0
% 4.90/1.85  #Sup     : 573
% 4.90/1.85  #Fact    : 2
% 4.90/1.85  #Define  : 0
% 4.90/1.85  #Split   : 3
% 4.90/1.85  #Chain   : 0
% 4.90/1.85  #Close   : 0
% 4.90/1.85  
% 4.90/1.85  Ordering : KBO
% 4.90/1.85  
% 4.90/1.85  Simplification rules
% 4.90/1.85  ----------------------
% 4.90/1.85  #Subsume      : 269
% 4.90/1.85  #Demod        : 53
% 4.90/1.85  #Tautology    : 69
% 4.90/1.85  #SimpNegUnit  : 2
% 4.90/1.85  #BackRed      : 1
% 4.90/1.85  
% 4.90/1.85  #Partial instantiations: 0
% 4.90/1.85  #Strategies tried      : 1
% 4.90/1.85  
% 4.90/1.85  Timing (in seconds)
% 4.90/1.85  ----------------------
% 4.90/1.85  Preprocessing        : 0.29
% 4.90/1.85  Parsing              : 0.16
% 4.90/1.85  CNF conversion       : 0.02
% 4.90/1.85  Main loop            : 0.85
% 4.90/1.85  Inferencing          : 0.29
% 4.90/1.85  Reduction            : 0.18
% 4.90/1.85  Demodulation         : 0.11
% 4.90/1.85  BG Simplification    : 0.04
% 4.90/1.85  Subsumption          : 0.30
% 4.90/1.85  Abstraction          : 0.04
% 4.90/1.85  MUC search           : 0.00
% 4.90/1.85  Cooper               : 0.00
% 4.90/1.85  Total                : 1.16
% 4.90/1.85  Index Insertion      : 0.00
% 4.90/1.85  Index Deletion       : 0.00
% 4.90/1.85  Index Matching       : 0.00
% 4.90/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
