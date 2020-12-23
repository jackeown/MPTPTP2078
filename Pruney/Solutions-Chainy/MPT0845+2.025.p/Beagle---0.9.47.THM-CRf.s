%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:47 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   43 (  46 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  68 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_60,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_230,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_3'(A_87,B_88),A_87)
      | r2_hidden('#skF_4'(A_87,B_88),B_88)
      | k3_tarski(A_87) = B_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [A_53,C_54,B_55] :
      ( ~ r2_hidden(A_53,C_54)
      | ~ r1_xboole_0(k2_tarski(A_53,B_55),C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_81,plain,(
    ! [A_53] : ~ r2_hidden(A_53,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_249,plain,(
    ! [B_88] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_88),B_88)
      | k3_tarski(k1_xboole_0) = B_88 ) ),
    inference(resolution,[status(thm)],[c_230,c_81])).

tff(c_279,plain,(
    ! [B_88] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_88),B_88)
      | k1_xboole_0 = B_88 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_249])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_129,plain,(
    ! [D_70,A_71,B_72] :
      ( ~ r2_hidden(D_70,'#skF_6'(A_71,B_72))
      | ~ r2_hidden(D_70,B_72)
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_378,plain,(
    ! [A_99,B_100,B_101] :
      ( ~ r2_hidden('#skF_1'('#skF_6'(A_99,B_100),B_101),B_100)
      | ~ r2_hidden(A_99,B_100)
      | r1_xboole_0('#skF_6'(A_99,B_100),B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_389,plain,(
    ! [A_102,B_103] :
      ( ~ r2_hidden(A_102,B_103)
      | r1_xboole_0('#skF_6'(A_102,B_103),B_103) ) ),
    inference(resolution,[status(thm)],[c_4,c_378])).

tff(c_64,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_6'(A_49,B_50),B_50)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    ! [B_42] :
      ( ~ r1_xboole_0(B_42,'#skF_7')
      | ~ r2_hidden(B_42,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_69,plain,(
    ! [A_49] :
      ( ~ r1_xboole_0('#skF_6'(A_49,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_49,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_40])).

tff(c_398,plain,(
    ! [A_104] : ~ r2_hidden(A_104,'#skF_7') ),
    inference(resolution,[status(thm)],[c_389,c_69])).

tff(c_406,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_279,c_398])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.42  
% 2.39/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.43  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.39/1.43  
% 2.39/1.43  %Foreground sorts:
% 2.39/1.43  
% 2.39/1.43  
% 2.39/1.43  %Background operators:
% 2.39/1.43  
% 2.39/1.43  
% 2.39/1.43  %Foreground operators:
% 2.39/1.43  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.39/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.39/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.39/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.39/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.43  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.39/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.39/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.39/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.39/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.39/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.39/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.39/1.43  
% 2.39/1.44  tff(f_89, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.39/1.44  tff(f_60, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.39/1.44  tff(f_59, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.39/1.44  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.39/1.44  tff(f_65, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.39/1.44  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.39/1.44  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.39/1.44  tff(c_42, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.39/1.44  tff(c_32, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.39/1.44  tff(c_230, plain, (![A_87, B_88]: (r2_hidden('#skF_3'(A_87, B_88), A_87) | r2_hidden('#skF_4'(A_87, B_88), B_88) | k3_tarski(A_87)=B_88)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.39/1.44  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.44  tff(c_76, plain, (![A_53, C_54, B_55]: (~r2_hidden(A_53, C_54) | ~r1_xboole_0(k2_tarski(A_53, B_55), C_54))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.39/1.44  tff(c_81, plain, (![A_53]: (~r2_hidden(A_53, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_76])).
% 2.39/1.44  tff(c_249, plain, (![B_88]: (r2_hidden('#skF_4'(k1_xboole_0, B_88), B_88) | k3_tarski(k1_xboole_0)=B_88)), inference(resolution, [status(thm)], [c_230, c_81])).
% 2.39/1.44  tff(c_279, plain, (![B_88]: (r2_hidden('#skF_4'(k1_xboole_0, B_88), B_88) | k1_xboole_0=B_88)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_249])).
% 2.39/1.44  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.39/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.39/1.44  tff(c_129, plain, (![D_70, A_71, B_72]: (~r2_hidden(D_70, '#skF_6'(A_71, B_72)) | ~r2_hidden(D_70, B_72) | ~r2_hidden(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.39/1.44  tff(c_378, plain, (![A_99, B_100, B_101]: (~r2_hidden('#skF_1'('#skF_6'(A_99, B_100), B_101), B_100) | ~r2_hidden(A_99, B_100) | r1_xboole_0('#skF_6'(A_99, B_100), B_101))), inference(resolution, [status(thm)], [c_6, c_129])).
% 2.39/1.44  tff(c_389, plain, (![A_102, B_103]: (~r2_hidden(A_102, B_103) | r1_xboole_0('#skF_6'(A_102, B_103), B_103))), inference(resolution, [status(thm)], [c_4, c_378])).
% 2.39/1.44  tff(c_64, plain, (![A_49, B_50]: (r2_hidden('#skF_6'(A_49, B_50), B_50) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.39/1.44  tff(c_40, plain, (![B_42]: (~r1_xboole_0(B_42, '#skF_7') | ~r2_hidden(B_42, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.39/1.44  tff(c_69, plain, (![A_49]: (~r1_xboole_0('#skF_6'(A_49, '#skF_7'), '#skF_7') | ~r2_hidden(A_49, '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_40])).
% 2.39/1.44  tff(c_398, plain, (![A_104]: (~r2_hidden(A_104, '#skF_7'))), inference(resolution, [status(thm)], [c_389, c_69])).
% 2.39/1.44  tff(c_406, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_279, c_398])).
% 2.39/1.44  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_406])).
% 2.39/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.44  
% 2.39/1.44  Inference rules
% 2.39/1.44  ----------------------
% 2.39/1.44  #Ref     : 0
% 2.39/1.44  #Sup     : 82
% 2.39/1.44  #Fact    : 0
% 2.39/1.44  #Define  : 0
% 2.39/1.44  #Split   : 2
% 2.39/1.44  #Chain   : 0
% 2.39/1.44  #Close   : 0
% 2.39/1.44  
% 2.39/1.44  Ordering : KBO
% 2.39/1.44  
% 2.39/1.44  Simplification rules
% 2.39/1.44  ----------------------
% 2.39/1.44  #Subsume      : 10
% 2.39/1.44  #Demod        : 5
% 2.39/1.44  #Tautology    : 9
% 2.39/1.44  #SimpNegUnit  : 4
% 2.39/1.44  #BackRed      : 0
% 2.39/1.44  
% 2.39/1.44  #Partial instantiations: 0
% 2.39/1.44  #Strategies tried      : 1
% 2.39/1.44  
% 2.39/1.44  Timing (in seconds)
% 2.39/1.44  ----------------------
% 2.39/1.44  Preprocessing        : 0.36
% 2.39/1.44  Parsing              : 0.18
% 2.39/1.44  CNF conversion       : 0.03
% 2.39/1.44  Main loop            : 0.25
% 2.39/1.44  Inferencing          : 0.09
% 2.39/1.44  Reduction            : 0.07
% 2.39/1.44  Demodulation         : 0.04
% 2.39/1.44  BG Simplification    : 0.02
% 2.39/1.44  Subsumption          : 0.06
% 2.39/1.44  Abstraction          : 0.01
% 2.39/1.44  MUC search           : 0.00
% 2.39/1.44  Cooper               : 0.00
% 2.60/1.44  Total                : 0.64
% 2.60/1.44  Index Insertion      : 0.00
% 2.60/1.44  Index Deletion       : 0.00
% 2.60/1.44  Index Matching       : 0.00
% 2.60/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
