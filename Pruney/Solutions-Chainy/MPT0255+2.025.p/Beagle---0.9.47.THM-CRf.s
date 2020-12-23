%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:42 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 199 expanded)
%              Number of leaves         :   26 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :   47 ( 270 expanded)
%              Number of equality atoms :    8 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_87,plain,(
    ! [B_35,A_36] :
      ( ~ v1_xboole_0(k2_xboole_0(B_35,A_36))
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_90,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_87])).

tff(c_92,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_96,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_22,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_99,plain,(
    ! [A_9] : r1_tarski('#skF_3',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_22])).

tff(c_97,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_42])).

tff(c_122,plain,(
    ! [A_39,B_40] :
      ( ~ v1_xboole_0(k2_xboole_0(A_39,B_40))
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_125,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_122])).

tff(c_127,plain,(
    v1_xboole_0(k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_125])).

tff(c_98,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_4])).

tff(c_131,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_127,c_98])).

tff(c_303,plain,(
    ! [B_53,C_54,A_55] :
      ( r2_hidden(B_53,C_54)
      | ~ r1_tarski(k2_tarski(A_55,B_53),C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_306,plain,(
    ! [C_54] :
      ( r2_hidden('#skF_2',C_54)
      | ~ r1_tarski('#skF_3',C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_303])).

tff(c_314,plain,(
    ! [C_54] : r2_hidden('#skF_2',C_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_306])).

tff(c_325,plain,(
    ! [A_60,C_61,B_62] :
      ( ~ r2_hidden(A_60,C_61)
      | ~ r2_hidden(A_60,B_62)
      | ~ r2_hidden(A_60,k5_xboole_0(B_62,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_329,plain,(
    ! [C_61,B_62] :
      ( ~ r2_hidden('#skF_2',C_61)
      | ~ r2_hidden('#skF_2',B_62) ) ),
    inference(resolution,[status(thm)],[c_314,c_325])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_314,c_329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.23  %$ r2_hidden > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.94/1.23  
% 1.94/1.23  %Foreground sorts:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Background operators:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Foreground operators:
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.94/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.94/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.23  
% 2.13/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.13/1.24  tff(f_73, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.13/1.24  tff(f_49, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.13/1.24  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.13/1.24  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.13/1.24  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_xboole_0)).
% 2.13/1.24  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.13/1.24  tff(f_37, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.13/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.13/1.24  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.13/1.24  tff(c_87, plain, (![B_35, A_36]: (~v1_xboole_0(k2_xboole_0(B_35, A_36)) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.24  tff(c_90, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_87])).
% 2.13/1.24  tff(c_92, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_90])).
% 2.13/1.24  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.13/1.24  tff(c_96, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_92, c_4])).
% 2.13/1.24  tff(c_22, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.13/1.24  tff(c_99, plain, (![A_9]: (r1_tarski('#skF_3', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_22])).
% 2.13/1.24  tff(c_97, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_42])).
% 2.13/1.24  tff(c_122, plain, (![A_39, B_40]: (~v1_xboole_0(k2_xboole_0(A_39, B_40)) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.24  tff(c_125, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0(k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_122])).
% 2.13/1.24  tff(c_127, plain, (v1_xboole_0(k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_125])).
% 2.13/1.24  tff(c_98, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_4])).
% 2.13/1.24  tff(c_131, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_127, c_98])).
% 2.13/1.24  tff(c_303, plain, (![B_53, C_54, A_55]: (r2_hidden(B_53, C_54) | ~r1_tarski(k2_tarski(A_55, B_53), C_54))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.13/1.24  tff(c_306, plain, (![C_54]: (r2_hidden('#skF_2', C_54) | ~r1_tarski('#skF_3', C_54))), inference(superposition, [status(thm), theory('equality')], [c_131, c_303])).
% 2.13/1.24  tff(c_314, plain, (![C_54]: (r2_hidden('#skF_2', C_54))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_306])).
% 2.13/1.24  tff(c_325, plain, (![A_60, C_61, B_62]: (~r2_hidden(A_60, C_61) | ~r2_hidden(A_60, B_62) | ~r2_hidden(A_60, k5_xboole_0(B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.24  tff(c_329, plain, (![C_61, B_62]: (~r2_hidden('#skF_2', C_61) | ~r2_hidden('#skF_2', B_62))), inference(resolution, [status(thm)], [c_314, c_325])).
% 2.13/1.24  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_314, c_314, c_329])).
% 2.13/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  Inference rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Ref     : 0
% 2.13/1.24  #Sup     : 75
% 2.13/1.24  #Fact    : 0
% 2.13/1.24  #Define  : 0
% 2.13/1.24  #Split   : 2
% 2.13/1.24  #Chain   : 0
% 2.13/1.24  #Close   : 0
% 2.13/1.24  
% 2.13/1.24  Ordering : KBO
% 2.13/1.24  
% 2.13/1.24  Simplification rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Subsume      : 12
% 2.13/1.24  #Demod        : 27
% 2.13/1.24  #Tautology    : 54
% 2.13/1.24  #SimpNegUnit  : 0
% 2.13/1.24  #BackRed      : 6
% 2.13/1.24  
% 2.13/1.24  #Partial instantiations: 0
% 2.13/1.24  #Strategies tried      : 1
% 2.13/1.24  
% 2.13/1.24  Timing (in seconds)
% 2.13/1.24  ----------------------
% 2.13/1.24  Preprocessing        : 0.30
% 2.13/1.24  Parsing              : 0.16
% 2.13/1.24  CNF conversion       : 0.02
% 2.13/1.24  Main loop            : 0.19
% 2.13/1.24  Inferencing          : 0.06
% 2.13/1.24  Reduction            : 0.06
% 2.13/1.24  Demodulation         : 0.05
% 2.13/1.24  BG Simplification    : 0.01
% 2.13/1.24  Subsumption          : 0.04
% 2.13/1.24  Abstraction          : 0.01
% 2.13/1.24  MUC search           : 0.00
% 2.13/1.24  Cooper               : 0.00
% 2.13/1.24  Total                : 0.52
% 2.13/1.24  Index Insertion      : 0.00
% 2.13/1.24  Index Deletion       : 0.00
% 2.13/1.24  Index Matching       : 0.00
% 2.13/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
