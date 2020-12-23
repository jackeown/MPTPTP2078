%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:19 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(c_34,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_102,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(k2_tarski(A_66,B_67),C_68)
      | ~ r2_hidden(B_67,C_68)
      | ~ r2_hidden(A_66,C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_115,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_xboole_0(k2_tarski(A_69,B_70),C_71) = C_71
      | ~ r2_hidden(B_70,C_71)
      | ~ r2_hidden(A_69,C_71) ) ),
    inference(resolution,[status(thm)],[c_102,c_35])).

tff(c_30,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_125,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_30])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.18  
% 1.82/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.18  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.82/1.18  
% 1.82/1.18  %Foreground sorts:
% 1.82/1.18  
% 1.82/1.18  
% 1.82/1.18  %Background operators:
% 1.82/1.18  
% 1.82/1.18  
% 1.82/1.18  %Foreground operators:
% 1.82/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.82/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.82/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.82/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.82/1.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.18  
% 1.82/1.19  tff(f_62, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 1.82/1.19  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.82/1.19  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.82/1.19  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.82/1.19  tff(c_34, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.82/1.19  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.82/1.19  tff(c_102, plain, (![A_66, B_67, C_68]: (r1_tarski(k2_tarski(A_66, B_67), C_68) | ~r2_hidden(B_67, C_68) | ~r2_hidden(A_66, C_68))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.82/1.19  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.19  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.82/1.19  tff(c_35, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.82/1.19  tff(c_115, plain, (![A_69, B_70, C_71]: (k2_xboole_0(k2_tarski(A_69, B_70), C_71)=C_71 | ~r2_hidden(B_70, C_71) | ~r2_hidden(A_69, C_71))), inference(resolution, [status(thm)], [c_102, c_35])).
% 1.82/1.19  tff(c_30, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.82/1.19  tff(c_125, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_115, c_30])).
% 1.82/1.19  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_125])).
% 1.82/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.19  
% 1.82/1.19  Inference rules
% 1.82/1.19  ----------------------
% 1.82/1.19  #Ref     : 0
% 1.82/1.19  #Sup     : 22
% 1.82/1.19  #Fact    : 0
% 1.82/1.19  #Define  : 0
% 1.82/1.19  #Split   : 0
% 1.82/1.19  #Chain   : 0
% 1.82/1.19  #Close   : 0
% 1.82/1.19  
% 1.82/1.19  Ordering : KBO
% 1.82/1.19  
% 1.82/1.19  Simplification rules
% 1.82/1.19  ----------------------
% 1.82/1.19  #Subsume      : 0
% 1.82/1.19  #Demod        : 3
% 1.82/1.19  #Tautology    : 17
% 1.82/1.19  #SimpNegUnit  : 0
% 1.82/1.19  #BackRed      : 0
% 1.82/1.19  
% 1.82/1.19  #Partial instantiations: 0
% 1.82/1.19  #Strategies tried      : 1
% 1.82/1.19  
% 1.82/1.19  Timing (in seconds)
% 1.82/1.19  ----------------------
% 1.82/1.19  Preprocessing        : 0.30
% 1.82/1.19  Parsing              : 0.16
% 1.82/1.19  CNF conversion       : 0.02
% 1.82/1.19  Main loop            : 0.11
% 1.82/1.19  Inferencing          : 0.04
% 1.82/1.19  Reduction            : 0.03
% 1.82/1.19  Demodulation         : 0.03
% 1.82/1.19  BG Simplification    : 0.01
% 1.82/1.19  Subsumption          : 0.01
% 1.82/1.19  Abstraction          : 0.01
% 1.82/1.19  MUC search           : 0.00
% 1.82/1.19  Cooper               : 0.00
% 1.82/1.19  Total                : 0.43
% 1.82/1.19  Index Insertion      : 0.00
% 1.82/1.19  Index Deletion       : 0.00
% 1.82/1.19  Index Matching       : 0.00
% 1.82/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
