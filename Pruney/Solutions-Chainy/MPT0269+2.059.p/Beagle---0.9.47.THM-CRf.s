%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:51 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  47 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_163,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,k1_tarski(B_44)) = A_43
      | r2_hidden(B_44,A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_38,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_175,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_38])).

tff(c_184,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_175])).

tff(c_16,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_394,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(k2_tarski(A_65,B_66),C_67)
      | ~ r2_hidden(B_66,C_67)
      | ~ r2_hidden(A_65,C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_407,plain,(
    ! [A_68,C_69] :
      ( r1_tarski(k1_tarski(A_68),C_69)
      | ~ r2_hidden(A_68,C_69)
      | ~ r2_hidden(A_68,C_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_394])).

tff(c_34,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_303,plain,(
    ! [A_58,B_59] :
      ( k2_xboole_0(A_58,k4_xboole_0(B_59,A_58)) = B_59
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_324,plain,
    ( k2_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = '#skF_1'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_303])).

tff(c_328,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_324])).

tff(c_329,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_328])).

tff(c_410,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_407,c_329])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:49:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.26  
% 2.11/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.26  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.11/1.26  
% 2.11/1.26  %Foreground sorts:
% 2.11/1.26  
% 2.11/1.26  
% 2.11/1.26  %Background operators:
% 2.11/1.26  
% 2.11/1.26  
% 2.11/1.26  %Foreground operators:
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.26  
% 2.11/1.27  tff(f_70, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 2.11/1.27  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.11/1.27  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.11/1.27  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.11/1.27  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.11/1.27  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.11/1.27  tff(c_36, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.11/1.27  tff(c_163, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k1_tarski(B_44))=A_43 | r2_hidden(B_44, A_43))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.11/1.27  tff(c_38, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.11/1.27  tff(c_175, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_163, c_38])).
% 2.11/1.27  tff(c_184, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_175])).
% 2.11/1.27  tff(c_16, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.27  tff(c_394, plain, (![A_65, B_66, C_67]: (r1_tarski(k2_tarski(A_65, B_66), C_67) | ~r2_hidden(B_66, C_67) | ~r2_hidden(A_65, C_67))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.27  tff(c_407, plain, (![A_68, C_69]: (r1_tarski(k1_tarski(A_68), C_69) | ~r2_hidden(A_68, C_69) | ~r2_hidden(A_68, C_69))), inference(superposition, [status(thm), theory('equality')], [c_16, c_394])).
% 2.11/1.27  tff(c_34, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.11/1.27  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.27  tff(c_303, plain, (![A_58, B_59]: (k2_xboole_0(A_58, k4_xboole_0(B_59, A_58))=B_59 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.27  tff(c_324, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)='#skF_1' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_303])).
% 2.11/1.27  tff(c_328, plain, (k1_tarski('#skF_2')='#skF_1' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_324])).
% 2.11/1.27  tff(c_329, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34, c_328])).
% 2.11/1.27  tff(c_410, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_407, c_329])).
% 2.11/1.27  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_410])).
% 2.11/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.27  
% 2.11/1.27  Inference rules
% 2.11/1.27  ----------------------
% 2.11/1.27  #Ref     : 0
% 2.11/1.27  #Sup     : 92
% 2.11/1.27  #Fact    : 0
% 2.11/1.27  #Define  : 0
% 2.11/1.27  #Split   : 0
% 2.11/1.27  #Chain   : 0
% 2.11/1.27  #Close   : 0
% 2.11/1.27  
% 2.11/1.27  Ordering : KBO
% 2.11/1.27  
% 2.11/1.27  Simplification rules
% 2.11/1.27  ----------------------
% 2.11/1.27  #Subsume      : 7
% 2.11/1.27  #Demod        : 30
% 2.11/1.27  #Tautology    : 65
% 2.11/1.27  #SimpNegUnit  : 5
% 2.11/1.27  #BackRed      : 1
% 2.11/1.27  
% 2.11/1.27  #Partial instantiations: 0
% 2.11/1.27  #Strategies tried      : 1
% 2.11/1.27  
% 2.11/1.27  Timing (in seconds)
% 2.11/1.27  ----------------------
% 2.11/1.27  Preprocessing        : 0.30
% 2.11/1.27  Parsing              : 0.16
% 2.11/1.27  CNF conversion       : 0.02
% 2.11/1.27  Main loop            : 0.21
% 2.11/1.27  Inferencing          : 0.09
% 2.11/1.27  Reduction            : 0.07
% 2.11/1.27  Demodulation         : 0.05
% 2.11/1.27  BG Simplification    : 0.01
% 2.11/1.27  Subsumption          : 0.03
% 2.11/1.27  Abstraction          : 0.01
% 2.11/1.27  MUC search           : 0.00
% 2.11/1.27  Cooper               : 0.00
% 2.11/1.27  Total                : 0.53
% 2.11/1.27  Index Insertion      : 0.00
% 2.11/1.27  Index Deletion       : 0.00
% 2.11/1.27  Index Matching       : 0.00
% 2.11/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
