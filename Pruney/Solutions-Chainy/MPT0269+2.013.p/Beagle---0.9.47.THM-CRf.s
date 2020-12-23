%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:45 EST 2020

% Result     : Theorem 4.98s
% Output     : CNFRefutation 4.98s
% Verified   : 
% Statistics : Number of formulae       :   55 (  85 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 101 expanded)
%              Number of equality atoms :   25 (  58 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_70,plain,(
    k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_44,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_74,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_541,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_585,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_7')) = k4_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_541])).

tff(c_597,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_585])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_662,plain,(
    ! [A_85,B_86] : r1_tarski(k3_xboole_0(A_85,B_86),A_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_42])).

tff(c_698,plain,(
    ! [B_87,A_88] : r1_tarski(k3_xboole_0(B_87,A_88),A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_662])).

tff(c_713,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_698])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_763,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_713,c_28])).

tff(c_769,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_763])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_476,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(A_79,k1_tarski(B_80)) = A_79
      | r2_hidden(B_80,A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_506,plain,
    ( k1_xboole_0 = '#skF_6'
    | r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_74])).

tff(c_533,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_506])).

tff(c_340,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62,B_63),A_62)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    ! [C_30,A_26] :
      ( C_30 = A_26
      | ~ r2_hidden(C_30,k1_tarski(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5799,plain,(
    ! [A_227,B_228] :
      ( '#skF_1'(k1_tarski(A_227),B_228) = A_227
      | r1_tarski(k1_tarski(A_227),B_228) ) ),
    inference(resolution,[status(thm)],[c_340,c_48])).

tff(c_5819,plain,(
    '#skF_1'(k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5799,c_769])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5844,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5819,c_6])).

tff(c_5851,plain,(
    r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_5844])).

tff(c_5853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_769,c_5851])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.98/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.98/2.02  
% 4.98/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.98/2.02  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 4.98/2.02  
% 4.98/2.02  %Foreground sorts:
% 4.98/2.02  
% 4.98/2.02  
% 4.98/2.02  %Background operators:
% 4.98/2.02  
% 4.98/2.02  
% 4.98/2.02  %Foreground operators:
% 4.98/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.98/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.98/2.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.98/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.98/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.98/2.02  tff('#skF_7', type, '#skF_7': $i).
% 4.98/2.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.98/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.98/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.98/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.98/2.02  tff('#skF_6', type, '#skF_6': $i).
% 4.98/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.98/2.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.98/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.98/2.02  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.98/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.98/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.98/2.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.98/2.02  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.98/2.02  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.98/2.02  
% 4.98/2.03  tff(f_92, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 4.98/2.03  tff(f_62, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.98/2.03  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.98/2.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.98/2.03  tff(f_60, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.98/2.03  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.98/2.03  tff(f_82, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.98/2.03  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.98/2.03  tff(f_71, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.98/2.03  tff(c_70, plain, (k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.98/2.03  tff(c_44, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.98/2.03  tff(c_74, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.98/2.03  tff(c_541, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.98/2.03  tff(c_585, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_7'))=k4_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_541])).
% 4.98/2.03  tff(c_597, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_585])).
% 4.98/2.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.98/2.03  tff(c_42, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.98/2.03  tff(c_662, plain, (![A_85, B_86]: (r1_tarski(k3_xboole_0(A_85, B_86), A_85))), inference(superposition, [status(thm), theory('equality')], [c_541, c_42])).
% 4.98/2.03  tff(c_698, plain, (![B_87, A_88]: (r1_tarski(k3_xboole_0(B_87, A_88), A_88))), inference(superposition, [status(thm), theory('equality')], [c_2, c_662])).
% 4.98/2.03  tff(c_713, plain, (r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_597, c_698])).
% 4.98/2.03  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.98/2.03  tff(c_763, plain, (k1_tarski('#skF_7')='#skF_6' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_713, c_28])).
% 4.98/2.03  tff(c_769, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_70, c_763])).
% 4.98/2.03  tff(c_72, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.98/2.03  tff(c_476, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k1_tarski(B_80))=A_79 | r2_hidden(B_80, A_79))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.98/2.03  tff(c_506, plain, (k1_xboole_0='#skF_6' | r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_476, c_74])).
% 4.98/2.03  tff(c_533, plain, (r2_hidden('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_72, c_506])).
% 4.98/2.03  tff(c_340, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62, B_63), A_62) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.98/2.03  tff(c_48, plain, (![C_30, A_26]: (C_30=A_26 | ~r2_hidden(C_30, k1_tarski(A_26)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.98/2.03  tff(c_5799, plain, (![A_227, B_228]: ('#skF_1'(k1_tarski(A_227), B_228)=A_227 | r1_tarski(k1_tarski(A_227), B_228))), inference(resolution, [status(thm)], [c_340, c_48])).
% 4.98/2.03  tff(c_5819, plain, ('#skF_1'(k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_5799, c_769])).
% 4.98/2.03  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.98/2.03  tff(c_5844, plain, (~r2_hidden('#skF_7', '#skF_6') | r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5819, c_6])).
% 4.98/2.03  tff(c_5851, plain, (r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_533, c_5844])).
% 4.98/2.03  tff(c_5853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_769, c_5851])).
% 4.98/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.98/2.03  
% 4.98/2.03  Inference rules
% 4.98/2.03  ----------------------
% 4.98/2.03  #Ref     : 0
% 4.98/2.03  #Sup     : 1395
% 4.98/2.03  #Fact    : 0
% 4.98/2.03  #Define  : 0
% 4.98/2.03  #Split   : 0
% 4.98/2.03  #Chain   : 0
% 4.98/2.03  #Close   : 0
% 4.98/2.03  
% 4.98/2.03  Ordering : KBO
% 4.98/2.03  
% 4.98/2.03  Simplification rules
% 4.98/2.03  ----------------------
% 4.98/2.03  #Subsume      : 292
% 4.98/2.03  #Demod        : 1080
% 4.98/2.03  #Tautology    : 769
% 4.98/2.03  #SimpNegUnit  : 74
% 4.98/2.03  #BackRed      : 0
% 4.98/2.03  
% 4.98/2.03  #Partial instantiations: 0
% 4.98/2.03  #Strategies tried      : 1
% 4.98/2.03  
% 4.98/2.03  Timing (in seconds)
% 4.98/2.03  ----------------------
% 4.98/2.04  Preprocessing        : 0.31
% 4.98/2.04  Parsing              : 0.16
% 4.98/2.04  CNF conversion       : 0.02
% 4.98/2.04  Main loop            : 0.90
% 4.98/2.04  Inferencing          : 0.28
% 4.98/2.04  Reduction            : 0.38
% 4.98/2.04  Demodulation         : 0.29
% 4.98/2.04  BG Simplification    : 0.03
% 4.98/2.04  Subsumption          : 0.15
% 4.98/2.04  Abstraction          : 0.04
% 4.98/2.04  MUC search           : 0.00
% 4.98/2.04  Cooper               : 0.00
% 4.98/2.04  Total                : 1.24
% 4.98/2.04  Index Insertion      : 0.00
% 4.98/2.04  Index Deletion       : 0.00
% 4.98/2.04  Index Matching       : 0.00
% 4.98/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
