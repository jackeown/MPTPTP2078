%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:45 EST 2020

% Result     : Theorem 8.17s
% Output     : CNFRefutation 8.17s
% Verified   : 
% Statistics : Number of formulae       :   55 (  79 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 112 expanded)
%              Number of equality atoms :   41 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_36,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_82])).

tff(c_824,plain,(
    ! [A_78,B_79,C_80] :
      ( k4_xboole_0(k2_tarski(A_78,B_79),C_80) = k2_tarski(A_78,B_79)
      | r2_hidden(B_79,C_80)
      | r2_hidden(A_78,C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_856,plain,(
    ! [A_78,B_79,C_80] :
      ( k4_xboole_0(k2_tarski(A_78,B_79),k2_tarski(A_78,B_79)) = k3_xboole_0(k2_tarski(A_78,B_79),C_80)
      | r2_hidden(B_79,C_80)
      | r2_hidden(A_78,C_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_824,c_18])).

tff(c_4089,plain,(
    ! [A_135,B_136,C_137] :
      ( k3_xboole_0(k2_tarski(A_135,B_136),C_137) = k1_xboole_0
      | r2_hidden(B_136,C_137)
      | r2_hidden(A_135,C_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_856])).

tff(c_15632,plain,(
    ! [B_240,A_241,B_242] :
      ( k3_xboole_0(B_240,k2_tarski(A_241,B_242)) = k1_xboole_0
      | r2_hidden(B_242,B_240)
      | r2_hidden(A_241,B_240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4089])).

tff(c_98,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_106,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_98])).

tff(c_232,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_247,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_232])).

tff(c_257,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_247])).

tff(c_416,plain,(
    ! [A_58,B_59,C_60] : k4_xboole_0(k3_xboole_0(A_58,B_59),C_60) = k3_xboole_0(A_58,k4_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_553,plain,(
    ! [B_67,C_68] : k3_xboole_0(B_67,k4_xboole_0(B_67,C_68)) = k4_xboole_0(B_67,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_416])).

tff(c_253,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_232])).

tff(c_569,plain,(
    ! [B_67,C_68] : k5_xboole_0(k4_xboole_0(B_67,C_68),k4_xboole_0(B_67,C_68)) = k4_xboole_0(k4_xboole_0(B_67,C_68),B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_253])).

tff(c_606,plain,(
    ! [B_67,C_68] : k4_xboole_0(k4_xboole_0(B_67,C_68),B_67) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_569])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_267,plain,(
    ! [B_45,A_46] :
      ( B_45 = A_46
      | ~ r1_tarski(B_45,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_404,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | k4_xboole_0(A_57,B_56) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_267])).

tff(c_13981,plain,(
    ! [B_227,A_228] :
      ( B_227 = A_228
      | k4_xboole_0(B_227,A_228) != k1_xboole_0
      | k4_xboole_0(A_228,B_227) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_404])).

tff(c_14031,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | k3_xboole_0(A_11,B_12) != k1_xboole_0
      | k4_xboole_0(k4_xboole_0(A_11,B_12),A_11) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_13981])).

tff(c_14069,plain,(
    ! [A_229,B_230] :
      ( k4_xboole_0(A_229,B_230) = A_229
      | k3_xboole_0(A_229,B_230) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_14031])).

tff(c_32,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14471,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14069,c_32])).

tff(c_15640,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15632,c_14471])).

tff(c_15870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_15640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n010.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:11:59 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.17/2.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.17/2.93  
% 8.17/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.17/2.93  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.17/2.93  
% 8.17/2.93  %Foreground sorts:
% 8.17/2.93  
% 8.17/2.93  
% 8.17/2.93  %Background operators:
% 8.17/2.93  
% 8.17/2.93  
% 8.17/2.93  %Foreground operators:
% 8.17/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.17/2.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.17/2.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.17/2.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.17/2.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.17/2.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.17/2.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.17/2.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.17/2.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.17/2.93  tff('#skF_2', type, '#skF_2': $i).
% 8.17/2.93  tff('#skF_3', type, '#skF_3': $i).
% 8.17/2.93  tff('#skF_1', type, '#skF_1': $i).
% 8.17/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.17/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.17/2.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.17/2.93  
% 8.17/2.94  tff(f_70, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 8.17/2.94  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.17/2.94  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.17/2.94  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.17/2.94  tff(f_59, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 8.17/2.94  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.17/2.94  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.17/2.94  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.17/2.94  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 8.17/2.94  tff(c_36, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.17/2.94  tff(c_34, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.17/2.94  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.17/2.94  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.17/2.94  tff(c_82, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.17/2.94  tff(c_90, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_82])).
% 8.17/2.94  tff(c_824, plain, (![A_78, B_79, C_80]: (k4_xboole_0(k2_tarski(A_78, B_79), C_80)=k2_tarski(A_78, B_79) | r2_hidden(B_79, C_80) | r2_hidden(A_78, C_80))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.17/2.94  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.17/2.94  tff(c_856, plain, (![A_78, B_79, C_80]: (k4_xboole_0(k2_tarski(A_78, B_79), k2_tarski(A_78, B_79))=k3_xboole_0(k2_tarski(A_78, B_79), C_80) | r2_hidden(B_79, C_80) | r2_hidden(A_78, C_80))), inference(superposition, [status(thm), theory('equality')], [c_824, c_18])).
% 8.17/2.94  tff(c_4089, plain, (![A_135, B_136, C_137]: (k3_xboole_0(k2_tarski(A_135, B_136), C_137)=k1_xboole_0 | r2_hidden(B_136, C_137) | r2_hidden(A_135, C_137))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_856])).
% 8.17/2.94  tff(c_15632, plain, (![B_240, A_241, B_242]: (k3_xboole_0(B_240, k2_tarski(A_241, B_242))=k1_xboole_0 | r2_hidden(B_242, B_240) | r2_hidden(A_241, B_240))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4089])).
% 8.17/2.94  tff(c_98, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.17/2.94  tff(c_106, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_98])).
% 8.17/2.94  tff(c_232, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.17/2.94  tff(c_247, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_106, c_232])).
% 8.17/2.94  tff(c_257, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_247])).
% 8.17/2.94  tff(c_416, plain, (![A_58, B_59, C_60]: (k4_xboole_0(k3_xboole_0(A_58, B_59), C_60)=k3_xboole_0(A_58, k4_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.17/2.94  tff(c_553, plain, (![B_67, C_68]: (k3_xboole_0(B_67, k4_xboole_0(B_67, C_68))=k4_xboole_0(B_67, C_68))), inference(superposition, [status(thm), theory('equality')], [c_106, c_416])).
% 8.17/2.94  tff(c_253, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_232])).
% 8.17/2.94  tff(c_569, plain, (![B_67, C_68]: (k5_xboole_0(k4_xboole_0(B_67, C_68), k4_xboole_0(B_67, C_68))=k4_xboole_0(k4_xboole_0(B_67, C_68), B_67))), inference(superposition, [status(thm), theory('equality')], [c_553, c_253])).
% 8.17/2.94  tff(c_606, plain, (![B_67, C_68]: (k4_xboole_0(k4_xboole_0(B_67, C_68), B_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_569])).
% 8.17/2.94  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.17/2.94  tff(c_267, plain, (![B_45, A_46]: (B_45=A_46 | ~r1_tarski(B_45, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.17/2.94  tff(c_404, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | k4_xboole_0(A_57, B_56)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_267])).
% 8.17/2.94  tff(c_13981, plain, (![B_227, A_228]: (B_227=A_228 | k4_xboole_0(B_227, A_228)!=k1_xboole_0 | k4_xboole_0(A_228, B_227)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_404])).
% 8.17/2.94  tff(c_14031, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | k3_xboole_0(A_11, B_12)!=k1_xboole_0 | k4_xboole_0(k4_xboole_0(A_11, B_12), A_11)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_13981])).
% 8.17/2.94  tff(c_14069, plain, (![A_229, B_230]: (k4_xboole_0(A_229, B_230)=A_229 | k3_xboole_0(A_229, B_230)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_606, c_14031])).
% 8.17/2.94  tff(c_32, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.17/2.94  tff(c_14471, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14069, c_32])).
% 8.17/2.94  tff(c_15640, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15632, c_14471])).
% 8.17/2.94  tff(c_15870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_15640])).
% 8.17/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.17/2.94  
% 8.17/2.94  Inference rules
% 8.17/2.94  ----------------------
% 8.17/2.94  #Ref     : 0
% 8.17/2.94  #Sup     : 3909
% 8.17/2.94  #Fact    : 2
% 8.17/2.94  #Define  : 0
% 8.17/2.94  #Split   : 0
% 8.17/2.94  #Chain   : 0
% 8.17/2.94  #Close   : 0
% 8.17/2.94  
% 8.17/2.94  Ordering : KBO
% 8.17/2.94  
% 8.17/2.94  Simplification rules
% 8.17/2.94  ----------------------
% 8.17/2.94  #Subsume      : 117
% 8.17/2.94  #Demod        : 4572
% 8.17/2.94  #Tautology    : 2634
% 8.17/2.94  #SimpNegUnit  : 9
% 8.17/2.94  #BackRed      : 2
% 8.17/2.94  
% 8.17/2.94  #Partial instantiations: 0
% 8.17/2.94  #Strategies tried      : 1
% 8.17/2.94  
% 8.17/2.94  Timing (in seconds)
% 8.17/2.94  ----------------------
% 8.17/2.95  Preprocessing        : 0.31
% 8.17/2.95  Parsing              : 0.17
% 8.17/2.95  CNF conversion       : 0.02
% 8.17/2.95  Main loop            : 1.82
% 8.17/2.95  Inferencing          : 0.43
% 8.17/2.95  Reduction            : 1.00
% 8.17/2.95  Demodulation         : 0.88
% 8.17/2.95  BG Simplification    : 0.05
% 8.17/2.95  Subsumption          : 0.24
% 8.17/2.95  Abstraction          : 0.09
% 8.17/2.95  MUC search           : 0.00
% 8.17/2.95  Cooper               : 0.00
% 8.17/2.95  Total                : 2.16
% 8.17/2.95  Index Insertion      : 0.00
% 8.17/2.95  Index Deletion       : 0.00
% 8.17/2.95  Index Matching       : 0.00
% 8.17/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
