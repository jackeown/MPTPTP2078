%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:45 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :   51 (  70 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 (  94 expanded)
%              Number of equality atoms :   36 (  54 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_38,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_87,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_83])).

tff(c_664,plain,(
    ! [A_69,B_70,C_71] :
      ( k4_xboole_0(k2_tarski(A_69,B_70),C_71) = k2_tarski(A_69,B_70)
      | r2_hidden(B_70,C_71)
      | r2_hidden(A_69,C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_683,plain,(
    ! [A_69,B_70,C_71] :
      ( k4_xboole_0(k2_tarski(A_69,B_70),k2_tarski(A_69,B_70)) = k3_xboole_0(k2_tarski(A_69,B_70),C_71)
      | r2_hidden(B_70,C_71)
      | r2_hidden(A_69,C_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_20])).

tff(c_4489,plain,(
    ! [A_136,B_137,C_138] :
      ( k3_xboole_0(k2_tarski(A_136,B_137),C_138) = k1_xboole_0
      | r2_hidden(B_137,C_138)
      | r2_hidden(A_136,C_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_683])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16492,plain,(
    ! [C_264,A_265,B_266] :
      ( k3_xboole_0(C_264,k2_tarski(A_265,B_266)) = k1_xboole_0
      | r2_hidden(B_266,C_264)
      | r2_hidden(A_265,C_264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4489,c_2])).

tff(c_18,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_159,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_168,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,k4_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_159])).

tff(c_598,plain,(
    ! [A_67,B_68] : k3_xboole_0(A_67,k4_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_168])).

tff(c_119,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_119])).

tff(c_607,plain,(
    ! [A_67,B_68] : k4_xboole_0(k4_xboole_0(A_67,B_68),k4_xboole_0(A_67,B_68)) = k4_xboole_0(k4_xboole_0(A_67,B_68),A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_131])).

tff(c_651,plain,(
    ! [A_67,B_68] : k4_xboole_0(k4_xboole_0(A_67,B_68),A_67) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_607])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [B_40,A_41] :
      ( B_40 = A_41
      | ~ r1_tarski(B_40,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1538,plain,(
    ! [B_96,A_97] :
      ( B_96 = A_97
      | ~ r1_tarski(B_96,A_97)
      | k4_xboole_0(A_97,B_96) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_149])).

tff(c_13694,plain,(
    ! [B_229,A_230] :
      ( B_229 = A_230
      | k4_xboole_0(B_229,A_230) != k1_xboole_0
      | k4_xboole_0(A_230,B_229) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_1538])).

tff(c_13730,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = A_67
      | k4_xboole_0(A_67,k4_xboole_0(A_67,B_68)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_13694])).

tff(c_13782,plain,(
    ! [A_231,B_232] :
      ( k4_xboole_0(A_231,B_232) = A_231
      | k3_xboole_0(A_231,B_232) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_13730])).

tff(c_34,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14176,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13782,c_34])).

tff(c_16514,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16492,c_14176])).

tff(c_16771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_16514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:45:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.79/2.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.95  
% 7.79/2.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.95  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.79/2.95  
% 7.79/2.95  %Foreground sorts:
% 7.79/2.95  
% 7.79/2.95  
% 7.79/2.95  %Background operators:
% 7.79/2.95  
% 7.79/2.95  
% 7.79/2.95  %Foreground operators:
% 7.79/2.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.79/2.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.79/2.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.79/2.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.79/2.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.79/2.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.79/2.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.79/2.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.79/2.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.79/2.95  tff('#skF_2', type, '#skF_2': $i).
% 7.79/2.95  tff('#skF_3', type, '#skF_3': $i).
% 7.79/2.95  tff('#skF_1', type, '#skF_1': $i).
% 7.79/2.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.79/2.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.79/2.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.79/2.95  
% 7.79/2.96  tff(f_70, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 7.79/2.96  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.79/2.96  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.79/2.96  tff(f_59, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 7.79/2.96  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.79/2.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.79/2.96  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.79/2.96  tff(c_38, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.79/2.96  tff(c_36, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.79/2.96  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.79/2.96  tff(c_83, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.79/2.96  tff(c_87, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_83])).
% 7.79/2.96  tff(c_664, plain, (![A_69, B_70, C_71]: (k4_xboole_0(k2_tarski(A_69, B_70), C_71)=k2_tarski(A_69, B_70) | r2_hidden(B_70, C_71) | r2_hidden(A_69, C_71))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.79/2.96  tff(c_20, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.79/2.96  tff(c_683, plain, (![A_69, B_70, C_71]: (k4_xboole_0(k2_tarski(A_69, B_70), k2_tarski(A_69, B_70))=k3_xboole_0(k2_tarski(A_69, B_70), C_71) | r2_hidden(B_70, C_71) | r2_hidden(A_69, C_71))), inference(superposition, [status(thm), theory('equality')], [c_664, c_20])).
% 7.79/2.96  tff(c_4489, plain, (![A_136, B_137, C_138]: (k3_xboole_0(k2_tarski(A_136, B_137), C_138)=k1_xboole_0 | r2_hidden(B_137, C_138) | r2_hidden(A_136, C_138))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_683])).
% 7.79/2.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.79/2.96  tff(c_16492, plain, (![C_264, A_265, B_266]: (k3_xboole_0(C_264, k2_tarski(A_265, B_266))=k1_xboole_0 | r2_hidden(B_266, C_264) | r2_hidden(A_265, C_264))), inference(superposition, [status(thm), theory('equality')], [c_4489, c_2])).
% 7.79/2.96  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.79/2.96  tff(c_159, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.79/2.96  tff(c_168, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k3_xboole_0(A_12, k4_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_159])).
% 7.79/2.96  tff(c_598, plain, (![A_67, B_68]: (k3_xboole_0(A_67, k4_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_168])).
% 7.79/2.96  tff(c_119, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.79/2.96  tff(c_131, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_119])).
% 7.79/2.96  tff(c_607, plain, (![A_67, B_68]: (k4_xboole_0(k4_xboole_0(A_67, B_68), k4_xboole_0(A_67, B_68))=k4_xboole_0(k4_xboole_0(A_67, B_68), A_67))), inference(superposition, [status(thm), theory('equality')], [c_598, c_131])).
% 7.79/2.96  tff(c_651, plain, (![A_67, B_68]: (k4_xboole_0(k4_xboole_0(A_67, B_68), A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_607])).
% 7.79/2.96  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.79/2.96  tff(c_149, plain, (![B_40, A_41]: (B_40=A_41 | ~r1_tarski(B_40, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.79/2.96  tff(c_1538, plain, (![B_96, A_97]: (B_96=A_97 | ~r1_tarski(B_96, A_97) | k4_xboole_0(A_97, B_96)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_149])).
% 7.79/2.96  tff(c_13694, plain, (![B_229, A_230]: (B_229=A_230 | k4_xboole_0(B_229, A_230)!=k1_xboole_0 | k4_xboole_0(A_230, B_229)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1538])).
% 7.79/2.96  tff(c_13730, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=A_67 | k4_xboole_0(A_67, k4_xboole_0(A_67, B_68))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_651, c_13694])).
% 7.79/2.96  tff(c_13782, plain, (![A_231, B_232]: (k4_xboole_0(A_231, B_232)=A_231 | k3_xboole_0(A_231, B_232)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_13730])).
% 7.79/2.96  tff(c_34, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.79/2.96  tff(c_14176, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13782, c_34])).
% 7.79/2.96  tff(c_16514, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16492, c_14176])).
% 7.79/2.96  tff(c_16771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_16514])).
% 7.79/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.96  
% 7.79/2.96  Inference rules
% 7.79/2.96  ----------------------
% 7.79/2.96  #Ref     : 0
% 7.79/2.96  #Sup     : 4106
% 7.79/2.96  #Fact    : 4
% 7.79/2.96  #Define  : 0
% 7.79/2.96  #Split   : 0
% 7.79/2.96  #Chain   : 0
% 7.79/2.96  #Close   : 0
% 7.79/2.96  
% 7.79/2.96  Ordering : KBO
% 7.79/2.96  
% 7.79/2.96  Simplification rules
% 7.79/2.96  ----------------------
% 7.79/2.96  #Subsume      : 224
% 7.79/2.96  #Demod        : 4705
% 7.79/2.96  #Tautology    : 2657
% 7.79/2.96  #SimpNegUnit  : 21
% 7.79/2.96  #BackRed      : 0
% 7.79/2.96  
% 7.79/2.96  #Partial instantiations: 0
% 7.79/2.96  #Strategies tried      : 1
% 7.79/2.96  
% 7.79/2.96  Timing (in seconds)
% 7.79/2.96  ----------------------
% 7.79/2.97  Preprocessing        : 0.29
% 7.79/2.97  Parsing              : 0.15
% 7.79/2.97  CNF conversion       : 0.02
% 7.79/2.97  Main loop            : 1.91
% 7.79/2.97  Inferencing          : 0.45
% 7.79/2.97  Reduction            : 1.05
% 7.79/2.97  Demodulation         : 0.92
% 7.79/2.97  BG Simplification    : 0.05
% 7.79/2.97  Subsumption          : 0.26
% 7.79/2.97  Abstraction          : 0.09
% 7.79/2.97  MUC search           : 0.00
% 7.79/2.97  Cooper               : 0.00
% 7.79/2.97  Total                : 2.23
% 7.79/2.97  Index Insertion      : 0.00
% 7.79/2.97  Index Deletion       : 0.00
% 7.79/2.97  Index Matching       : 0.00
% 7.79/2.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
