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
% DateTime   : Thu Dec  3 09:54:47 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :   58 (  79 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 ( 100 expanded)
%              Number of equality atoms :   40 (  58 expanded)
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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_36,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_1093,plain,(
    ! [A_87,B_88,C_89] :
      ( k4_xboole_0(k2_tarski(A_87,B_88),C_89) = k2_tarski(A_87,B_88)
      | r2_hidden(B_88,C_89)
      | r2_hidden(A_87,C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1136,plain,(
    ! [A_87,B_88,C_89] :
      ( k4_xboole_0(k2_tarski(A_87,B_88),k2_tarski(A_87,B_88)) = k3_xboole_0(k2_tarski(A_87,B_88),C_89)
      | r2_hidden(B_88,C_89)
      | r2_hidden(A_87,C_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_18])).

tff(c_6217,plain,(
    ! [A_162,B_163,C_164] :
      ( k3_xboole_0(k2_tarski(A_162,B_163),C_164) = k1_xboole_0
      | r2_hidden(B_163,C_164)
      | r2_hidden(A_162,C_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_1136])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_171,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2099,plain,(
    ! [B_106,A_107] :
      ( B_106 = A_107
      | ~ r1_tarski(B_106,A_107)
      | k4_xboole_0(A_107,B_106) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_171])).

tff(c_2111,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_2099])).

tff(c_2125,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(A_108,B_109) = A_108
      | k3_xboole_0(A_108,B_109) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2111])).

tff(c_16,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_212,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_250,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_212])).

tff(c_256,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_250])).

tff(c_308,plain,(
    ! [A_46,B_47] : k5_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_323,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k4_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_308])).

tff(c_328,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_323])).

tff(c_435,plain,(
    ! [A_57,B_58,C_59] : k4_xboole_0(k3_xboole_0(A_57,B_58),C_59) = k3_xboole_0(A_57,k4_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_53])).

tff(c_221,plain,(
    ! [A_41,B_42] : k4_xboole_0(k3_xboole_0(A_41,B_42),A_41) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_60])).

tff(c_499,plain,(
    ! [C_60,B_61] : k3_xboole_0(C_60,k4_xboole_0(B_61,C_60)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_221])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_513,plain,(
    ! [C_60,B_61] : k4_xboole_0(C_60,k4_xboole_0(B_61,C_60)) = k5_xboole_0(C_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_12])).

tff(c_547,plain,(
    ! [C_60,B_61] : k4_xboole_0(C_60,k4_xboole_0(B_61,C_60)) = C_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_513])).

tff(c_4036,plain,(
    ! [B_138,A_139] :
      ( k4_xboole_0(B_138,A_139) = B_138
      | k3_xboole_0(A_139,B_138) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2125,c_547])).

tff(c_32,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4286,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4036,c_32])).

tff(c_6236,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6217,c_4286])).

tff(c_6370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_6236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:01:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.92  
% 4.69/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.92  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.69/1.92  
% 4.69/1.92  %Foreground sorts:
% 4.69/1.92  
% 4.69/1.92  
% 4.69/1.92  %Background operators:
% 4.69/1.92  
% 4.69/1.92  
% 4.69/1.92  %Foreground operators:
% 4.69/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.69/1.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.69/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.69/1.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.69/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/1.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.69/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.69/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.69/1.92  tff('#skF_2', type, '#skF_2': $i).
% 4.69/1.92  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.92  tff('#skF_1', type, '#skF_1': $i).
% 4.69/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.69/1.92  
% 4.77/1.94  tff(f_68, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 4.77/1.94  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.77/1.94  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.77/1.94  tff(f_57, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 4.77/1.94  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.77/1.94  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.77/1.94  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.77/1.94  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.77/1.94  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.77/1.94  tff(c_36, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.77/1.94  tff(c_34, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.77/1.94  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.77/1.94  tff(c_53, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.77/1.94  tff(c_61, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_53])).
% 4.77/1.94  tff(c_1093, plain, (![A_87, B_88, C_89]: (k4_xboole_0(k2_tarski(A_87, B_88), C_89)=k2_tarski(A_87, B_88) | r2_hidden(B_88, C_89) | r2_hidden(A_87, C_89))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.77/1.94  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.94  tff(c_1136, plain, (![A_87, B_88, C_89]: (k4_xboole_0(k2_tarski(A_87, B_88), k2_tarski(A_87, B_88))=k3_xboole_0(k2_tarski(A_87, B_88), C_89) | r2_hidden(B_88, C_89) | r2_hidden(A_87, C_89))), inference(superposition, [status(thm), theory('equality')], [c_1093, c_18])).
% 4.77/1.94  tff(c_6217, plain, (![A_162, B_163, C_164]: (k3_xboole_0(k2_tarski(A_162, B_163), C_164)=k1_xboole_0 | r2_hidden(B_163, C_164) | r2_hidden(A_162, C_164))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_1136])).
% 4.77/1.94  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.77/1.94  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.77/1.94  tff(c_171, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.77/1.94  tff(c_2099, plain, (![B_106, A_107]: (B_106=A_107 | ~r1_tarski(B_106, A_107) | k4_xboole_0(A_107, B_106)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_171])).
% 4.77/1.94  tff(c_2111, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=A_7 | k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_2099])).
% 4.77/1.94  tff(c_2125, plain, (![A_108, B_109]: (k4_xboole_0(A_108, B_109)=A_108 | k3_xboole_0(A_108, B_109)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2111])).
% 4.77/1.94  tff(c_16, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.77/1.94  tff(c_212, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.94  tff(c_250, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_212])).
% 4.77/1.94  tff(c_256, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_250])).
% 4.77/1.94  tff(c_308, plain, (![A_46, B_47]: (k5_xboole_0(A_46, k3_xboole_0(A_46, B_47))=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.77/1.94  tff(c_323, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k4_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_256, c_308])).
% 4.77/1.94  tff(c_328, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_323])).
% 4.77/1.94  tff(c_435, plain, (![A_57, B_58, C_59]: (k4_xboole_0(k3_xboole_0(A_57, B_58), C_59)=k3_xboole_0(A_57, k4_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.77/1.94  tff(c_60, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_53])).
% 4.77/1.94  tff(c_221, plain, (![A_41, B_42]: (k4_xboole_0(k3_xboole_0(A_41, B_42), A_41)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_212, c_60])).
% 4.77/1.94  tff(c_499, plain, (![C_60, B_61]: (k3_xboole_0(C_60, k4_xboole_0(B_61, C_60))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_435, c_221])).
% 4.77/1.94  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.77/1.94  tff(c_513, plain, (![C_60, B_61]: (k4_xboole_0(C_60, k4_xboole_0(B_61, C_60))=k5_xboole_0(C_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_499, c_12])).
% 4.77/1.94  tff(c_547, plain, (![C_60, B_61]: (k4_xboole_0(C_60, k4_xboole_0(B_61, C_60))=C_60)), inference(demodulation, [status(thm), theory('equality')], [c_328, c_513])).
% 4.77/1.94  tff(c_4036, plain, (![B_138, A_139]: (k4_xboole_0(B_138, A_139)=B_138 | k3_xboole_0(A_139, B_138)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2125, c_547])).
% 4.77/1.94  tff(c_32, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.77/1.94  tff(c_4286, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4036, c_32])).
% 4.77/1.94  tff(c_6236, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6217, c_4286])).
% 4.77/1.94  tff(c_6370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_6236])).
% 4.77/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.94  
% 4.77/1.94  Inference rules
% 4.77/1.94  ----------------------
% 4.77/1.94  #Ref     : 0
% 4.77/1.94  #Sup     : 1557
% 4.77/1.94  #Fact    : 0
% 4.77/1.94  #Define  : 0
% 4.77/1.94  #Split   : 0
% 4.77/1.94  #Chain   : 0
% 4.77/1.94  #Close   : 0
% 4.77/1.94  
% 4.77/1.94  Ordering : KBO
% 4.77/1.94  
% 4.77/1.94  Simplification rules
% 4.77/1.94  ----------------------
% 4.77/1.94  #Subsume      : 43
% 4.77/1.94  #Demod        : 1340
% 4.77/1.94  #Tautology    : 1113
% 4.77/1.94  #SimpNegUnit  : 5
% 4.77/1.94  #BackRed      : 0
% 4.77/1.94  
% 4.77/1.94  #Partial instantiations: 0
% 4.77/1.94  #Strategies tried      : 1
% 4.77/1.94  
% 4.77/1.94  Timing (in seconds)
% 4.77/1.94  ----------------------
% 4.77/1.94  Preprocessing        : 0.30
% 4.77/1.94  Parsing              : 0.15
% 4.77/1.94  CNF conversion       : 0.02
% 4.77/1.94  Main loop            : 0.86
% 4.77/1.94  Inferencing          : 0.30
% 4.77/1.94  Reduction            : 0.35
% 4.77/1.94  Demodulation         : 0.27
% 4.77/1.94  BG Simplification    : 0.03
% 4.77/1.94  Subsumption          : 0.13
% 4.77/1.94  Abstraction          : 0.06
% 4.77/1.94  MUC search           : 0.00
% 4.77/1.94  Cooper               : 0.00
% 4.77/1.94  Total                : 1.20
% 4.77/1.94  Index Insertion      : 0.00
% 4.77/1.94  Index Deletion       : 0.00
% 4.77/1.94  Index Matching       : 0.00
% 4.77/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
