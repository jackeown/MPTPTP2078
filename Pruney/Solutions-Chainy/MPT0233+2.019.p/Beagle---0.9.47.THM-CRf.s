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
% DateTime   : Thu Dec  3 09:49:26 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :   60 (  70 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  69 expanded)
%              Number of equality atoms :   35 (  47 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_34,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_108,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_108])).

tff(c_18,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_283,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_1','#skF_2')) = k5_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_18])).

tff(c_292,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_1','#skF_2')) = k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_283])).

tff(c_672,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) = k2_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_292])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_128,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_108])).

tff(c_252,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k4_xboole_0(B_55,A_54)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_264,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k5_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_252])).

tff(c_612,plain,(
    ! [A_72,B_73] : k2_xboole_0(A_72,k4_xboole_0(A_72,B_73)) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_264])).

tff(c_628,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_612])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_26,B_27] : r1_tarski(k1_tarski(A_26),k2_tarski(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_126,plain,(
    ! [A_26,B_27] : k4_xboole_0(k1_tarski(A_26),k2_tarski(A_26,B_27)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_108])).

tff(c_387,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_418,plain,(
    ! [A_26,B_27] : k3_xboole_0(k1_tarski(A_26),k2_tarski(A_26,B_27)) = k4_xboole_0(k1_tarski(A_26),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_387])).

tff(c_439,plain,(
    ! [A_26,B_27] : k3_xboole_0(k1_tarski(A_26),k2_tarski(A_26,B_27)) = k1_tarski(A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_418])).

tff(c_942,plain,(
    ! [A_93,B_94,C_95] : r1_tarski(k2_xboole_0(k3_xboole_0(A_93,B_94),k3_xboole_0(A_93,C_95)),k2_xboole_0(B_94,C_95)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_963,plain,(
    ! [A_26,C_95,B_27] : r1_tarski(k2_xboole_0(k1_tarski(A_26),k3_xboole_0(k1_tarski(A_26),C_95)),k2_xboole_0(k2_tarski(A_26,B_27),C_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_942])).

tff(c_3588,plain,(
    ! [A_187,B_188,C_189] : r1_tarski(k1_tarski(A_187),k2_xboole_0(k2_tarski(A_187,B_188),C_189)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_963])).

tff(c_3601,plain,(
    r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_3588])).

tff(c_30,plain,(
    ! [C_30,A_28,B_29] :
      ( C_30 = A_28
      | B_29 = A_28
      | ~ r1_tarski(k1_tarski(A_28),k2_tarski(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3644,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3601,c_30])).

tff(c_3651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_3644])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:51:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.67  
% 3.83/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.68  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.94/1.68  
% 3.94/1.68  %Foreground sorts:
% 3.94/1.68  
% 3.94/1.68  
% 3.94/1.68  %Background operators:
% 3.94/1.68  
% 3.94/1.68  
% 3.94/1.68  %Foreground operators:
% 3.94/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.94/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.94/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.94/1.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.94/1.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.94/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.94/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.94/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.94/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.94/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.94/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.94/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.94/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.94/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.94/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.94/1.68  
% 3.94/1.69  tff(f_72, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.94/1.69  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.94/1.69  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.94/1.69  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.94/1.69  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.94/1.69  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.94/1.69  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.94/1.69  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.94/1.69  tff(f_53, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.94/1.69  tff(f_33, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 3.94/1.69  tff(f_62, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.94/1.69  tff(c_34, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.94/1.69  tff(c_32, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.94/1.69  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.94/1.69  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.94/1.69  tff(c_36, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.94/1.69  tff(c_108, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.94/1.69  tff(c_125, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_108])).
% 3.94/1.69  tff(c_18, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.94/1.69  tff(c_283, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_1', '#skF_2'))=k5_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_18])).
% 3.94/1.69  tff(c_292, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_1', '#skF_2'))=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_283])).
% 3.94/1.69  tff(c_672, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))=k2_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2, c_292])).
% 3.94/1.69  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.94/1.69  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.94/1.69  tff(c_128, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_108])).
% 3.94/1.69  tff(c_252, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k4_xboole_0(B_55, A_54))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.94/1.69  tff(c_264, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k5_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_128, c_252])).
% 3.94/1.69  tff(c_612, plain, (![A_72, B_73]: (k2_xboole_0(A_72, k4_xboole_0(A_72, B_73))=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_264])).
% 3.94/1.69  tff(c_628, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k3_xboole_0(A_11, B_12))=A_11)), inference(superposition, [status(thm), theory('equality')], [c_14, c_612])).
% 3.94/1.69  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.94/1.69  tff(c_28, plain, (![A_26, B_27]: (r1_tarski(k1_tarski(A_26), k2_tarski(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.94/1.69  tff(c_126, plain, (![A_26, B_27]: (k4_xboole_0(k1_tarski(A_26), k2_tarski(A_26, B_27))=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_108])).
% 3.94/1.69  tff(c_387, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.94/1.69  tff(c_418, plain, (![A_26, B_27]: (k3_xboole_0(k1_tarski(A_26), k2_tarski(A_26, B_27))=k4_xboole_0(k1_tarski(A_26), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_126, c_387])).
% 3.94/1.69  tff(c_439, plain, (![A_26, B_27]: (k3_xboole_0(k1_tarski(A_26), k2_tarski(A_26, B_27))=k1_tarski(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_418])).
% 3.94/1.69  tff(c_942, plain, (![A_93, B_94, C_95]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_93, B_94), k3_xboole_0(A_93, C_95)), k2_xboole_0(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.94/1.69  tff(c_963, plain, (![A_26, C_95, B_27]: (r1_tarski(k2_xboole_0(k1_tarski(A_26), k3_xboole_0(k1_tarski(A_26), C_95)), k2_xboole_0(k2_tarski(A_26, B_27), C_95)))), inference(superposition, [status(thm), theory('equality')], [c_439, c_942])).
% 3.94/1.69  tff(c_3588, plain, (![A_187, B_188, C_189]: (r1_tarski(k1_tarski(A_187), k2_xboole_0(k2_tarski(A_187, B_188), C_189)))), inference(demodulation, [status(thm), theory('equality')], [c_628, c_963])).
% 3.94/1.69  tff(c_3601, plain, (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_672, c_3588])).
% 3.94/1.69  tff(c_30, plain, (![C_30, A_28, B_29]: (C_30=A_28 | B_29=A_28 | ~r1_tarski(k1_tarski(A_28), k2_tarski(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.94/1.69  tff(c_3644, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_3601, c_30])).
% 3.94/1.69  tff(c_3651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_3644])).
% 3.94/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.69  
% 3.94/1.69  Inference rules
% 3.94/1.69  ----------------------
% 3.94/1.69  #Ref     : 0
% 3.94/1.69  #Sup     : 876
% 3.94/1.69  #Fact    : 0
% 3.94/1.69  #Define  : 0
% 3.94/1.69  #Split   : 0
% 3.94/1.69  #Chain   : 0
% 3.94/1.69  #Close   : 0
% 3.94/1.69  
% 3.94/1.69  Ordering : KBO
% 3.94/1.69  
% 3.94/1.69  Simplification rules
% 3.94/1.69  ----------------------
% 3.94/1.69  #Subsume      : 1
% 3.94/1.69  #Demod        : 788
% 3.94/1.69  #Tautology    : 718
% 3.94/1.69  #SimpNegUnit  : 1
% 3.94/1.69  #BackRed      : 0
% 3.94/1.69  
% 3.94/1.69  #Partial instantiations: 0
% 3.94/1.69  #Strategies tried      : 1
% 3.94/1.69  
% 3.94/1.69  Timing (in seconds)
% 3.94/1.69  ----------------------
% 3.94/1.69  Preprocessing        : 0.31
% 3.94/1.69  Parsing              : 0.17
% 3.94/1.69  CNF conversion       : 0.02
% 3.94/1.69  Main loop            : 0.62
% 3.94/1.69  Inferencing          : 0.20
% 3.94/1.69  Reduction            : 0.28
% 3.94/1.69  Demodulation         : 0.23
% 3.94/1.69  BG Simplification    : 0.02
% 3.94/1.69  Subsumption          : 0.09
% 3.94/1.69  Abstraction          : 0.03
% 3.94/1.69  MUC search           : 0.00
% 3.94/1.69  Cooper               : 0.00
% 3.94/1.69  Total                : 0.96
% 3.94/1.69  Index Insertion      : 0.00
% 3.94/1.69  Index Deletion       : 0.00
% 3.94/1.69  Index Matching       : 0.00
% 3.94/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
