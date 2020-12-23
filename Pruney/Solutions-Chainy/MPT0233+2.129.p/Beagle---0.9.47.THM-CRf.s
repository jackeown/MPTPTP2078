%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:37 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   51 (  54 expanded)
%              Number of leaves         :   29 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   55 (  65 expanded)
%              Number of equality atoms :   28 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_60,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_58,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    ! [D_22,B_18] : r2_hidden(D_22,k2_tarski(D_22,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_209,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(k4_xboole_0(A_57,B_58),C_59)
      | ~ r1_tarski(A_57,k2_xboole_0(B_58,C_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_145,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_157,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_145])).

tff(c_213,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,k2_xboole_0(B_58,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_209,c_157])).

tff(c_231,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k1_xboole_0
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_213])).

tff(c_245,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_231])).

tff(c_34,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_363,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_34])).

tff(c_367,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_363])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_669,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k2_tarski('#skF_7','#skF_8'))
      | ~ r2_hidden(D_89,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_4])).

tff(c_36,plain,(
    ! [D_22,B_18,A_17] :
      ( D_22 = B_18
      | D_22 = A_17
      | ~ r2_hidden(D_22,k2_tarski(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_684,plain,(
    ! [D_90] :
      ( D_90 = '#skF_8'
      | D_90 = '#skF_7'
      | ~ r2_hidden(D_90,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_669,c_36])).

tff(c_688,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_684])).

tff(c_696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:17:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.44  
% 2.60/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.44  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 2.60/1.44  
% 2.60/1.44  %Foreground sorts:
% 2.60/1.44  
% 2.60/1.44  
% 2.60/1.44  %Background operators:
% 2.60/1.44  
% 2.60/1.44  
% 2.60/1.44  %Foreground operators:
% 2.60/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.60/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.60/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.60/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.60/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.60/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.60/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.60/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.60/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.60/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.60/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.60/1.44  
% 2.76/1.45  tff(f_75, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.76/1.45  tff(f_61, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.76/1.45  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.76/1.45  tff(f_42, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.76/1.45  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.76/1.45  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.76/1.45  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.76/1.45  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.76/1.45  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.76/1.45  tff(c_60, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.45  tff(c_58, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.45  tff(c_40, plain, (![D_22, B_18]: (r2_hidden(D_22, k2_tarski(D_22, B_18)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.76/1.45  tff(c_30, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.45  tff(c_62, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.45  tff(c_26, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.76/1.45  tff(c_209, plain, (![A_57, B_58, C_59]: (r1_tarski(k4_xboole_0(A_57, B_58), C_59) | ~r1_tarski(A_57, k2_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.76/1.45  tff(c_28, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.45  tff(c_145, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.45  tff(c_157, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_145])).
% 2.76/1.45  tff(c_213, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, k2_xboole_0(B_58, k1_xboole_0)))), inference(resolution, [status(thm)], [c_209, c_157])).
% 2.76/1.45  tff(c_231, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k1_xboole_0 | ~r1_tarski(A_60, B_61))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_213])).
% 2.76/1.45  tff(c_245, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_231])).
% 2.76/1.45  tff(c_34, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.76/1.45  tff(c_363, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_245, c_34])).
% 2.76/1.45  tff(c_367, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_363])).
% 2.76/1.45  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.45  tff(c_669, plain, (![D_89]: (r2_hidden(D_89, k2_tarski('#skF_7', '#skF_8')) | ~r2_hidden(D_89, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_367, c_4])).
% 2.76/1.45  tff(c_36, plain, (![D_22, B_18, A_17]: (D_22=B_18 | D_22=A_17 | ~r2_hidden(D_22, k2_tarski(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.76/1.45  tff(c_684, plain, (![D_90]: (D_90='#skF_8' | D_90='#skF_7' | ~r2_hidden(D_90, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_669, c_36])).
% 2.76/1.45  tff(c_688, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_40, c_684])).
% 2.76/1.45  tff(c_696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_688])).
% 2.76/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.45  
% 2.76/1.45  Inference rules
% 2.76/1.45  ----------------------
% 2.76/1.45  #Ref     : 0
% 2.76/1.45  #Sup     : 146
% 2.76/1.45  #Fact    : 0
% 2.76/1.45  #Define  : 0
% 2.76/1.45  #Split   : 1
% 2.76/1.45  #Chain   : 0
% 2.76/1.45  #Close   : 0
% 2.76/1.45  
% 2.76/1.45  Ordering : KBO
% 2.76/1.45  
% 2.76/1.45  Simplification rules
% 2.76/1.45  ----------------------
% 2.76/1.45  #Subsume      : 2
% 2.76/1.45  #Demod        : 55
% 2.76/1.45  #Tautology    : 102
% 2.76/1.45  #SimpNegUnit  : 1
% 2.76/1.45  #BackRed      : 2
% 2.76/1.45  
% 2.76/1.45  #Partial instantiations: 0
% 2.76/1.45  #Strategies tried      : 1
% 2.76/1.45  
% 2.76/1.45  Timing (in seconds)
% 2.76/1.45  ----------------------
% 2.76/1.45  Preprocessing        : 0.30
% 2.76/1.45  Parsing              : 0.15
% 2.76/1.45  CNF conversion       : 0.03
% 2.76/1.45  Main loop            : 0.33
% 2.76/1.45  Inferencing          : 0.12
% 2.76/1.45  Reduction            : 0.11
% 2.76/1.45  Demodulation         : 0.08
% 2.76/1.45  BG Simplification    : 0.02
% 2.76/1.46  Subsumption          : 0.07
% 2.76/1.46  Abstraction          : 0.02
% 2.76/1.46  MUC search           : 0.00
% 2.76/1.46  Cooper               : 0.00
% 2.76/1.46  Total                : 0.66
% 2.76/1.46  Index Insertion      : 0.00
% 2.76/1.46  Index Deletion       : 0.00
% 2.76/1.46  Index Matching       : 0.00
% 2.76/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
