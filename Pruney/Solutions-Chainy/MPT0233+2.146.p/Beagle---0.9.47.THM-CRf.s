%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:40 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   56 (  82 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 124 expanded)
%              Number of equality atoms :   34 (  67 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_14,plain,(
    ! [D_13,B_9] : r2_hidden(D_13,k2_tarski(D_13,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    ! [B_33,C_34] : r1_tarski(k2_tarski(B_33,C_34),k2_tarski(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_104,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    ! [B_33,C_34] : k4_xboole_0(k2_tarski(B_33,C_34),k2_tarski(B_33,C_34)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_104])).

tff(c_710,plain,(
    ! [A_110,C_111,B_112] :
      ( ~ r2_hidden(A_110,C_111)
      | k4_xboole_0(k2_tarski(A_110,B_112),C_111) != k1_tarski(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_713,plain,(
    ! [B_33,C_34] :
      ( ~ r2_hidden(B_33,k2_tarski(B_33,C_34))
      | k1_tarski(B_33) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_710])).

tff(c_721,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_713])).

tff(c_58,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_60,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_52,plain,(
    ! [B_33,C_34] : r1_tarski(k1_tarski(B_33),k2_tarski(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_140,plain,(
    ! [A_54,B_55] :
      ( k2_xboole_0(A_54,B_55) = B_55
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_465,plain,(
    ! [B_95,C_96] : k2_xboole_0(k1_tarski(B_95),k2_tarski(B_95,C_96)) = k2_tarski(B_95,C_96) ),
    inference(resolution,[status(thm)],[c_52,c_140])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_538,plain,(
    ! [B_103,C_104,C_105] :
      ( r1_tarski(k1_tarski(B_103),C_104)
      | ~ r1_tarski(k2_tarski(B_103,C_105),C_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_6])).

tff(c_555,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_60,c_538])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_568,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_555,c_4])).

tff(c_28,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_42,plain,(
    ! [B_30,C_31] :
      ( k4_xboole_0(k2_tarski(B_30,B_30),C_31) = k1_tarski(B_30)
      | r2_hidden(B_30,C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_61,plain,(
    ! [B_30,C_31] :
      ( k4_xboole_0(k1_tarski(B_30),C_31) = k1_tarski(B_30)
      | r2_hidden(B_30,C_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42])).

tff(c_572,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_61])).

tff(c_588,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_572])).

tff(c_10,plain,(
    ! [D_13,B_9,A_8] :
      ( D_13 = B_9
      | D_13 = A_8
      | ~ r2_hidden(D_13,k2_tarski(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_604,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_588,c_10])).

tff(c_608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_604])).

tff(c_609,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_572])).

tff(c_725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_721,c_609])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:36:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.38  
% 2.60/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.38  %$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.60/1.38  
% 2.60/1.38  %Foreground sorts:
% 2.60/1.38  
% 2.60/1.38  
% 2.60/1.38  %Background operators:
% 2.60/1.38  
% 2.60/1.38  
% 2.60/1.38  %Foreground operators:
% 2.60/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.60/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.60/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.60/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.60/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.60/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.60/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.60/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.60/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.60/1.39  
% 2.60/1.40  tff(f_46, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.60/1.40  tff(f_80, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.60/1.40  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.60/1.40  tff(f_65, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.60/1.40  tff(f_90, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.60/1.40  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.60/1.40  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.60/1.40  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.60/1.40  tff(c_14, plain, (![D_13, B_9]: (r2_hidden(D_13, k2_tarski(D_13, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.60/1.40  tff(c_48, plain, (![B_33, C_34]: (r1_tarski(k2_tarski(B_33, C_34), k2_tarski(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.40  tff(c_104, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.40  tff(c_126, plain, (![B_33, C_34]: (k4_xboole_0(k2_tarski(B_33, C_34), k2_tarski(B_33, C_34))=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_104])).
% 2.60/1.40  tff(c_710, plain, (![A_110, C_111, B_112]: (~r2_hidden(A_110, C_111) | k4_xboole_0(k2_tarski(A_110, B_112), C_111)!=k1_tarski(A_110))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.60/1.40  tff(c_713, plain, (![B_33, C_34]: (~r2_hidden(B_33, k2_tarski(B_33, C_34)) | k1_tarski(B_33)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_126, c_710])).
% 2.60/1.40  tff(c_721, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_713])).
% 2.60/1.40  tff(c_58, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.60/1.40  tff(c_56, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.60/1.40  tff(c_60, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.60/1.40  tff(c_52, plain, (![B_33, C_34]: (r1_tarski(k1_tarski(B_33), k2_tarski(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.40  tff(c_140, plain, (![A_54, B_55]: (k2_xboole_0(A_54, B_55)=B_55 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.60/1.40  tff(c_465, plain, (![B_95, C_96]: (k2_xboole_0(k1_tarski(B_95), k2_tarski(B_95, C_96))=k2_tarski(B_95, C_96))), inference(resolution, [status(thm)], [c_52, c_140])).
% 2.60/1.40  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.40  tff(c_538, plain, (![B_103, C_104, C_105]: (r1_tarski(k1_tarski(B_103), C_104) | ~r1_tarski(k2_tarski(B_103, C_105), C_104))), inference(superposition, [status(thm), theory('equality')], [c_465, c_6])).
% 2.60/1.40  tff(c_555, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_538])).
% 2.60/1.40  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.40  tff(c_568, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_555, c_4])).
% 2.60/1.40  tff(c_28, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.60/1.40  tff(c_42, plain, (![B_30, C_31]: (k4_xboole_0(k2_tarski(B_30, B_30), C_31)=k1_tarski(B_30) | r2_hidden(B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.60/1.40  tff(c_61, plain, (![B_30, C_31]: (k4_xboole_0(k1_tarski(B_30), C_31)=k1_tarski(B_30) | r2_hidden(B_30, C_31))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42])).
% 2.60/1.40  tff(c_572, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_568, c_61])).
% 2.60/1.40  tff(c_588, plain, (r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_572])).
% 2.60/1.40  tff(c_10, plain, (![D_13, B_9, A_8]: (D_13=B_9 | D_13=A_8 | ~r2_hidden(D_13, k2_tarski(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.60/1.40  tff(c_604, plain, ('#skF_6'='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_588, c_10])).
% 2.60/1.40  tff(c_608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_604])).
% 2.60/1.40  tff(c_609, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_572])).
% 2.60/1.40  tff(c_725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_721, c_609])).
% 2.60/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.40  
% 2.60/1.40  Inference rules
% 2.60/1.40  ----------------------
% 2.60/1.40  #Ref     : 0
% 2.60/1.40  #Sup     : 162
% 2.60/1.40  #Fact    : 0
% 2.60/1.40  #Define  : 0
% 2.60/1.40  #Split   : 1
% 2.60/1.40  #Chain   : 0
% 2.60/1.40  #Close   : 0
% 2.60/1.40  
% 2.60/1.40  Ordering : KBO
% 2.60/1.40  
% 2.60/1.40  Simplification rules
% 2.60/1.40  ----------------------
% 2.60/1.40  #Subsume      : 5
% 2.60/1.40  #Demod        : 72
% 2.60/1.40  #Tautology    : 100
% 2.60/1.40  #SimpNegUnit  : 2
% 2.60/1.40  #BackRed      : 3
% 2.60/1.40  
% 2.60/1.40  #Partial instantiations: 0
% 2.60/1.40  #Strategies tried      : 1
% 2.60/1.40  
% 2.60/1.40  Timing (in seconds)
% 2.60/1.40  ----------------------
% 2.60/1.40  Preprocessing        : 0.32
% 2.60/1.40  Parsing              : 0.16
% 2.60/1.40  CNF conversion       : 0.02
% 2.60/1.40  Main loop            : 0.30
% 2.60/1.40  Inferencing          : 0.11
% 2.60/1.40  Reduction            : 0.10
% 2.60/1.40  Demodulation         : 0.07
% 2.60/1.40  BG Simplification    : 0.02
% 2.60/1.40  Subsumption          : 0.06
% 2.60/1.40  Abstraction          : 0.01
% 2.60/1.40  MUC search           : 0.00
% 2.60/1.40  Cooper               : 0.00
% 2.60/1.40  Total                : 0.65
% 2.60/1.40  Index Insertion      : 0.00
% 2.60/1.40  Index Deletion       : 0.00
% 2.60/1.40  Index Matching       : 0.00
% 2.60/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
