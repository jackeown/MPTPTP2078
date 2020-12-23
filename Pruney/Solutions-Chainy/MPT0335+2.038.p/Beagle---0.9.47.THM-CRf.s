%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:58 EST 2020

% Result     : Theorem 5.49s
% Output     : CNFRefutation 5.49s
% Verified   : 
% Statistics : Number of formulae       :   51 (  59 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 (  64 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_26,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_172,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(k1_tarski(A_41),B_42) = B_42
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_108])).

tff(c_260,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(k1_tarski(A_52),B_53) = k1_xboole_0
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_115])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_274,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(k1_tarski(A_52),k1_xboole_0) = k3_xboole_0(k1_tarski(A_52),B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_12])).

tff(c_4426,plain,(
    ! [A_102,B_103] :
      ( k3_xboole_0(k1_tarski(A_102),B_103) = k1_tarski(A_102)
      | ~ r2_hidden(A_102,B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_274])).

tff(c_4629,plain,(
    ! [A_104,A_105] :
      ( k3_xboole_0(A_104,k1_tarski(A_105)) = k1_tarski(A_105)
      | ~ r2_hidden(A_105,A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4426])).

tff(c_30,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_116,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_108])).

tff(c_142,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_160,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_142])).

tff(c_167,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_160])).

tff(c_320,plain,(
    ! [A_55,B_56,C_57] : k3_xboole_0(k3_xboole_0(A_55,B_56),C_57) = k3_xboole_0(A_55,k3_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_474,plain,(
    ! [C_60] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_60)) = k3_xboole_0('#skF_1',C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_320])).

tff(c_498,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_474])).

tff(c_4715,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4629,c_498])).

tff(c_4798,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4715])).

tff(c_4800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4798])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:24:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.49/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.49/2.18  
% 5.49/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.49/2.19  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.49/2.19  
% 5.49/2.19  %Foreground sorts:
% 5.49/2.19  
% 5.49/2.19  
% 5.49/2.19  %Background operators:
% 5.49/2.19  
% 5.49/2.19  
% 5.49/2.19  %Foreground operators:
% 5.49/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.49/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.49/2.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.49/2.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.49/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.49/2.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.49/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.49/2.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.49/2.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.49/2.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.49/2.19  tff('#skF_2', type, '#skF_2': $i).
% 5.49/2.19  tff('#skF_3', type, '#skF_3': $i).
% 5.49/2.19  tff('#skF_1', type, '#skF_1': $i).
% 5.49/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.49/2.19  tff('#skF_4', type, '#skF_4': $i).
% 5.49/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.49/2.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.49/2.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.49/2.19  
% 5.49/2.20  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 5.49/2.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.49/2.20  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.49/2.20  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 5.49/2.20  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.49/2.20  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.49/2.20  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.49/2.20  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 5.49/2.20  tff(c_26, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.49/2.20  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.49/2.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.49/2.20  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.49/2.20  tff(c_172, plain, (![A_41, B_42]: (k2_xboole_0(k1_tarski(A_41), B_42)=B_42 | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.49/2.20  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.49/2.20  tff(c_108, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.49/2.20  tff(c_115, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_108])).
% 5.49/2.20  tff(c_260, plain, (![A_52, B_53]: (k4_xboole_0(k1_tarski(A_52), B_53)=k1_xboole_0 | ~r2_hidden(A_52, B_53))), inference(superposition, [status(thm), theory('equality')], [c_172, c_115])).
% 5.49/2.20  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.49/2.20  tff(c_274, plain, (![A_52, B_53]: (k4_xboole_0(k1_tarski(A_52), k1_xboole_0)=k3_xboole_0(k1_tarski(A_52), B_53) | ~r2_hidden(A_52, B_53))), inference(superposition, [status(thm), theory('equality')], [c_260, c_12])).
% 5.49/2.20  tff(c_4426, plain, (![A_102, B_103]: (k3_xboole_0(k1_tarski(A_102), B_103)=k1_tarski(A_102) | ~r2_hidden(A_102, B_103))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_274])).
% 5.49/2.20  tff(c_4629, plain, (![A_104, A_105]: (k3_xboole_0(A_104, k1_tarski(A_105))=k1_tarski(A_105) | ~r2_hidden(A_105, A_104))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4426])).
% 5.49/2.20  tff(c_30, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.49/2.20  tff(c_32, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.49/2.20  tff(c_116, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_108])).
% 5.49/2.20  tff(c_142, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.49/2.20  tff(c_160, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_116, c_142])).
% 5.49/2.20  tff(c_167, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_160])).
% 5.49/2.20  tff(c_320, plain, (![A_55, B_56, C_57]: (k3_xboole_0(k3_xboole_0(A_55, B_56), C_57)=k3_xboole_0(A_55, k3_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.49/2.20  tff(c_474, plain, (![C_60]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_60))=k3_xboole_0('#skF_1', C_60))), inference(superposition, [status(thm), theory('equality')], [c_167, c_320])).
% 5.49/2.20  tff(c_498, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_474])).
% 5.49/2.20  tff(c_4715, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4629, c_498])).
% 5.49/2.20  tff(c_4798, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4715])).
% 5.49/2.20  tff(c_4800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_4798])).
% 5.49/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.49/2.20  
% 5.49/2.20  Inference rules
% 5.49/2.20  ----------------------
% 5.49/2.20  #Ref     : 0
% 5.49/2.20  #Sup     : 1144
% 5.49/2.20  #Fact    : 0
% 5.49/2.20  #Define  : 0
% 5.49/2.20  #Split   : 0
% 5.49/2.20  #Chain   : 0
% 5.49/2.20  #Close   : 0
% 5.49/2.20  
% 5.49/2.20  Ordering : KBO
% 5.49/2.20  
% 5.49/2.20  Simplification rules
% 5.49/2.20  ----------------------
% 5.49/2.20  #Subsume      : 90
% 5.49/2.20  #Demod        : 1647
% 5.49/2.20  #Tautology    : 518
% 5.49/2.20  #SimpNegUnit  : 1
% 5.49/2.20  #BackRed      : 1
% 5.49/2.20  
% 5.49/2.20  #Partial instantiations: 0
% 5.49/2.20  #Strategies tried      : 1
% 5.49/2.20  
% 5.49/2.20  Timing (in seconds)
% 5.49/2.20  ----------------------
% 5.49/2.20  Preprocessing        : 0.31
% 5.49/2.20  Parsing              : 0.17
% 5.49/2.20  CNF conversion       : 0.02
% 5.49/2.20  Main loop            : 1.10
% 5.49/2.20  Inferencing          : 0.27
% 5.49/2.20  Reduction            : 0.64
% 5.49/2.20  Demodulation         : 0.57
% 5.49/2.20  BG Simplification    : 0.04
% 5.49/2.20  Subsumption          : 0.11
% 5.49/2.20  Abstraction          : 0.06
% 5.49/2.20  MUC search           : 0.00
% 5.49/2.20  Cooper               : 0.00
% 5.49/2.20  Total                : 1.44
% 5.49/2.20  Index Insertion      : 0.00
% 5.49/2.20  Index Deletion       : 0.00
% 5.49/2.20  Index Matching       : 0.00
% 5.49/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
