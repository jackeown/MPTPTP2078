%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:58 EST 2020

% Result     : Theorem 12.74s
% Output     : CNFRefutation 12.74s
% Verified   : 
% Statistics : Number of formulae       :   61 (  88 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 ( 102 expanded)
%              Number of equality atoms :   39 (  69 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_30,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1183,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_tarski(k2_tarski(A_75,B_76),C_77)
      | ~ r2_hidden(B_76,C_77)
      | ~ r2_hidden(A_75,C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4980,plain,(
    ! [A_117,C_118] :
      ( r1_tarski(k1_tarski(A_117),C_118)
      | ~ r2_hidden(A_117,C_118)
      | ~ r2_hidden(A_117,C_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1183])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4989,plain,(
    ! [A_119,C_120] :
      ( k4_xboole_0(k1_tarski(A_119),C_120) = k1_xboole_0
      | ~ r2_hidden(A_119,C_120) ) ),
    inference(resolution,[status(thm)],[c_4980,c_6])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5027,plain,(
    ! [A_119,C_120] :
      ( k4_xboole_0(k1_tarski(A_119),k1_xboole_0) = k3_xboole_0(k1_tarski(A_119),C_120)
      | ~ r2_hidden(A_119,C_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4989,c_14])).

tff(c_24441,plain,(
    ! [A_214,C_215] :
      ( k3_xboole_0(k1_tarski(A_214),C_215) = k1_tarski(A_214)
      | ~ r2_hidden(A_214,C_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_5027])).

tff(c_59,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_74,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_34])).

tff(c_36,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_112,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_112])).

tff(c_134,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_149,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_134])).

tff(c_155,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_149])).

tff(c_434,plain,(
    ! [A_56,B_57,C_58] : k3_xboole_0(k3_xboole_0(A_56,B_57),C_58) = k3_xboole_0(A_56,k3_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_490,plain,(
    ! [C_58] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_58)) = k3_xboole_0('#skF_1',C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_434])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_209,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_215,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,k3_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_14])).

tff(c_358,plain,(
    ! [A_54,B_55] : k3_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = k3_xboole_0(A_54,B_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_215])).

tff(c_400,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_358])).

tff(c_2927,plain,(
    ! [C_106,A_107,B_108] : k3_xboole_0(C_106,k3_xboole_0(A_107,B_108)) = k3_xboole_0(A_107,k3_xboole_0(B_108,C_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_2])).

tff(c_3575,plain,(
    ! [C_109] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_109)) = k3_xboole_0(C_109,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_2927])).

tff(c_3681,plain,(
    ! [A_1] : k3_xboole_0(k3_xboole_0(A_1,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_3575])).

tff(c_5322,plain,(
    ! [A_123] : k3_xboole_0(k3_xboole_0(A_123,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',A_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_3681])).

tff(c_5409,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_5322])).

tff(c_24647,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24441,c_5409])).

tff(c_24898,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24647])).

tff(c_24900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24898])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.74/5.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.74/5.84  
% 12.74/5.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.74/5.84  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.74/5.84  
% 12.74/5.84  %Foreground sorts:
% 12.74/5.84  
% 12.74/5.84  
% 12.74/5.84  %Background operators:
% 12.74/5.84  
% 12.74/5.84  
% 12.74/5.84  %Foreground operators:
% 12.74/5.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.74/5.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.74/5.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.74/5.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.74/5.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.74/5.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.74/5.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.74/5.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.74/5.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.74/5.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.74/5.84  tff('#skF_2', type, '#skF_2': $i).
% 12.74/5.84  tff('#skF_3', type, '#skF_3': $i).
% 12.74/5.84  tff('#skF_1', type, '#skF_1': $i).
% 12.74/5.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.74/5.84  tff('#skF_4', type, '#skF_4': $i).
% 12.74/5.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.74/5.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.74/5.84  
% 12.74/5.85  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 12.74/5.85  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.74/5.85  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 12.74/5.85  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 12.74/5.85  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.74/5.85  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.74/5.85  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.74/5.85  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 12.74/5.85  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 12.74/5.85  tff(c_30, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.74/5.85  tff(c_32, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.74/5.85  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.74/5.85  tff(c_16, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.74/5.85  tff(c_1183, plain, (![A_75, B_76, C_77]: (r1_tarski(k2_tarski(A_75, B_76), C_77) | ~r2_hidden(B_76, C_77) | ~r2_hidden(A_75, C_77))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.74/5.85  tff(c_4980, plain, (![A_117, C_118]: (r1_tarski(k1_tarski(A_117), C_118) | ~r2_hidden(A_117, C_118) | ~r2_hidden(A_117, C_118))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1183])).
% 12.74/5.85  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.74/5.85  tff(c_4989, plain, (![A_119, C_120]: (k4_xboole_0(k1_tarski(A_119), C_120)=k1_xboole_0 | ~r2_hidden(A_119, C_120))), inference(resolution, [status(thm)], [c_4980, c_6])).
% 12.74/5.85  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.74/5.85  tff(c_5027, plain, (![A_119, C_120]: (k4_xboole_0(k1_tarski(A_119), k1_xboole_0)=k3_xboole_0(k1_tarski(A_119), C_120) | ~r2_hidden(A_119, C_120))), inference(superposition, [status(thm), theory('equality')], [c_4989, c_14])).
% 12.74/5.85  tff(c_24441, plain, (![A_214, C_215]: (k3_xboole_0(k1_tarski(A_214), C_215)=k1_tarski(A_214) | ~r2_hidden(A_214, C_215))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_5027])).
% 12.74/5.85  tff(c_59, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.74/5.85  tff(c_34, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.74/5.85  tff(c_74, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_59, c_34])).
% 12.74/5.85  tff(c_36, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.74/5.85  tff(c_112, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.74/5.85  tff(c_120, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_112])).
% 12.74/5.85  tff(c_134, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.74/5.85  tff(c_149, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_120, c_134])).
% 12.74/5.85  tff(c_155, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_149])).
% 12.74/5.85  tff(c_434, plain, (![A_56, B_57, C_58]: (k3_xboole_0(k3_xboole_0(A_56, B_57), C_58)=k3_xboole_0(A_56, k3_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.74/5.85  tff(c_490, plain, (![C_58]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_58))=k3_xboole_0('#skF_1', C_58))), inference(superposition, [status(thm), theory('equality')], [c_155, c_434])).
% 12.74/5.85  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.74/5.85  tff(c_209, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.74/5.85  tff(c_215, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, k3_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_209, c_14])).
% 12.74/5.85  tff(c_358, plain, (![A_54, B_55]: (k3_xboole_0(A_54, k3_xboole_0(A_54, B_55))=k3_xboole_0(A_54, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_215])).
% 12.74/5.85  tff(c_400, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_358])).
% 12.74/5.85  tff(c_2927, plain, (![C_106, A_107, B_108]: (k3_xboole_0(C_106, k3_xboole_0(A_107, B_108))=k3_xboole_0(A_107, k3_xboole_0(B_108, C_106)))), inference(superposition, [status(thm), theory('equality')], [c_434, c_2])).
% 12.74/5.85  tff(c_3575, plain, (![C_109]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_109))=k3_xboole_0(C_109, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_2927])).
% 12.74/5.85  tff(c_3681, plain, (![A_1]: (k3_xboole_0(k3_xboole_0(A_1, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', A_1)))), inference(superposition, [status(thm), theory('equality')], [c_400, c_3575])).
% 12.74/5.85  tff(c_5322, plain, (![A_123]: (k3_xboole_0(k3_xboole_0(A_123, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', A_123))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_3681])).
% 12.74/5.85  tff(c_5409, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_74, c_5322])).
% 12.74/5.85  tff(c_24647, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24441, c_5409])).
% 12.74/5.85  tff(c_24898, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24647])).
% 12.74/5.85  tff(c_24900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24898])).
% 12.74/5.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.74/5.85  
% 12.74/5.85  Inference rules
% 12.74/5.85  ----------------------
% 12.74/5.85  #Ref     : 0
% 12.74/5.85  #Sup     : 5979
% 12.74/5.85  #Fact    : 0
% 12.74/5.85  #Define  : 0
% 12.74/5.85  #Split   : 2
% 12.74/5.85  #Chain   : 0
% 12.74/5.85  #Close   : 0
% 12.74/5.85  
% 12.74/5.85  Ordering : KBO
% 12.74/5.85  
% 12.74/5.85  Simplification rules
% 12.74/5.85  ----------------------
% 12.74/5.85  #Subsume      : 383
% 12.74/5.85  #Demod        : 9359
% 12.74/5.85  #Tautology    : 3140
% 12.74/5.85  #SimpNegUnit  : 7
% 12.74/5.85  #BackRed      : 4
% 12.74/5.85  
% 12.74/5.85  #Partial instantiations: 0
% 12.74/5.85  #Strategies tried      : 1
% 12.74/5.85  
% 12.74/5.85  Timing (in seconds)
% 12.74/5.85  ----------------------
% 12.86/5.85  Preprocessing        : 0.30
% 12.86/5.86  Parsing              : 0.17
% 12.86/5.86  CNF conversion       : 0.02
% 12.86/5.86  Main loop            : 4.80
% 12.87/5.86  Inferencing          : 0.68
% 12.87/5.86  Reduction            : 3.36
% 12.87/5.86  Demodulation         : 3.12
% 12.87/5.86  BG Simplification    : 0.10
% 12.87/5.86  Subsumption          : 0.50
% 12.87/5.86  Abstraction          : 0.15
% 12.87/5.86  MUC search           : 0.00
% 12.87/5.86  Cooper               : 0.00
% 12.87/5.86  Total                : 5.13
% 12.87/5.86  Index Insertion      : 0.00
% 12.87/5.86  Index Deletion       : 0.00
% 12.87/5.86  Index Matching       : 0.00
% 12.87/5.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
