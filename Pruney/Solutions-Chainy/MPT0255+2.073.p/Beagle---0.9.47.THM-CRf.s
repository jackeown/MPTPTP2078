%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:48 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 104 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 ( 169 expanded)
%              Number of equality atoms :   29 (  78 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(c_271,plain,(
    ! [A_48,B_49] : k2_xboole_0(k1_tarski(A_48),k1_tarski(B_49)) = k2_tarski(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38,plain,(
    ! [A_23,B_24] : k2_xboole_0(k1_tarski(A_23),B_24) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_291,plain,(
    ! [A_48,B_49] : k2_tarski(A_48,B_49) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_38])).

tff(c_70,plain,(
    ! [B_31,A_32] : k2_xboole_0(B_31,A_32) = k2_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_100,plain,(
    ! [A_32] : k2_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_767,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden('#skF_1'(A_103,B_104,C_105),B_104)
      | r2_hidden('#skF_1'(A_103,B_104,C_105),A_103)
      | r2_hidden('#skF_2'(A_103,B_104,C_105),C_105)
      | k2_xboole_0(A_103,B_104) = C_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3173,plain,(
    ! [A_152,B_153] :
      ( r2_hidden('#skF_1'(A_152,B_153,B_153),A_152)
      | r2_hidden('#skF_2'(A_152,B_153,B_153),B_153)
      | k2_xboole_0(A_152,B_153) = B_153 ) ),
    inference(resolution,[status(thm)],[c_767,c_18])).

tff(c_1441,plain,(
    ! [A_114,B_115,C_116] :
      ( r2_hidden('#skF_1'(A_114,B_115,C_116),B_115)
      | r2_hidden('#skF_1'(A_114,B_115,C_116),A_114)
      | ~ r2_hidden('#skF_2'(A_114,B_115,C_116),B_115)
      | k2_xboole_0(A_114,B_115) = C_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1541,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_1'(A_114,B_115,B_115),A_114)
      | ~ r2_hidden('#skF_2'(A_114,B_115,B_115),B_115)
      | k2_xboole_0(A_114,B_115) = B_115 ) ),
    inference(resolution,[status(thm)],[c_1441,c_10])).

tff(c_3274,plain,(
    ! [A_154,B_155] :
      ( r2_hidden('#skF_1'(A_154,B_155,B_155),A_154)
      | k2_xboole_0(A_154,B_155) = B_155 ) ),
    inference(resolution,[status(thm)],[c_3173,c_1541])).

tff(c_353,plain,(
    ! [B_60,A_61] : k2_xboole_0(k1_tarski(B_60),k1_tarski(A_61)) = k2_tarski(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_2])).

tff(c_28,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_362,plain,(
    ! [B_60,A_61] : k2_tarski(B_60,A_61) = k2_tarski(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_28])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_328,plain,(
    ! [D_57,A_58,B_59] :
      ( ~ r2_hidden(D_57,A_58)
      | r2_hidden(D_57,k2_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_349,plain,(
    ! [D_57] :
      ( ~ r2_hidden(D_57,k2_tarski('#skF_3','#skF_4'))
      | r2_hidden(D_57,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_328])).

tff(c_490,plain,(
    ! [D_57] :
      ( ~ r2_hidden(D_57,k2_tarski('#skF_4','#skF_3'))
      | r2_hidden(D_57,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_349])).

tff(c_3393,plain,(
    ! [B_158] :
      ( r2_hidden('#skF_1'(k2_tarski('#skF_4','#skF_3'),B_158,B_158),k1_xboole_0)
      | k2_xboole_0(k2_tarski('#skF_4','#skF_3'),B_158) = B_158 ) ),
    inference(resolution,[status(thm)],[c_3274,c_490])).

tff(c_3396,plain,
    ( ~ r2_hidden('#skF_2'(k2_tarski('#skF_4','#skF_3'),k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k2_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3393,c_10])).

tff(c_3407,plain,
    ( ~ r2_hidden('#skF_2'(k2_tarski('#skF_4','#skF_3'),k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k2_tarski('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2,c_3396])).

tff(c_3408,plain,(
    ~ r2_hidden('#skF_2'(k2_tarski('#skF_4','#skF_3'),k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_3407])).

tff(c_3400,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_4','#skF_3'),k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k2_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3393,c_18])).

tff(c_3410,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_4','#skF_3'),k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k2_tarski('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2,c_3400])).

tff(c_3411,plain,(
    r2_hidden('#skF_2'(k2_tarski('#skF_4','#skF_3'),k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_3410])).

tff(c_3417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3408,c_3411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.87  
% 4.45/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.87  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 4.45/1.87  
% 4.45/1.87  %Foreground sorts:
% 4.45/1.87  
% 4.45/1.87  
% 4.45/1.87  %Background operators:
% 4.45/1.87  
% 4.45/1.87  
% 4.45/1.87  %Foreground operators:
% 4.45/1.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.45/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.45/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.45/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.45/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.45/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.45/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.45/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.45/1.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.45/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.87  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.45/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.45/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.45/1.87  
% 4.45/1.88  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 4.45/1.88  tff(f_57, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.45/1.88  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.45/1.88  tff(f_42, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.45/1.88  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.45/1.88  tff(f_61, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 4.45/1.88  tff(c_271, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), k1_tarski(B_49))=k2_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.45/1.88  tff(c_38, plain, (![A_23, B_24]: (k2_xboole_0(k1_tarski(A_23), B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.45/1.88  tff(c_291, plain, (![A_48, B_49]: (k2_tarski(A_48, B_49)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_271, c_38])).
% 4.45/1.88  tff(c_70, plain, (![B_31, A_32]: (k2_xboole_0(B_31, A_32)=k2_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/1.88  tff(c_24, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.45/1.88  tff(c_100, plain, (![A_32]: (k2_xboole_0(k1_xboole_0, A_32)=A_32)), inference(superposition, [status(thm), theory('equality')], [c_70, c_24])).
% 4.45/1.88  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/1.88  tff(c_767, plain, (![A_103, B_104, C_105]: (r2_hidden('#skF_1'(A_103, B_104, C_105), B_104) | r2_hidden('#skF_1'(A_103, B_104, C_105), A_103) | r2_hidden('#skF_2'(A_103, B_104, C_105), C_105) | k2_xboole_0(A_103, B_104)=C_105)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.45/1.88  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.45/1.88  tff(c_3173, plain, (![A_152, B_153]: (r2_hidden('#skF_1'(A_152, B_153, B_153), A_152) | r2_hidden('#skF_2'(A_152, B_153, B_153), B_153) | k2_xboole_0(A_152, B_153)=B_153)), inference(resolution, [status(thm)], [c_767, c_18])).
% 4.45/1.88  tff(c_1441, plain, (![A_114, B_115, C_116]: (r2_hidden('#skF_1'(A_114, B_115, C_116), B_115) | r2_hidden('#skF_1'(A_114, B_115, C_116), A_114) | ~r2_hidden('#skF_2'(A_114, B_115, C_116), B_115) | k2_xboole_0(A_114, B_115)=C_116)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.45/1.88  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.45/1.88  tff(c_1541, plain, (![A_114, B_115]: (r2_hidden('#skF_1'(A_114, B_115, B_115), A_114) | ~r2_hidden('#skF_2'(A_114, B_115, B_115), B_115) | k2_xboole_0(A_114, B_115)=B_115)), inference(resolution, [status(thm)], [c_1441, c_10])).
% 4.45/1.88  tff(c_3274, plain, (![A_154, B_155]: (r2_hidden('#skF_1'(A_154, B_155, B_155), A_154) | k2_xboole_0(A_154, B_155)=B_155)), inference(resolution, [status(thm)], [c_3173, c_1541])).
% 4.45/1.88  tff(c_353, plain, (![B_60, A_61]: (k2_xboole_0(k1_tarski(B_60), k1_tarski(A_61))=k2_tarski(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_271, c_2])).
% 4.45/1.88  tff(c_28, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.45/1.88  tff(c_362, plain, (![B_60, A_61]: (k2_tarski(B_60, A_61)=k2_tarski(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_353, c_28])).
% 4.45/1.88  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.45/1.88  tff(c_328, plain, (![D_57, A_58, B_59]: (~r2_hidden(D_57, A_58) | r2_hidden(D_57, k2_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.45/1.88  tff(c_349, plain, (![D_57]: (~r2_hidden(D_57, k2_tarski('#skF_3', '#skF_4')) | r2_hidden(D_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_328])).
% 4.45/1.88  tff(c_490, plain, (![D_57]: (~r2_hidden(D_57, k2_tarski('#skF_4', '#skF_3')) | r2_hidden(D_57, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_362, c_349])).
% 4.45/1.88  tff(c_3393, plain, (![B_158]: (r2_hidden('#skF_1'(k2_tarski('#skF_4', '#skF_3'), B_158, B_158), k1_xboole_0) | k2_xboole_0(k2_tarski('#skF_4', '#skF_3'), B_158)=B_158)), inference(resolution, [status(thm)], [c_3274, c_490])).
% 4.45/1.88  tff(c_3396, plain, (~r2_hidden('#skF_2'(k2_tarski('#skF_4', '#skF_3'), k1_xboole_0, k1_xboole_0), k1_xboole_0) | k2_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_3393, c_10])).
% 4.45/1.88  tff(c_3407, plain, (~r2_hidden('#skF_2'(k2_tarski('#skF_4', '#skF_3'), k1_xboole_0, k1_xboole_0), k1_xboole_0) | k2_tarski('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2, c_3396])).
% 4.45/1.88  tff(c_3408, plain, (~r2_hidden('#skF_2'(k2_tarski('#skF_4', '#skF_3'), k1_xboole_0, k1_xboole_0), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_291, c_3407])).
% 4.45/1.88  tff(c_3400, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_4', '#skF_3'), k1_xboole_0, k1_xboole_0), k1_xboole_0) | k2_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_3393, c_18])).
% 4.45/1.88  tff(c_3410, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_4', '#skF_3'), k1_xboole_0, k1_xboole_0), k1_xboole_0) | k2_tarski('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2, c_3400])).
% 4.45/1.88  tff(c_3411, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_4', '#skF_3'), k1_xboole_0, k1_xboole_0), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_291, c_3410])).
% 4.45/1.88  tff(c_3417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3408, c_3411])).
% 4.45/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.88  
% 4.45/1.88  Inference rules
% 4.45/1.88  ----------------------
% 4.45/1.88  #Ref     : 0
% 4.45/1.88  #Sup     : 695
% 4.45/1.88  #Fact    : 10
% 4.45/1.88  #Define  : 0
% 4.45/1.88  #Split   : 5
% 4.45/1.88  #Chain   : 0
% 4.45/1.88  #Close   : 0
% 4.45/1.88  
% 4.45/1.88  Ordering : KBO
% 4.45/1.88  
% 4.45/1.88  Simplification rules
% 4.45/1.88  ----------------------
% 4.45/1.88  #Subsume      : 121
% 4.45/1.88  #Demod        : 324
% 4.45/1.88  #Tautology    : 280
% 4.45/1.88  #SimpNegUnit  : 30
% 4.45/1.88  #BackRed      : 32
% 4.45/1.88  
% 4.45/1.88  #Partial instantiations: 0
% 4.45/1.88  #Strategies tried      : 1
% 4.45/1.88  
% 4.45/1.88  Timing (in seconds)
% 4.45/1.88  ----------------------
% 4.45/1.89  Preprocessing        : 0.32
% 4.45/1.89  Parsing              : 0.17
% 4.45/1.89  CNF conversion       : 0.02
% 4.45/1.89  Main loop            : 0.76
% 4.45/1.89  Inferencing          : 0.25
% 4.45/1.89  Reduction            : 0.27
% 4.45/1.89  Demodulation         : 0.21
% 4.45/1.89  BG Simplification    : 0.03
% 4.45/1.89  Subsumption          : 0.15
% 4.45/1.89  Abstraction          : 0.04
% 4.45/1.89  MUC search           : 0.00
% 4.45/1.89  Cooper               : 0.00
% 4.45/1.89  Total                : 1.11
% 4.45/1.89  Index Insertion      : 0.00
% 4.45/1.89  Index Deletion       : 0.00
% 4.45/1.89  Index Matching       : 0.00
% 4.45/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
