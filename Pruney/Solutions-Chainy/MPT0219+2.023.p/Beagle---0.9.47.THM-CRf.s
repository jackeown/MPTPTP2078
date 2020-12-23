%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:53 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   61 (  78 expanded)
%              Number of leaves         :   35 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :   46 (  66 expanded)
%              Number of equality atoms :   34 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_84,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,(
    ! [C_31] : r2_hidden(C_31,k1_tarski(C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_86,plain,(
    k2_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_123,plain,(
    ! [B_64,A_65] : k5_xboole_0(B_64,A_65) = k5_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_139,plain,(
    ! [A_65] : k5_xboole_0(k1_xboole_0,A_65) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_26])).

tff(c_475,plain,(
    ! [A_104,B_105,C_106] : k5_xboole_0(k5_xboole_0(A_104,B_105),C_106) = k5_xboole_0(A_104,k5_xboole_0(B_105,C_106)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_561,plain,(
    ! [A_17,C_106] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_106)) = k5_xboole_0(k1_xboole_0,C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_475])).

tff(c_575,plain,(
    ! [A_107,C_108] : k5_xboole_0(A_107,k5_xboole_0(A_107,C_108)) = C_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_561])).

tff(c_990,plain,(
    ! [A_124,B_125] : k5_xboole_0(A_124,k2_xboole_0(A_124,B_125)) = k4_xboole_0(B_125,A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_575])).

tff(c_1026,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_7')) = k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_990])).

tff(c_1035,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1026])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_340,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_356,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_340])).

tff(c_1045,plain,(
    ! [B_126,A_127] : k5_xboole_0(B_126,k4_xboole_0(B_126,A_127)) = k3_xboole_0(A_127,B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_575])).

tff(c_1081,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k5_xboole_0(k1_tarski('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_1045])).

tff(c_1107,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1081])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( r2_hidden(D_10,A_5)
      | ~ r2_hidden(D_10,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1484,plain,(
    ! [D_140] :
      ( r2_hidden(D_140,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_140,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1107,c_10])).

tff(c_58,plain,(
    ! [C_31,A_27] :
      ( C_31 = A_27
      | ~ r2_hidden(C_31,k1_tarski(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1519,plain,(
    ! [D_142] :
      ( D_142 = '#skF_7'
      | ~ r2_hidden(D_142,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1484,c_58])).

tff(c_1523,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_60,c_1519])).

tff(c_1527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:34:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.48  
% 3.15/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.48  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 3.15/1.48  
% 3.15/1.48  %Foreground sorts:
% 3.15/1.48  
% 3.15/1.48  
% 3.15/1.48  %Background operators:
% 3.15/1.48  
% 3.15/1.48  
% 3.15/1.48  %Foreground operators:
% 3.15/1.48  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.15/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.15/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.15/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.15/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.15/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.15/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.15/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.48  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.15/1.48  
% 3.15/1.49  tff(f_89, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 3.15/1.49  tff(f_70, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.15/1.49  tff(f_42, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.15/1.49  tff(f_46, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.15/1.49  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.15/1.49  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.15/1.49  tff(f_44, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.15/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.49  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.15/1.49  tff(f_38, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.15/1.49  tff(c_84, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.15/1.49  tff(c_60, plain, (![C_31]: (r2_hidden(C_31, k1_tarski(C_31)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.15/1.49  tff(c_26, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.15/1.49  tff(c_30, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.15/1.49  tff(c_86, plain, (k2_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.15/1.49  tff(c_32, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.15/1.49  tff(c_123, plain, (![B_64, A_65]: (k5_xboole_0(B_64, A_65)=k5_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.15/1.49  tff(c_139, plain, (![A_65]: (k5_xboole_0(k1_xboole_0, A_65)=A_65)), inference(superposition, [status(thm), theory('equality')], [c_123, c_26])).
% 3.15/1.49  tff(c_475, plain, (![A_104, B_105, C_106]: (k5_xboole_0(k5_xboole_0(A_104, B_105), C_106)=k5_xboole_0(A_104, k5_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.15/1.49  tff(c_561, plain, (![A_17, C_106]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_106))=k5_xboole_0(k1_xboole_0, C_106))), inference(superposition, [status(thm), theory('equality')], [c_30, c_475])).
% 3.15/1.49  tff(c_575, plain, (![A_107, C_108]: (k5_xboole_0(A_107, k5_xboole_0(A_107, C_108))=C_108)), inference(demodulation, [status(thm), theory('equality')], [c_139, c_561])).
% 3.15/1.49  tff(c_990, plain, (![A_124, B_125]: (k5_xboole_0(A_124, k2_xboole_0(A_124, B_125))=k4_xboole_0(B_125, A_124))), inference(superposition, [status(thm), theory('equality')], [c_32, c_575])).
% 3.15/1.49  tff(c_1026, plain, (k5_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_7'))=k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_990])).
% 3.15/1.49  tff(c_1035, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1026])).
% 3.15/1.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.49  tff(c_340, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.15/1.49  tff(c_356, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_340])).
% 3.15/1.49  tff(c_1045, plain, (![B_126, A_127]: (k5_xboole_0(B_126, k4_xboole_0(B_126, A_127))=k3_xboole_0(A_127, B_126))), inference(superposition, [status(thm), theory('equality')], [c_356, c_575])).
% 3.15/1.49  tff(c_1081, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k5_xboole_0(k1_tarski('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1035, c_1045])).
% 3.15/1.49  tff(c_1107, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1081])).
% 3.15/1.49  tff(c_10, plain, (![D_10, A_5, B_6]: (r2_hidden(D_10, A_5) | ~r2_hidden(D_10, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.15/1.49  tff(c_1484, plain, (![D_140]: (r2_hidden(D_140, k1_tarski('#skF_7')) | ~r2_hidden(D_140, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1107, c_10])).
% 3.15/1.49  tff(c_58, plain, (![C_31, A_27]: (C_31=A_27 | ~r2_hidden(C_31, k1_tarski(A_27)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.15/1.49  tff(c_1519, plain, (![D_142]: (D_142='#skF_7' | ~r2_hidden(D_142, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_1484, c_58])).
% 3.15/1.49  tff(c_1523, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_60, c_1519])).
% 3.15/1.49  tff(c_1527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1523])).
% 3.15/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.49  
% 3.15/1.49  Inference rules
% 3.15/1.49  ----------------------
% 3.15/1.49  #Ref     : 0
% 3.15/1.49  #Sup     : 359
% 3.15/1.49  #Fact    : 0
% 3.15/1.49  #Define  : 0
% 3.15/1.49  #Split   : 0
% 3.15/1.49  #Chain   : 0
% 3.15/1.49  #Close   : 0
% 3.15/1.49  
% 3.15/1.49  Ordering : KBO
% 3.15/1.49  
% 3.15/1.49  Simplification rules
% 3.15/1.49  ----------------------
% 3.15/1.49  #Subsume      : 18
% 3.15/1.49  #Demod        : 150
% 3.15/1.49  #Tautology    : 229
% 3.15/1.49  #SimpNegUnit  : 1
% 3.15/1.49  #BackRed      : 0
% 3.15/1.49  
% 3.15/1.49  #Partial instantiations: 0
% 3.15/1.49  #Strategies tried      : 1
% 3.15/1.49  
% 3.15/1.49  Timing (in seconds)
% 3.15/1.49  ----------------------
% 3.15/1.49  Preprocessing        : 0.33
% 3.15/1.49  Parsing              : 0.16
% 3.15/1.49  CNF conversion       : 0.03
% 3.15/1.49  Main loop            : 0.40
% 3.15/1.49  Inferencing          : 0.13
% 3.15/1.49  Reduction            : 0.16
% 3.15/1.50  Demodulation         : 0.13
% 3.15/1.50  BG Simplification    : 0.03
% 3.15/1.50  Subsumption          : 0.06
% 3.15/1.50  Abstraction          : 0.02
% 3.15/1.50  MUC search           : 0.00
% 3.15/1.50  Cooper               : 0.00
% 3.15/1.50  Total                : 0.76
% 3.15/1.50  Index Insertion      : 0.00
% 3.15/1.50  Index Deletion       : 0.00
% 3.15/1.50  Index Matching       : 0.00
% 3.15/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
