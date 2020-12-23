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
% DateTime   : Thu Dec  3 09:54:55 EST 2020

% Result     : Theorem 22.95s
% Output     : CNFRefutation 22.95s
% Verified   : 
% Statistics : Number of formulae       :   55 (  69 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 (  71 expanded)
%              Number of equality atoms :   35 (  53 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_38,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(k1_tarski(A_33),B_34) = B_34
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_74,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_74])).

tff(c_44,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_227,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_255,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_227])).

tff(c_1437,plain,(
    ! [A_93,B_94,C_95] : k2_xboole_0(k3_xboole_0(A_93,B_94),k3_xboole_0(A_93,C_95)) = k3_xboole_0(A_93,k2_xboole_0(B_94,C_95)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16088,plain,(
    ! [B_248,B_249,A_250] : k2_xboole_0(k3_xboole_0(B_248,B_249),k3_xboole_0(A_250,B_248)) = k3_xboole_0(B_248,k2_xboole_0(B_249,A_250)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1437])).

tff(c_19755,plain,(
    ! [A_269] : k2_xboole_0(k1_tarski('#skF_4'),k3_xboole_0(A_269,'#skF_2')) = k3_xboole_0('#skF_2',k2_xboole_0('#skF_3',A_269)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_16088])).

tff(c_19848,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_1')) = k2_xboole_0(k1_tarski('#skF_4'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_19755])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] : k3_xboole_0(k3_xboole_0(A_5,B_6),C_7) = k3_xboole_0(A_5,k3_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_686,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_692,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k4_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,k3_xboole_0(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_686,c_26])).

tff(c_733,plain,(
    ! [A_67,B_68] : k3_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_692])).

tff(c_20248,plain,(
    ! [A_273,B_274,C_275] : k2_xboole_0(k3_xboole_0(A_273,B_274),k3_xboole_0(B_274,C_275)) = k3_xboole_0(B_274,k2_xboole_0(A_273,C_275)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1437])).

tff(c_20504,plain,(
    ! [A_67,B_68,C_275] : k2_xboole_0(k3_xboole_0(A_67,B_68),k3_xboole_0(k3_xboole_0(A_67,B_68),C_275)) = k3_xboole_0(k3_xboole_0(A_67,B_68),k2_xboole_0(A_67,C_275)) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_20248])).

tff(c_20665,plain,(
    ! [A_67,B_68,C_275] : k3_xboole_0(A_67,k3_xboole_0(B_68,k2_xboole_0(A_67,C_275))) = k3_xboole_0(A_67,B_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14,c_20504])).

tff(c_77742,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0(k1_tarski('#skF_4'),'#skF_1')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_19848,c_20665])).

tff(c_78009,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0(k1_tarski('#skF_4'),'#skF_1')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_77742])).

tff(c_91508,plain,
    ( k3_xboole_0('#skF_3','#skF_1') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_78009])).

tff(c_91577,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2,c_91508])).

tff(c_91579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_91577])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.36  % Computer   : n008.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 12:47:00 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.95/15.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.95/15.54  
% 22.95/15.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.95/15.54  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 22.95/15.54  
% 22.95/15.54  %Foreground sorts:
% 22.95/15.54  
% 22.95/15.54  
% 22.95/15.54  %Background operators:
% 22.95/15.54  
% 22.95/15.54  
% 22.95/15.54  %Foreground operators:
% 22.95/15.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.95/15.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.95/15.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.95/15.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.95/15.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.95/15.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 22.95/15.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.95/15.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 22.95/15.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.95/15.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 22.95/15.54  tff('#skF_2', type, '#skF_2': $i).
% 22.95/15.54  tff('#skF_3', type, '#skF_3': $i).
% 22.95/15.54  tff('#skF_1', type, '#skF_1': $i).
% 22.95/15.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.95/15.54  tff('#skF_4', type, '#skF_4': $i).
% 22.95/15.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.95/15.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.95/15.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.95/15.54  
% 22.95/15.55  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 22.95/15.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 22.95/15.55  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 22.95/15.55  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 22.95/15.55  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 22.95/15.55  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 22.95/15.55  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 22.95/15.55  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 22.95/15.55  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 22.95/15.55  tff(c_38, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.95/15.55  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.95/15.55  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.95/15.55  tff(c_36, plain, (![A_33, B_34]: (k2_xboole_0(k1_tarski(A_33), B_34)=B_34 | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_65])).
% 22.95/15.55  tff(c_42, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.95/15.55  tff(c_74, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.95/15.55  tff(c_113, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_42, c_74])).
% 22.95/15.55  tff(c_44, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.95/15.55  tff(c_227, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.95/15.55  tff(c_255, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_44, c_227])).
% 22.95/15.55  tff(c_1437, plain, (![A_93, B_94, C_95]: (k2_xboole_0(k3_xboole_0(A_93, B_94), k3_xboole_0(A_93, C_95))=k3_xboole_0(A_93, k2_xboole_0(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.95/15.55  tff(c_16088, plain, (![B_248, B_249, A_250]: (k2_xboole_0(k3_xboole_0(B_248, B_249), k3_xboole_0(A_250, B_248))=k3_xboole_0(B_248, k2_xboole_0(B_249, A_250)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1437])).
% 22.95/15.55  tff(c_19755, plain, (![A_269]: (k2_xboole_0(k1_tarski('#skF_4'), k3_xboole_0(A_269, '#skF_2'))=k3_xboole_0('#skF_2', k2_xboole_0('#skF_3', A_269)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_16088])).
% 22.95/15.55  tff(c_19848, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0(k1_tarski('#skF_4'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_255, c_19755])).
% 22.95/15.55  tff(c_10, plain, (![A_5, B_6, C_7]: (k3_xboole_0(k3_xboole_0(A_5, B_6), C_7)=k3_xboole_0(A_5, k3_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.95/15.55  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k3_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 22.95/15.55  tff(c_26, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 22.95/15.55  tff(c_686, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_51])).
% 22.95/15.55  tff(c_692, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k4_xboole_0(A_67, B_68))=k3_xboole_0(A_67, k3_xboole_0(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_686, c_26])).
% 22.95/15.55  tff(c_733, plain, (![A_67, B_68]: (k3_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_692])).
% 22.95/15.55  tff(c_20248, plain, (![A_273, B_274, C_275]: (k2_xboole_0(k3_xboole_0(A_273, B_274), k3_xboole_0(B_274, C_275))=k3_xboole_0(B_274, k2_xboole_0(A_273, C_275)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1437])).
% 22.95/15.55  tff(c_20504, plain, (![A_67, B_68, C_275]: (k2_xboole_0(k3_xboole_0(A_67, B_68), k3_xboole_0(k3_xboole_0(A_67, B_68), C_275))=k3_xboole_0(k3_xboole_0(A_67, B_68), k2_xboole_0(A_67, C_275)))), inference(superposition, [status(thm), theory('equality')], [c_733, c_20248])).
% 22.95/15.55  tff(c_20665, plain, (![A_67, B_68, C_275]: (k3_xboole_0(A_67, k3_xboole_0(B_68, k2_xboole_0(A_67, C_275)))=k3_xboole_0(A_67, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14, c_20504])).
% 22.95/15.55  tff(c_77742, plain, (k3_xboole_0('#skF_3', k2_xboole_0(k1_tarski('#skF_4'), '#skF_1'))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_19848, c_20665])).
% 22.95/15.55  tff(c_78009, plain, (k3_xboole_0('#skF_3', k2_xboole_0(k1_tarski('#skF_4'), '#skF_1'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_77742])).
% 22.95/15.55  tff(c_91508, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_78009])).
% 22.95/15.55  tff(c_91577, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2, c_91508])).
% 22.95/15.55  tff(c_91579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_91577])).
% 22.95/15.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.95/15.55  
% 22.95/15.55  Inference rules
% 22.95/15.55  ----------------------
% 22.95/15.55  #Ref     : 0
% 22.95/15.55  #Sup     : 23008
% 22.95/15.55  #Fact    : 0
% 22.95/15.55  #Define  : 0
% 22.95/15.55  #Split   : 4
% 22.95/15.55  #Chain   : 0
% 22.95/15.55  #Close   : 0
% 22.95/15.55  
% 22.95/15.55  Ordering : KBO
% 22.95/15.55  
% 22.95/15.55  Simplification rules
% 22.95/15.55  ----------------------
% 22.95/15.55  #Subsume      : 430
% 22.95/15.55  #Demod        : 26099
% 22.95/15.55  #Tautology    : 14929
% 22.95/15.55  #SimpNegUnit  : 8
% 22.95/15.55  #BackRed      : 8
% 22.95/15.55  
% 22.95/15.55  #Partial instantiations: 0
% 22.95/15.55  #Strategies tried      : 1
% 22.95/15.55  
% 22.95/15.55  Timing (in seconds)
% 22.95/15.55  ----------------------
% 22.95/15.56  Preprocessing        : 0.32
% 22.95/15.56  Parsing              : 0.17
% 22.95/15.56  CNF conversion       : 0.02
% 22.95/15.56  Main loop            : 14.44
% 22.95/15.56  Inferencing          : 1.48
% 22.95/15.56  Reduction            : 9.74
% 22.95/15.56  Demodulation         : 8.95
% 22.95/15.56  BG Simplification    : 0.18
% 22.95/15.56  Subsumption          : 2.49
% 22.95/15.56  Abstraction          : 0.27
% 22.95/15.56  MUC search           : 0.00
% 22.95/15.56  Cooper               : 0.00
% 22.95/15.56  Total                : 14.79
% 22.95/15.56  Index Insertion      : 0.00
% 22.95/15.56  Index Deletion       : 0.00
% 22.95/15.56  Index Matching       : 0.00
% 22.95/15.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
