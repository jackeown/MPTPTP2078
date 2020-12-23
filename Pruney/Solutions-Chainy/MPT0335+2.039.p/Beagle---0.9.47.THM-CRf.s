%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:58 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 (  78 expanded)
%              Number of equality atoms :   32 (  52 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_24,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_45,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_60,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_28])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_105,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_97])).

tff(c_489,plain,(
    ! [A_57,B_58,C_59] : k3_xboole_0(k3_xboole_0(A_57,B_58),C_59) = k3_xboole_0(A_57,k3_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_572,plain,(
    ! [C_59] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_59)) = k3_xboole_0('#skF_1',C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_489])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_163,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_169,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,k3_xboole_0(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_10])).

tff(c_251,plain,(
    ! [A_48,B_49] : k3_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_169])).

tff(c_290,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_251])).

tff(c_1382,plain,(
    ! [B_75,A_76,B_77] : k3_xboole_0(B_75,k3_xboole_0(A_76,B_77)) = k3_xboole_0(A_76,k3_xboole_0(B_77,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_489])).

tff(c_1793,plain,(
    ! [B_78] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_78)) = k3_xboole_0(B_78,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_1382])).

tff(c_1860,plain,(
    ! [A_1] : k3_xboole_0(k3_xboole_0(A_1,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_1793])).

tff(c_3175,plain,(
    ! [A_91] : k3_xboole_0(k3_xboole_0(A_91,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',A_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_1860])).

tff(c_3247,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_3175])).

tff(c_143,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(k1_tarski(A_39),B_40) = B_40
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(resolution,[status(thm)],[c_12,c_97])).

tff(c_149,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(k1_tarski(A_39),B_40) = k1_tarski(A_39)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_104])).

tff(c_3299,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3247,c_149])).

tff(c_3339,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3299])).

tff(c_3341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_3339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.84  
% 4.61/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.85  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.61/1.85  
% 4.61/1.85  %Foreground sorts:
% 4.61/1.85  
% 4.61/1.85  
% 4.61/1.85  %Background operators:
% 4.61/1.85  
% 4.61/1.85  
% 4.61/1.85  %Foreground operators:
% 4.61/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.61/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.61/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.61/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.61/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.61/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.61/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.61/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.61/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.61/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.61/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.61/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.61/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.61/1.85  
% 4.61/1.86  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 4.61/1.86  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.61/1.86  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.61/1.86  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.61/1.86  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.61/1.86  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.61/1.86  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 4.61/1.86  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.61/1.86  tff(c_24, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.61/1.86  tff(c_26, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.61/1.86  tff(c_45, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.61/1.86  tff(c_28, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.61/1.86  tff(c_60, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_45, c_28])).
% 4.61/1.86  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.61/1.86  tff(c_97, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.61/1.86  tff(c_105, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_30, c_97])).
% 4.61/1.86  tff(c_489, plain, (![A_57, B_58, C_59]: (k3_xboole_0(k3_xboole_0(A_57, B_58), C_59)=k3_xboole_0(A_57, k3_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.61/1.86  tff(c_572, plain, (![C_59]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_59))=k3_xboole_0('#skF_1', C_59))), inference(superposition, [status(thm), theory('equality')], [c_105, c_489])).
% 4.61/1.86  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.61/1.86  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.61/1.86  tff(c_163, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.61/1.86  tff(c_169, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, k3_xboole_0(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_10])).
% 4.61/1.86  tff(c_251, plain, (![A_48, B_49]: (k3_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_169])).
% 4.61/1.86  tff(c_290, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_251])).
% 4.61/1.86  tff(c_1382, plain, (![B_75, A_76, B_77]: (k3_xboole_0(B_75, k3_xboole_0(A_76, B_77))=k3_xboole_0(A_76, k3_xboole_0(B_77, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_489])).
% 4.61/1.86  tff(c_1793, plain, (![B_78]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_78))=k3_xboole_0(B_78, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_1382])).
% 4.61/1.86  tff(c_1860, plain, (![A_1]: (k3_xboole_0(k3_xboole_0(A_1, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', A_1)))), inference(superposition, [status(thm), theory('equality')], [c_290, c_1793])).
% 4.61/1.86  tff(c_3175, plain, (![A_91]: (k3_xboole_0(k3_xboole_0(A_91, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', A_91))), inference(demodulation, [status(thm), theory('equality')], [c_572, c_1860])).
% 4.61/1.86  tff(c_3247, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_60, c_3175])).
% 4.61/1.86  tff(c_143, plain, (![A_39, B_40]: (k2_xboole_0(k1_tarski(A_39), B_40)=B_40 | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.61/1.86  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.61/1.86  tff(c_104, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(resolution, [status(thm)], [c_12, c_97])).
% 4.61/1.86  tff(c_149, plain, (![A_39, B_40]: (k3_xboole_0(k1_tarski(A_39), B_40)=k1_tarski(A_39) | ~r2_hidden(A_39, B_40))), inference(superposition, [status(thm), theory('equality')], [c_143, c_104])).
% 4.61/1.86  tff(c_3299, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3247, c_149])).
% 4.61/1.86  tff(c_3339, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3299])).
% 4.61/1.86  tff(c_3341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_3339])).
% 4.61/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.86  
% 4.61/1.86  Inference rules
% 4.61/1.86  ----------------------
% 4.61/1.86  #Ref     : 0
% 4.61/1.86  #Sup     : 827
% 4.61/1.86  #Fact    : 0
% 4.61/1.86  #Define  : 0
% 4.61/1.86  #Split   : 0
% 4.61/1.86  #Chain   : 0
% 4.61/1.86  #Close   : 0
% 4.61/1.86  
% 4.61/1.86  Ordering : KBO
% 4.61/1.86  
% 4.61/1.86  Simplification rules
% 4.61/1.86  ----------------------
% 4.61/1.86  #Subsume      : 28
% 4.61/1.86  #Demod        : 782
% 4.61/1.86  #Tautology    : 446
% 4.61/1.86  #SimpNegUnit  : 1
% 4.61/1.86  #BackRed      : 1
% 4.61/1.86  
% 4.61/1.86  #Partial instantiations: 0
% 4.61/1.86  #Strategies tried      : 1
% 4.61/1.86  
% 4.61/1.86  Timing (in seconds)
% 4.61/1.86  ----------------------
% 4.61/1.86  Preprocessing        : 0.29
% 4.61/1.86  Parsing              : 0.16
% 4.61/1.86  CNF conversion       : 0.02
% 4.61/1.86  Main loop            : 0.82
% 4.61/1.86  Inferencing          : 0.25
% 4.61/1.86  Reduction            : 0.41
% 4.61/1.86  Demodulation         : 0.36
% 4.61/1.86  BG Simplification    : 0.03
% 4.61/1.86  Subsumption          : 0.10
% 4.61/1.86  Abstraction          : 0.04
% 4.61/1.86  MUC search           : 0.00
% 4.61/1.86  Cooper               : 0.00
% 4.61/1.86  Total                : 1.13
% 4.61/1.86  Index Insertion      : 0.00
% 4.61/1.86  Index Deletion       : 0.00
% 4.61/1.86  Index Matching       : 0.00
% 4.61/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
