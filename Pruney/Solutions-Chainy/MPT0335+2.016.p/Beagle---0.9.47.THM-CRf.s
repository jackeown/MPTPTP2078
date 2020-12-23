%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:55 EST 2020

% Result     : Theorem 13.03s
% Output     : CNFRefutation 13.03s
% Verified   : 
% Statistics : Number of formulae       :   50 (  65 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 (  72 expanded)
%              Number of equality atoms :   28 (  46 expanded)
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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_38,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_111,plain,(
    ! [B_44,A_45] : k3_xboole_0(B_44,A_45) = k3_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_153,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_111])).

tff(c_44,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_211,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_241,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_211])).

tff(c_1081,plain,(
    ! [A_89,B_90,C_91] : k3_xboole_0(k3_xboole_0(A_89,B_90),C_91) = k3_xboole_0(A_89,k3_xboole_0(B_90,C_91)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1164,plain,(
    ! [C_91] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_91)) = k3_xboole_0('#skF_1',C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_1081])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_238,plain,(
    ! [A_11,B_12] : k3_xboole_0(k3_xboole_0(A_11,B_12),A_11) = k3_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_14,c_211])).

tff(c_1100,plain,(
    ! [C_91,B_90] : k3_xboole_0(C_91,k3_xboole_0(B_90,C_91)) = k3_xboole_0(C_91,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_238])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_7384,plain,(
    ! [C_212,A_213,B_214] : k3_xboole_0(C_212,k3_xboole_0(A_213,B_214)) = k3_xboole_0(A_213,k3_xboole_0(B_214,C_212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_2])).

tff(c_8123,plain,(
    ! [C_215] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_215)) = k3_xboole_0(C_215,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_7384])).

tff(c_8258,plain,(
    ! [B_90] : k3_xboole_0(k3_xboole_0(B_90,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1100,c_8123])).

tff(c_17256,plain,(
    ! [B_265] : k3_xboole_0(k3_xboole_0(B_265,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',B_265) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1164,c_8258])).

tff(c_17449,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_17256])).

tff(c_553,plain,(
    ! [A_65,B_66] :
      ( k2_xboole_0(k1_tarski(A_65),B_66) = B_66
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_565,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(k1_tarski(A_65),B_66) = k1_tarski(A_65)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_18])).

tff(c_17587,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_17449,c_565])).

tff(c_17680,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_17587])).

tff(c_17682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_17680])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.03/5.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.03/5.58  
% 13.03/5.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.03/5.59  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.03/5.59  
% 13.03/5.59  %Foreground sorts:
% 13.03/5.59  
% 13.03/5.59  
% 13.03/5.59  %Background operators:
% 13.03/5.59  
% 13.03/5.59  
% 13.03/5.59  %Foreground operators:
% 13.03/5.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.03/5.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.03/5.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.03/5.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.03/5.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.03/5.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.03/5.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.03/5.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.03/5.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.03/5.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.03/5.59  tff('#skF_2', type, '#skF_2': $i).
% 13.03/5.59  tff('#skF_3', type, '#skF_3': $i).
% 13.03/5.59  tff('#skF_1', type, '#skF_1': $i).
% 13.03/5.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.03/5.59  tff('#skF_4', type, '#skF_4': $i).
% 13.03/5.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.03/5.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.03/5.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.03/5.59  
% 13.03/5.60  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 13.03/5.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.03/5.60  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.03/5.60  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 13.03/5.60  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.03/5.60  tff(f_67, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 13.03/5.60  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 13.03/5.60  tff(c_38, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.03/5.60  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.03/5.60  tff(c_42, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.03/5.60  tff(c_111, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=k3_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.03/5.60  tff(c_153, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_42, c_111])).
% 13.03/5.60  tff(c_44, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.03/5.60  tff(c_211, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.03/5.60  tff(c_241, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_44, c_211])).
% 13.03/5.60  tff(c_1081, plain, (![A_89, B_90, C_91]: (k3_xboole_0(k3_xboole_0(A_89, B_90), C_91)=k3_xboole_0(A_89, k3_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.03/5.60  tff(c_1164, plain, (![C_91]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_91))=k3_xboole_0('#skF_1', C_91))), inference(superposition, [status(thm), theory('equality')], [c_241, c_1081])).
% 13.03/5.60  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.03/5.60  tff(c_238, plain, (![A_11, B_12]: (k3_xboole_0(k3_xboole_0(A_11, B_12), A_11)=k3_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_14, c_211])).
% 13.03/5.60  tff(c_1100, plain, (![C_91, B_90]: (k3_xboole_0(C_91, k3_xboole_0(B_90, C_91))=k3_xboole_0(C_91, B_90))), inference(superposition, [status(thm), theory('equality')], [c_1081, c_238])).
% 13.03/5.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.03/5.60  tff(c_7384, plain, (![C_212, A_213, B_214]: (k3_xboole_0(C_212, k3_xboole_0(A_213, B_214))=k3_xboole_0(A_213, k3_xboole_0(B_214, C_212)))), inference(superposition, [status(thm), theory('equality')], [c_1081, c_2])).
% 13.03/5.60  tff(c_8123, plain, (![C_215]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_215))=k3_xboole_0(C_215, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_7384])).
% 13.03/5.60  tff(c_8258, plain, (![B_90]: (k3_xboole_0(k3_xboole_0(B_90, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_90)))), inference(superposition, [status(thm), theory('equality')], [c_1100, c_8123])).
% 13.03/5.60  tff(c_17256, plain, (![B_265]: (k3_xboole_0(k3_xboole_0(B_265, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', B_265))), inference(demodulation, [status(thm), theory('equality')], [c_1164, c_8258])).
% 13.03/5.60  tff(c_17449, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_153, c_17256])).
% 13.03/5.60  tff(c_553, plain, (![A_65, B_66]: (k2_xboole_0(k1_tarski(A_65), B_66)=B_66 | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.03/5.60  tff(c_18, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k2_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.03/5.60  tff(c_565, plain, (![A_65, B_66]: (k3_xboole_0(k1_tarski(A_65), B_66)=k1_tarski(A_65) | ~r2_hidden(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_553, c_18])).
% 13.03/5.60  tff(c_17587, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17449, c_565])).
% 13.03/5.60  tff(c_17680, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_17587])).
% 13.03/5.60  tff(c_17682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_17680])).
% 13.03/5.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.03/5.60  
% 13.03/5.60  Inference rules
% 13.03/5.60  ----------------------
% 13.03/5.60  #Ref     : 0
% 13.03/5.60  #Sup     : 4275
% 13.03/5.60  #Fact    : 0
% 13.03/5.60  #Define  : 0
% 13.03/5.60  #Split   : 3
% 13.03/5.60  #Chain   : 0
% 13.03/5.60  #Close   : 0
% 13.03/5.60  
% 13.03/5.60  Ordering : KBO
% 13.03/5.60  
% 13.03/5.60  Simplification rules
% 13.03/5.60  ----------------------
% 13.03/5.60  #Subsume      : 111
% 13.03/5.60  #Demod        : 4757
% 13.03/5.60  #Tautology    : 2709
% 13.03/5.60  #SimpNegUnit  : 3
% 13.03/5.60  #BackRed      : 5
% 13.03/5.60  
% 13.03/5.60  #Partial instantiations: 0
% 13.03/5.60  #Strategies tried      : 1
% 13.03/5.60  
% 13.03/5.60  Timing (in seconds)
% 13.03/5.60  ----------------------
% 13.03/5.61  Preprocessing        : 0.50
% 13.03/5.61  Parsing              : 0.26
% 13.03/5.61  CNF conversion       : 0.03
% 13.03/5.61  Main loop            : 4.21
% 13.03/5.61  Inferencing          : 0.82
% 13.03/5.61  Reduction            : 2.47
% 13.03/5.61  Demodulation         : 2.17
% 13.03/5.61  BG Simplification    : 0.12
% 13.03/5.61  Subsumption          : 0.61
% 13.03/5.61  Abstraction          : 0.13
% 13.03/5.61  MUC search           : 0.00
% 13.03/5.61  Cooper               : 0.00
% 13.03/5.61  Total                : 4.74
% 13.03/5.61  Index Insertion      : 0.00
% 13.03/5.61  Index Deletion       : 0.00
% 13.03/5.61  Index Matching       : 0.00
% 13.03/5.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
