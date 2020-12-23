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
% DateTime   : Thu Dec  3 09:51:43 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 140 expanded)
%              Number of leaves         :   23 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :   42 ( 155 expanded)
%              Number of equality atoms :   37 ( 126 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(c_8,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_93,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_257,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(B_48,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_93])).

tff(c_16,plain,(
    ! [A_15,B_16] : k3_tarski(k2_tarski(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_318,plain,(
    ! [B_51,A_52] : k2_xboole_0(B_51,A_52) = k2_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_16])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | k2_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4])).

tff(c_74,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_20])).

tff(c_114,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_74])).

tff(c_128,plain,(
    ! [A_5] : k2_xboole_0('#skF_3',A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_92])).

tff(c_424,plain,(
    ! [B_53] : k2_xboole_0(B_53,'#skF_3') = B_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_128])).

tff(c_18,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),B_18) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_131,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),B_18) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_18])).

tff(c_440,plain,(
    ! [A_17] : k1_tarski(A_17) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_131])).

tff(c_129,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_39])).

tff(c_12,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_208,plain,(
    ! [A_42,B_43,C_44,D_45] : k2_xboole_0(k2_tarski(A_42,B_43),k2_tarski(C_44,D_45)) = k2_enumset1(A_42,B_43,C_44,D_45) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_231,plain,(
    ! [A_42,B_43] : k2_xboole_0(k2_tarski(A_42,B_43),'#skF_3') = k2_enumset1(A_42,B_43,'#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_208])).

tff(c_336,plain,(
    ! [A_42,B_43] : k2_xboole_0('#skF_3',k2_tarski(A_42,B_43)) = k2_enumset1(A_42,B_43,'#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_231])).

tff(c_537,plain,(
    ! [A_61,B_62] : k2_enumset1(A_61,B_62,'#skF_1','#skF_2') = k2_tarski(A_61,B_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_336])).

tff(c_14,plain,(
    ! [A_13,B_14] : k2_enumset1(A_13,A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_551,plain,(
    k2_tarski('#skF_1','#skF_2') = k2_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_14])).

tff(c_569,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_12,c_551])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:22:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.21  
% 2.09/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.21  %$ r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.09/1.21  
% 2.09/1.21  %Foreground sorts:
% 2.09/1.21  
% 2.09/1.21  
% 2.09/1.21  %Background operators:
% 2.09/1.21  
% 2.09/1.21  
% 2.09/1.21  %Foreground operators:
% 2.09/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.21  
% 2.22/1.22  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.22/1.22  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.22/1.22  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.22/1.22  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.22/1.22  tff(f_52, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.22/1.22  tff(f_33, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.22/1.22  tff(f_48, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.22/1.22  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.22/1.22  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.22/1.22  tff(f_43, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 2.22/1.22  tff(c_8, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.22  tff(c_93, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.22/1.22  tff(c_257, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(B_48, A_47))), inference(superposition, [status(thm), theory('equality')], [c_8, c_93])).
% 2.22/1.22  tff(c_16, plain, (![A_15, B_16]: (k3_tarski(k2_tarski(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.22/1.22  tff(c_318, plain, (![B_51, A_52]: (k2_xboole_0(B_51, A_52)=k2_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_257, c_16])).
% 2.22/1.22  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.22  tff(c_88, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.22  tff(c_92, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_88])).
% 2.22/1.22  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.22/1.22  tff(c_4, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | k2_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.22  tff(c_39, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20, c_4])).
% 2.22/1.22  tff(c_74, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_39, c_20])).
% 2.22/1.22  tff(c_114, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_74])).
% 2.22/1.22  tff(c_128, plain, (![A_5]: (k2_xboole_0('#skF_3', A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_92])).
% 2.22/1.22  tff(c_424, plain, (![B_53]: (k2_xboole_0(B_53, '#skF_3')=B_53)), inference(superposition, [status(thm), theory('equality')], [c_318, c_128])).
% 2.22/1.22  tff(c_18, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.22/1.22  tff(c_131, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), B_18)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_18])).
% 2.22/1.22  tff(c_440, plain, (![A_17]: (k1_tarski(A_17)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_424, c_131])).
% 2.22/1.22  tff(c_129, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_39])).
% 2.22/1.22  tff(c_12, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.22/1.22  tff(c_208, plain, (![A_42, B_43, C_44, D_45]: (k2_xboole_0(k2_tarski(A_42, B_43), k2_tarski(C_44, D_45))=k2_enumset1(A_42, B_43, C_44, D_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.22  tff(c_231, plain, (![A_42, B_43]: (k2_xboole_0(k2_tarski(A_42, B_43), '#skF_3')=k2_enumset1(A_42, B_43, '#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_208])).
% 2.22/1.22  tff(c_336, plain, (![A_42, B_43]: (k2_xboole_0('#skF_3', k2_tarski(A_42, B_43))=k2_enumset1(A_42, B_43, '#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_318, c_231])).
% 2.22/1.22  tff(c_537, plain, (![A_61, B_62]: (k2_enumset1(A_61, B_62, '#skF_1', '#skF_2')=k2_tarski(A_61, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_336])).
% 2.22/1.22  tff(c_14, plain, (![A_13, B_14]: (k2_enumset1(A_13, A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.22  tff(c_551, plain, (k2_tarski('#skF_1', '#skF_2')=k2_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_537, c_14])).
% 2.22/1.22  tff(c_569, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_12, c_551])).
% 2.22/1.22  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_440, c_569])).
% 2.22/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.22  
% 2.22/1.22  Inference rules
% 2.22/1.22  ----------------------
% 2.22/1.22  #Ref     : 0
% 2.22/1.22  #Sup     : 144
% 2.22/1.22  #Fact    : 0
% 2.22/1.22  #Define  : 0
% 2.22/1.22  #Split   : 1
% 2.22/1.22  #Chain   : 0
% 2.22/1.22  #Close   : 0
% 2.22/1.22  
% 2.22/1.22  Ordering : KBO
% 2.22/1.22  
% 2.22/1.22  Simplification rules
% 2.22/1.22  ----------------------
% 2.22/1.22  #Subsume      : 15
% 2.22/1.22  #Demod        : 39
% 2.22/1.22  #Tautology    : 85
% 2.22/1.22  #SimpNegUnit  : 1
% 2.22/1.22  #BackRed      : 8
% 2.22/1.22  
% 2.22/1.22  #Partial instantiations: 0
% 2.22/1.22  #Strategies tried      : 1
% 2.22/1.22  
% 2.22/1.22  Timing (in seconds)
% 2.22/1.22  ----------------------
% 2.22/1.22  Preprocessing        : 0.28
% 2.22/1.22  Parsing              : 0.15
% 2.22/1.22  CNF conversion       : 0.01
% 2.22/1.22  Main loop            : 0.25
% 2.22/1.22  Inferencing          : 0.09
% 2.22/1.22  Reduction            : 0.09
% 2.22/1.23  Demodulation         : 0.07
% 2.22/1.23  BG Simplification    : 0.01
% 2.22/1.23  Subsumption          : 0.03
% 2.22/1.23  Abstraction          : 0.02
% 2.22/1.23  MUC search           : 0.00
% 2.22/1.23  Cooper               : 0.00
% 2.22/1.23  Total                : 0.55
% 2.22/1.23  Index Insertion      : 0.00
% 2.22/1.23  Index Deletion       : 0.00
% 2.25/1.23  Index Matching       : 0.00
% 2.25/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
