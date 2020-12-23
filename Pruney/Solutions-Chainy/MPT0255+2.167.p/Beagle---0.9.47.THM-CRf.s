%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:59 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   68 (1722 expanded)
%              Number of leaves         :   31 ( 595 expanded)
%              Depth                    :   19
%              Number of atoms          :   61 (2416 expanded)
%              Number of equality atoms :   31 ( 853 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_86,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_54,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_129,plain,(
    ! [A_77,B_78] :
      ( ~ v1_xboole_0(k2_xboole_0(A_77,B_78))
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_132,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_129])).

tff(c_137,plain,(
    v1_xboole_0(k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_132])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_141,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_8])).

tff(c_143,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_54])).

tff(c_158,plain,(
    ! [B_79,A_80] :
      ( ~ v1_xboole_0(k2_xboole_0(B_79,A_80))
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_161,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_158])).

tff(c_166,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_161])).

tff(c_171,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_166,c_8])).

tff(c_52,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_178,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_171,c_52])).

tff(c_173,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_141])).

tff(c_233,plain,(
    ! [A_86,B_87] : k3_tarski(k2_tarski(A_86,B_87)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_242,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k3_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_233])).

tff(c_248,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_242])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( ~ v1_xboole_0(k2_xboole_0(A_6,B_7))
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_274,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_10])).

tff(c_280,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_274])).

tff(c_174,plain,(
    ! [A_5] :
      ( A_5 = '#skF_3'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_8])).

tff(c_289,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_280,c_174])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_175,plain,(
    ! [A_12] : k4_xboole_0('#skF_3',A_12) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_171,c_16])).

tff(c_299,plain,(
    ! [A_12] : k4_xboole_0('#skF_1',A_12) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_289,c_175])).

tff(c_32,plain,(
    ! [A_38] : k2_tarski(A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( ~ v1_xboole_0(k2_xboole_0(B_9,A_8))
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_271,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_12])).

tff(c_278,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_271])).

tff(c_285,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_278,c_174])).

tff(c_292,plain,(
    k2_tarski('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_173])).

tff(c_367,plain,(
    k1_tarski('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_32,c_289,c_292])).

tff(c_48,plain,(
    ! [B_69] : k4_xboole_0(k1_tarski(B_69),k1_tarski(B_69)) != k1_tarski(B_69) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_377,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_1') != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_48])).

tff(c_382,plain,(
    k4_xboole_0('#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_367,c_377])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.27  
% 2.23/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.27  %$ v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.23/1.27  
% 2.23/1.27  %Foreground sorts:
% 2.23/1.27  
% 2.23/1.27  
% 2.23/1.27  %Background operators:
% 2.23/1.27  
% 2.23/1.27  
% 2.23/1.27  %Foreground operators:
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.27  
% 2.23/1.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.23/1.28  tff(f_90, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.23/1.28  tff(f_40, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_xboole_0)).
% 2.23/1.28  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.23/1.28  tff(f_46, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.23/1.28  tff(f_86, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.23/1.28  tff(f_80, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.23/1.28  tff(f_50, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.23/1.28  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.23/1.28  tff(f_85, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.23/1.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.23/1.28  tff(c_54, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.23/1.28  tff(c_129, plain, (![A_77, B_78]: (~v1_xboole_0(k2_xboole_0(A_77, B_78)) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.28  tff(c_132, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_129])).
% 2.23/1.28  tff(c_137, plain, (v1_xboole_0(k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_132])).
% 2.23/1.28  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.28  tff(c_141, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_137, c_8])).
% 2.23/1.28  tff(c_143, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_141, c_54])).
% 2.23/1.28  tff(c_158, plain, (![B_79, A_80]: (~v1_xboole_0(k2_xboole_0(B_79, A_80)) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.23/1.28  tff(c_161, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_143, c_158])).
% 2.23/1.28  tff(c_166, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_161])).
% 2.23/1.28  tff(c_171, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_166, c_8])).
% 2.23/1.28  tff(c_52, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.28  tff(c_178, plain, (k3_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_171, c_52])).
% 2.23/1.28  tff(c_173, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_141])).
% 2.23/1.28  tff(c_233, plain, (![A_86, B_87]: (k3_tarski(k2_tarski(A_86, B_87))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.23/1.28  tff(c_242, plain, (k2_xboole_0('#skF_1', '#skF_2')=k3_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_173, c_233])).
% 2.23/1.28  tff(c_248, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_242])).
% 2.23/1.28  tff(c_10, plain, (![A_6, B_7]: (~v1_xboole_0(k2_xboole_0(A_6, B_7)) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.28  tff(c_274, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_248, c_10])).
% 2.23/1.28  tff(c_280, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_274])).
% 2.23/1.28  tff(c_174, plain, (![A_5]: (A_5='#skF_3' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_8])).
% 2.23/1.28  tff(c_289, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_280, c_174])).
% 2.23/1.28  tff(c_16, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.23/1.28  tff(c_175, plain, (![A_12]: (k4_xboole_0('#skF_3', A_12)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_171, c_16])).
% 2.23/1.28  tff(c_299, plain, (![A_12]: (k4_xboole_0('#skF_1', A_12)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_289, c_175])).
% 2.23/1.28  tff(c_32, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.23/1.28  tff(c_12, plain, (![B_9, A_8]: (~v1_xboole_0(k2_xboole_0(B_9, A_8)) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.23/1.28  tff(c_271, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_248, c_12])).
% 2.23/1.28  tff(c_278, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_271])).
% 2.23/1.28  tff(c_285, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_278, c_174])).
% 2.23/1.28  tff(c_292, plain, (k2_tarski('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_285, c_173])).
% 2.23/1.28  tff(c_367, plain, (k1_tarski('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_289, c_32, c_289, c_292])).
% 2.23/1.28  tff(c_48, plain, (![B_69]: (k4_xboole_0(k1_tarski(B_69), k1_tarski(B_69))!=k1_tarski(B_69))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.23/1.28  tff(c_377, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_1')!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_367, c_48])).
% 2.23/1.28  tff(c_382, plain, (k4_xboole_0('#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_367, c_367, c_377])).
% 2.23/1.28  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_299, c_382])).
% 2.23/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  Inference rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Ref     : 0
% 2.23/1.28  #Sup     : 86
% 2.23/1.28  #Fact    : 0
% 2.23/1.28  #Define  : 0
% 2.23/1.28  #Split   : 0
% 2.23/1.28  #Chain   : 0
% 2.23/1.28  #Close   : 0
% 2.23/1.28  
% 2.23/1.28  Ordering : KBO
% 2.23/1.28  
% 2.23/1.28  Simplification rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Subsume      : 0
% 2.23/1.28  #Demod        : 51
% 2.23/1.28  #Tautology    : 79
% 2.23/1.28  #SimpNegUnit  : 0
% 2.23/1.28  #BackRed      : 21
% 2.23/1.28  
% 2.23/1.28  #Partial instantiations: 0
% 2.23/1.28  #Strategies tried      : 1
% 2.23/1.28  
% 2.23/1.28  Timing (in seconds)
% 2.23/1.28  ----------------------
% 2.23/1.28  Preprocessing        : 0.34
% 2.23/1.28  Parsing              : 0.17
% 2.23/1.28  CNF conversion       : 0.02
% 2.23/1.28  Main loop            : 0.18
% 2.23/1.28  Inferencing          : 0.06
% 2.23/1.28  Reduction            : 0.07
% 2.23/1.28  Demodulation         : 0.05
% 2.23/1.28  BG Simplification    : 0.02
% 2.23/1.28  Subsumption          : 0.03
% 2.23/1.28  Abstraction          : 0.01
% 2.23/1.28  MUC search           : 0.00
% 2.23/1.28  Cooper               : 0.00
% 2.23/1.28  Total                : 0.56
% 2.23/1.29  Index Insertion      : 0.00
% 2.23/1.29  Index Deletion       : 0.00
% 2.23/1.29  Index Matching       : 0.00
% 2.23/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
