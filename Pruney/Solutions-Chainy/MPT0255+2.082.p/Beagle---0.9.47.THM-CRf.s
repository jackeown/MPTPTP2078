%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:50 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 165 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :   72 ( 228 expanded)
%              Number of equality atoms :   26 (  70 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_30,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_56,plain,(
    ! [B_30,A_31] :
      ( ~ v1_xboole_0(k2_xboole_0(B_30,A_31))
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_56])).

tff(c_61,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_46,plain,(
    ! [B_27,A_28] :
      ( ~ v1_xboole_0(B_27)
      | B_27 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_49,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_4,c_46])).

tff(c_67,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_61,c_49])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_10])).

tff(c_70,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_30])).

tff(c_87,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( ~ v1_xboole_0(k2_xboole_0(B_4,A_3))
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_113,plain,(
    ! [A_37,B_36] :
      ( ~ v1_xboole_0(k2_xboole_0(A_37,B_36))
      | v1_xboole_0(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_6])).

tff(c_162,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_113])).

tff(c_181,plain,(
    v1_xboole_0(k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_162])).

tff(c_69,plain,(
    ! [A_28] :
      ( A_28 = '#skF_3'
      | ~ v1_xboole_0(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_49])).

tff(c_190,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_181,c_69])).

tff(c_381,plain,(
    ! [A_60,C_61,B_62] :
      ( r2_hidden(A_60,C_61)
      | ~ r1_tarski(k2_tarski(A_60,B_62),C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_384,plain,(
    ! [C_61] :
      ( r2_hidden('#skF_1',C_61)
      | ~ r1_tarski('#skF_3',C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_381])).

tff(c_389,plain,(
    ! [C_61] : r2_hidden('#skF_1',C_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_384])).

tff(c_214,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(A_44,B_45) = B_45
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_220,plain,(
    ! [A_46] : k2_xboole_0('#skF_3',A_46) = A_46 ),
    inference(resolution,[status(thm)],[c_72,c_214])).

tff(c_28,plain,(
    ! [A_21,B_22] : k2_xboole_0(k1_tarski(A_21),B_22) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_71,plain,(
    ! [A_21,B_22] : k2_xboole_0(k1_tarski(A_21),B_22) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_28])).

tff(c_103,plain,(
    ! [B_36,A_21] : k2_xboole_0(B_36,k1_tarski(A_21)) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_71])).

tff(c_230,plain,(
    ! [A_21] : k1_tarski(A_21) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_103])).

tff(c_14,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_400,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(k2_tarski(A_67,B_68),C_69)
      | ~ r2_hidden(B_68,C_69)
      | ~ r2_hidden(A_67,C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_421,plain,(
    ! [A_70,C_71] :
      ( r1_tarski(k1_tarski(A_70),C_71)
      | ~ r2_hidden(A_70,C_71)
      | ~ r2_hidden(A_70,C_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_400])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_430,plain,(
    ! [A_72,C_73] :
      ( k2_xboole_0(k1_tarski(A_72),C_73) = C_73
      | ~ r2_hidden(A_72,C_73) ) ),
    inference(resolution,[status(thm)],[c_421,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_233,plain,(
    ! [A_46] : k2_xboole_0(A_46,'#skF_3') = A_46 ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_2])).

tff(c_441,plain,(
    ! [A_72] :
      ( k1_tarski(A_72) = '#skF_3'
      | ~ r2_hidden(A_72,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_233])).

tff(c_540,plain,(
    ! [A_77] : ~ r2_hidden(A_77,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_441])).

tff(c_548,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_389,c_540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.34  
% 2.42/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.34  %$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.42/1.34  
% 2.42/1.34  %Foreground sorts:
% 2.42/1.34  
% 2.42/1.34  
% 2.42/1.34  %Background operators:
% 2.42/1.34  
% 2.42/1.34  
% 2.42/1.34  %Foreground operators:
% 2.42/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.42/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.42/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.42/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.42/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.42/1.34  
% 2.42/1.35  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.42/1.35  tff(f_69, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.42/1.35  tff(f_34, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.42/1.35  tff(f_48, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.42/1.35  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.42/1.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.42/1.35  tff(f_62, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.42/1.35  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.42/1.35  tff(f_65, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.42/1.35  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.42/1.35  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.42/1.35  tff(c_30, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.42/1.35  tff(c_56, plain, (![B_30, A_31]: (~v1_xboole_0(k2_xboole_0(B_30, A_31)) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.42/1.35  tff(c_59, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_56])).
% 2.42/1.35  tff(c_61, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_59])).
% 2.42/1.35  tff(c_46, plain, (![B_27, A_28]: (~v1_xboole_0(B_27) | B_27=A_28 | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.42/1.35  tff(c_49, plain, (![A_28]: (k1_xboole_0=A_28 | ~v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_4, c_46])).
% 2.42/1.35  tff(c_67, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_61, c_49])).
% 2.42/1.35  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.42/1.35  tff(c_72, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_10])).
% 2.42/1.35  tff(c_70, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_30])).
% 2.42/1.35  tff(c_87, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.42/1.35  tff(c_6, plain, (![B_4, A_3]: (~v1_xboole_0(k2_xboole_0(B_4, A_3)) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.42/1.35  tff(c_113, plain, (![A_37, B_36]: (~v1_xboole_0(k2_xboole_0(A_37, B_36)) | v1_xboole_0(A_37))), inference(superposition, [status(thm), theory('equality')], [c_87, c_6])).
% 2.42/1.35  tff(c_162, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0(k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_113])).
% 2.42/1.35  tff(c_181, plain, (v1_xboole_0(k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_162])).
% 2.42/1.35  tff(c_69, plain, (![A_28]: (A_28='#skF_3' | ~v1_xboole_0(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_49])).
% 2.42/1.35  tff(c_190, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_181, c_69])).
% 2.42/1.35  tff(c_381, plain, (![A_60, C_61, B_62]: (r2_hidden(A_60, C_61) | ~r1_tarski(k2_tarski(A_60, B_62), C_61))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.42/1.35  tff(c_384, plain, (![C_61]: (r2_hidden('#skF_1', C_61) | ~r1_tarski('#skF_3', C_61))), inference(superposition, [status(thm), theory('equality')], [c_190, c_381])).
% 2.42/1.35  tff(c_389, plain, (![C_61]: (r2_hidden('#skF_1', C_61))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_384])).
% 2.42/1.35  tff(c_214, plain, (![A_44, B_45]: (k2_xboole_0(A_44, B_45)=B_45 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.42/1.35  tff(c_220, plain, (![A_46]: (k2_xboole_0('#skF_3', A_46)=A_46)), inference(resolution, [status(thm)], [c_72, c_214])).
% 2.42/1.35  tff(c_28, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.42/1.35  tff(c_71, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), B_22)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_28])).
% 2.42/1.35  tff(c_103, plain, (![B_36, A_21]: (k2_xboole_0(B_36, k1_tarski(A_21))!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_87, c_71])).
% 2.42/1.35  tff(c_230, plain, (![A_21]: (k1_tarski(A_21)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_220, c_103])).
% 2.42/1.35  tff(c_14, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.42/1.35  tff(c_400, plain, (![A_67, B_68, C_69]: (r1_tarski(k2_tarski(A_67, B_68), C_69) | ~r2_hidden(B_68, C_69) | ~r2_hidden(A_67, C_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.42/1.35  tff(c_421, plain, (![A_70, C_71]: (r1_tarski(k1_tarski(A_70), C_71) | ~r2_hidden(A_70, C_71) | ~r2_hidden(A_70, C_71))), inference(superposition, [status(thm), theory('equality')], [c_14, c_400])).
% 2.42/1.35  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.42/1.35  tff(c_430, plain, (![A_72, C_73]: (k2_xboole_0(k1_tarski(A_72), C_73)=C_73 | ~r2_hidden(A_72, C_73))), inference(resolution, [status(thm)], [c_421, c_8])).
% 2.42/1.35  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.42/1.35  tff(c_233, plain, (![A_46]: (k2_xboole_0(A_46, '#skF_3')=A_46)), inference(superposition, [status(thm), theory('equality')], [c_220, c_2])).
% 2.42/1.35  tff(c_441, plain, (![A_72]: (k1_tarski(A_72)='#skF_3' | ~r2_hidden(A_72, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_430, c_233])).
% 2.42/1.35  tff(c_540, plain, (![A_77]: (~r2_hidden(A_77, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_230, c_441])).
% 2.42/1.35  tff(c_548, plain, $false, inference(resolution, [status(thm)], [c_389, c_540])).
% 2.42/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.35  
% 2.42/1.35  Inference rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Ref     : 0
% 2.42/1.35  #Sup     : 128
% 2.42/1.35  #Fact    : 0
% 2.42/1.35  #Define  : 0
% 2.42/1.35  #Split   : 1
% 2.42/1.35  #Chain   : 0
% 2.42/1.35  #Close   : 0
% 2.42/1.35  
% 2.42/1.35  Ordering : KBO
% 2.42/1.35  
% 2.42/1.35  Simplification rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Subsume      : 19
% 2.42/1.35  #Demod        : 44
% 2.42/1.35  #Tautology    : 70
% 2.42/1.35  #SimpNegUnit  : 2
% 2.42/1.35  #BackRed      : 7
% 2.42/1.35  
% 2.42/1.35  #Partial instantiations: 0
% 2.42/1.35  #Strategies tried      : 1
% 2.42/1.35  
% 2.42/1.35  Timing (in seconds)
% 2.42/1.35  ----------------------
% 2.42/1.36  Preprocessing        : 0.31
% 2.42/1.36  Parsing              : 0.17
% 2.42/1.36  CNF conversion       : 0.02
% 2.42/1.36  Main loop            : 0.27
% 2.42/1.36  Inferencing          : 0.10
% 2.42/1.36  Reduction            : 0.09
% 2.42/1.36  Demodulation         : 0.07
% 2.42/1.36  BG Simplification    : 0.01
% 2.42/1.36  Subsumption          : 0.04
% 2.42/1.36  Abstraction          : 0.02
% 2.42/1.36  MUC search           : 0.00
% 2.42/1.36  Cooper               : 0.00
% 2.42/1.36  Total                : 0.61
% 2.42/1.36  Index Insertion      : 0.00
% 2.42/1.36  Index Deletion       : 0.00
% 2.42/1.36  Index Matching       : 0.00
% 2.42/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
