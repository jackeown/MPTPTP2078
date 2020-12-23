%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:54 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   52 (  68 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   37 (  54 expanded)
%              Number of equality atoms :   30 (  47 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_32,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    ! [B_44,A_45] : k5_xboole_0(B_44,A_45) = k5_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_45] : k5_xboole_0(k1_xboole_0,A_45) = A_45 ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_398,plain,(
    ! [A_67,B_68,C_69] : k5_xboole_0(k5_xboole_0(A_67,B_68),C_69) = k5_xboole_0(A_67,k5_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_484,plain,(
    ! [A_13,C_69] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_69)) = k5_xboole_0(k1_xboole_0,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_398])).

tff(c_498,plain,(
    ! [A_70,C_71] : k5_xboole_0(A_70,k5_xboole_0(A_70,C_71)) = C_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_484])).

tff(c_912,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k2_xboole_0(A_93,B_94)) = k4_xboole_0(B_94,A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_498])).

tff(c_948,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_912])).

tff(c_957,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_948])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_967,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k4_xboole_0(A_95,B_96)) = k3_xboole_0(A_95,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_498])).

tff(c_1003,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_967])).

tff(c_1029,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1003])).

tff(c_172,plain,(
    ! [B_47,A_48] : k3_xboole_0(B_47,A_48) = k3_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_187,plain,(
    ! [B_47,A_48] : r1_tarski(k3_xboole_0(B_47,A_48),A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_8])).

tff(c_1041,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_187])).

tff(c_30,plain,(
    ! [B_38,A_37] :
      ( B_38 = A_37
      | ~ r1_tarski(k1_tarski(A_37),k1_tarski(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1063,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1041,c_30])).

tff(c_1067,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:22:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.38  
% 2.77/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.38  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.77/1.38  
% 2.77/1.38  %Foreground sorts:
% 2.77/1.38  
% 2.77/1.38  
% 2.77/1.38  %Background operators:
% 2.77/1.38  
% 2.77/1.38  
% 2.77/1.38  %Foreground operators:
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.77/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.38  
% 2.77/1.39  tff(f_62, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.77/1.39  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.77/1.39  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.77/1.39  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.77/1.39  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.77/1.39  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.77/1.39  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.77/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.77/1.39  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.77/1.39  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.77/1.39  tff(c_32, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.77/1.39  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.39  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.39  tff(c_34, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.77/1.39  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.77/1.39  tff(c_71, plain, (![B_44, A_45]: (k5_xboole_0(B_44, A_45)=k5_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.39  tff(c_87, plain, (![A_45]: (k5_xboole_0(k1_xboole_0, A_45)=A_45)), inference(superposition, [status(thm), theory('equality')], [c_71, c_10])).
% 2.77/1.39  tff(c_398, plain, (![A_67, B_68, C_69]: (k5_xboole_0(k5_xboole_0(A_67, B_68), C_69)=k5_xboole_0(A_67, k5_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.77/1.39  tff(c_484, plain, (![A_13, C_69]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_69))=k5_xboole_0(k1_xboole_0, C_69))), inference(superposition, [status(thm), theory('equality')], [c_14, c_398])).
% 2.77/1.39  tff(c_498, plain, (![A_70, C_71]: (k5_xboole_0(A_70, k5_xboole_0(A_70, C_71))=C_71)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_484])).
% 2.77/1.39  tff(c_912, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k2_xboole_0(A_93, B_94))=k4_xboole_0(B_94, A_93))), inference(superposition, [status(thm), theory('equality')], [c_16, c_498])).
% 2.77/1.39  tff(c_948, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_912])).
% 2.77/1.39  tff(c_957, plain, (k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_948])).
% 2.77/1.39  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.39  tff(c_967, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k4_xboole_0(A_95, B_96))=k3_xboole_0(A_95, B_96))), inference(superposition, [status(thm), theory('equality')], [c_6, c_498])).
% 2.77/1.39  tff(c_1003, plain, (k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_957, c_967])).
% 2.77/1.39  tff(c_1029, plain, (k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1003])).
% 2.77/1.39  tff(c_172, plain, (![B_47, A_48]: (k3_xboole_0(B_47, A_48)=k3_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.39  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.77/1.39  tff(c_187, plain, (![B_47, A_48]: (r1_tarski(k3_xboole_0(B_47, A_48), A_48))), inference(superposition, [status(thm), theory('equality')], [c_172, c_8])).
% 2.77/1.39  tff(c_1041, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1029, c_187])).
% 2.77/1.39  tff(c_30, plain, (![B_38, A_37]: (B_38=A_37 | ~r1_tarski(k1_tarski(A_37), k1_tarski(B_38)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.39  tff(c_1063, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_1041, c_30])).
% 2.77/1.39  tff(c_1067, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1063])).
% 2.77/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.39  
% 2.77/1.39  Inference rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Ref     : 0
% 2.77/1.39  #Sup     : 258
% 2.77/1.39  #Fact    : 0
% 2.77/1.39  #Define  : 0
% 2.77/1.39  #Split   : 0
% 2.77/1.39  #Chain   : 0
% 2.77/1.39  #Close   : 0
% 2.77/1.39  
% 2.77/1.39  Ordering : KBO
% 2.77/1.39  
% 2.77/1.39  Simplification rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Subsume      : 6
% 2.77/1.39  #Demod        : 109
% 2.77/1.39  #Tautology    : 174
% 2.77/1.39  #SimpNegUnit  : 1
% 2.77/1.39  #BackRed      : 0
% 2.77/1.39  
% 2.77/1.39  #Partial instantiations: 0
% 2.77/1.39  #Strategies tried      : 1
% 2.77/1.39  
% 2.77/1.39  Timing (in seconds)
% 2.77/1.39  ----------------------
% 2.77/1.39  Preprocessing        : 0.30
% 2.77/1.39  Parsing              : 0.17
% 2.77/1.39  CNF conversion       : 0.02
% 2.77/1.40  Main loop            : 0.33
% 2.77/1.40  Inferencing          : 0.12
% 2.77/1.40  Reduction            : 0.13
% 2.77/1.40  Demodulation         : 0.11
% 2.77/1.40  BG Simplification    : 0.02
% 2.77/1.40  Subsumption          : 0.04
% 2.77/1.40  Abstraction          : 0.02
% 2.77/1.40  MUC search           : 0.00
% 2.77/1.40  Cooper               : 0.00
% 2.77/1.40  Total                : 0.66
% 2.77/1.40  Index Insertion      : 0.00
% 2.77/1.40  Index Deletion       : 0.00
% 2.77/1.40  Index Matching       : 0.00
% 2.77/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
