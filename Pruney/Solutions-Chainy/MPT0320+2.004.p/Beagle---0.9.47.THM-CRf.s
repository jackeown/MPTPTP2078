%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:12 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   51 (  77 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  72 expanded)
%              Number of equality atoms :   37 (  70 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
        & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(c_6,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14,D_15] : k3_enumset1(A_12,A_12,B_13,C_14,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1263,plain,(
    ! [C_80,E_77,A_81,D_78,B_79] : k2_xboole_0(k2_enumset1(A_81,B_79,C_80,D_78),k1_tarski(E_77)) = k3_enumset1(A_81,B_79,C_80,D_78,E_77) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1272,plain,(
    ! [A_9,B_10,C_11,E_77] : k3_enumset1(A_9,A_9,B_10,C_11,E_77) = k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_tarski(E_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1263])).

tff(c_1847,plain,(
    ! [A_91,B_92,C_93,E_94] : k2_xboole_0(k1_enumset1(A_91,B_92,C_93),k1_tarski(E_94)) = k2_enumset1(A_91,B_92,C_93,E_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1272])).

tff(c_1856,plain,(
    ! [A_7,B_8,E_94] : k2_xboole_0(k2_tarski(A_7,B_8),k1_tarski(E_94)) = k2_enumset1(A_7,A_7,B_8,E_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1847])).

tff(c_1860,plain,(
    ! [A_95,B_96,E_97] : k2_xboole_0(k2_tarski(A_95,B_96),k1_tarski(E_97)) = k1_enumset1(A_95,B_96,E_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1856])).

tff(c_1869,plain,(
    ! [A_6,E_97] : k2_xboole_0(k1_tarski(A_6),k1_tarski(E_97)) = k1_enumset1(A_6,A_6,E_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1860])).

tff(c_1872,plain,(
    ! [A_6,E_97] : k2_xboole_0(k1_tarski(A_6),k1_tarski(E_97)) = k2_tarski(A_6,E_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1869])).

tff(c_673,plain,(
    ! [A_56,E_52,D_53,C_55,B_54] : k2_xboole_0(k2_enumset1(A_56,B_54,C_55,D_53),k1_tarski(E_52)) = k3_enumset1(A_56,B_54,C_55,D_53,E_52) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_682,plain,(
    ! [A_9,B_10,C_11,E_52] : k3_enumset1(A_9,A_9,B_10,C_11,E_52) = k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_tarski(E_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_673])).

tff(c_939,plain,(
    ! [A_61,B_62,C_63,E_64] : k2_xboole_0(k1_enumset1(A_61,B_62,C_63),k1_tarski(E_64)) = k2_enumset1(A_61,B_62,C_63,E_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_682])).

tff(c_948,plain,(
    ! [A_7,B_8,E_64] : k2_xboole_0(k2_tarski(A_7,B_8),k1_tarski(E_64)) = k2_enumset1(A_7,A_7,B_8,E_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_939])).

tff(c_952,plain,(
    ! [A_65,B_66,E_67] : k2_xboole_0(k2_tarski(A_65,B_66),k1_tarski(E_67)) = k1_enumset1(A_65,B_66,E_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_948])).

tff(c_961,plain,(
    ! [A_6,E_67] : k2_xboole_0(k1_tarski(A_6),k1_tarski(E_67)) = k1_enumset1(A_6,A_6,E_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_952])).

tff(c_964,plain,(
    ! [A_6,E_67] : k2_xboole_0(k1_tarski(A_6),k1_tarski(E_67)) = k2_tarski(A_6,E_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_961])).

tff(c_14,plain,(
    ! [A_18,C_20,B_19] : k2_xboole_0(k2_zfmisc_1(A_18,C_20),k2_zfmisc_1(B_19,C_20)) = k2_zfmisc_1(k2_xboole_0(A_18,B_19),C_20) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [C_20,A_18,B_19] : k2_xboole_0(k2_zfmisc_1(C_20,A_18),k2_zfmisc_1(C_20,B_19)) = k2_zfmisc_1(C_20,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_3',k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_20,plain,
    ( k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_19])).

tff(c_133,plain,(
    k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_964,c_133])).

tff(c_968,plain,(
    k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_1878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_968])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:52:31 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.80  
% 4.50/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.81  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.50/1.81  
% 4.50/1.81  %Foreground sorts:
% 4.50/1.81  
% 4.50/1.81  
% 4.50/1.81  %Background operators:
% 4.50/1.81  
% 4.50/1.81  
% 4.50/1.81  %Foreground operators:
% 4.50/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.50/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.50/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.50/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.50/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.50/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.50/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.50/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.50/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.50/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.50/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.50/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.50/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.50/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.50/1.81  
% 4.50/1.82  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.50/1.82  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.50/1.82  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.50/1.82  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.50/1.82  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 4.50/1.82  tff(f_41, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 4.50/1.82  tff(f_46, negated_conjecture, ~(![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 4.50/1.82  tff(c_6, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.50/1.82  tff(c_4, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.50/1.82  tff(c_8, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.50/1.82  tff(c_10, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.50/1.82  tff(c_1263, plain, (![C_80, E_77, A_81, D_78, B_79]: (k2_xboole_0(k2_enumset1(A_81, B_79, C_80, D_78), k1_tarski(E_77))=k3_enumset1(A_81, B_79, C_80, D_78, E_77))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.50/1.82  tff(c_1272, plain, (![A_9, B_10, C_11, E_77]: (k3_enumset1(A_9, A_9, B_10, C_11, E_77)=k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_tarski(E_77)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1263])).
% 4.50/1.82  tff(c_1847, plain, (![A_91, B_92, C_93, E_94]: (k2_xboole_0(k1_enumset1(A_91, B_92, C_93), k1_tarski(E_94))=k2_enumset1(A_91, B_92, C_93, E_94))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1272])).
% 4.50/1.82  tff(c_1856, plain, (![A_7, B_8, E_94]: (k2_xboole_0(k2_tarski(A_7, B_8), k1_tarski(E_94))=k2_enumset1(A_7, A_7, B_8, E_94))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1847])).
% 4.50/1.82  tff(c_1860, plain, (![A_95, B_96, E_97]: (k2_xboole_0(k2_tarski(A_95, B_96), k1_tarski(E_97))=k1_enumset1(A_95, B_96, E_97))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1856])).
% 4.50/1.82  tff(c_1869, plain, (![A_6, E_97]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(E_97))=k1_enumset1(A_6, A_6, E_97))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1860])).
% 4.50/1.82  tff(c_1872, plain, (![A_6, E_97]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(E_97))=k2_tarski(A_6, E_97))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1869])).
% 4.50/1.82  tff(c_673, plain, (![A_56, E_52, D_53, C_55, B_54]: (k2_xboole_0(k2_enumset1(A_56, B_54, C_55, D_53), k1_tarski(E_52))=k3_enumset1(A_56, B_54, C_55, D_53, E_52))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.50/1.82  tff(c_682, plain, (![A_9, B_10, C_11, E_52]: (k3_enumset1(A_9, A_9, B_10, C_11, E_52)=k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_tarski(E_52)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_673])).
% 4.50/1.82  tff(c_939, plain, (![A_61, B_62, C_63, E_64]: (k2_xboole_0(k1_enumset1(A_61, B_62, C_63), k1_tarski(E_64))=k2_enumset1(A_61, B_62, C_63, E_64))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_682])).
% 4.50/1.82  tff(c_948, plain, (![A_7, B_8, E_64]: (k2_xboole_0(k2_tarski(A_7, B_8), k1_tarski(E_64))=k2_enumset1(A_7, A_7, B_8, E_64))), inference(superposition, [status(thm), theory('equality')], [c_6, c_939])).
% 4.50/1.82  tff(c_952, plain, (![A_65, B_66, E_67]: (k2_xboole_0(k2_tarski(A_65, B_66), k1_tarski(E_67))=k1_enumset1(A_65, B_66, E_67))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_948])).
% 4.50/1.82  tff(c_961, plain, (![A_6, E_67]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(E_67))=k1_enumset1(A_6, A_6, E_67))), inference(superposition, [status(thm), theory('equality')], [c_4, c_952])).
% 4.50/1.82  tff(c_964, plain, (![A_6, E_67]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(E_67))=k2_tarski(A_6, E_67))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_961])).
% 4.50/1.82  tff(c_14, plain, (![A_18, C_20, B_19]: (k2_xboole_0(k2_zfmisc_1(A_18, C_20), k2_zfmisc_1(B_19, C_20))=k2_zfmisc_1(k2_xboole_0(A_18, B_19), C_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.50/1.82  tff(c_16, plain, (![C_20, A_18, B_19]: (k2_xboole_0(k2_zfmisc_1(C_20, A_18), k2_zfmisc_1(C_20, B_19))=k2_zfmisc_1(C_20, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.50/1.82  tff(c_18, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_3', k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.50/1.82  tff(c_19, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 4.50/1.82  tff(c_20, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_19])).
% 4.50/1.82  tff(c_133, plain, (k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_20])).
% 4.50/1.82  tff(c_967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_964, c_133])).
% 4.50/1.82  tff(c_968, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_20])).
% 4.50/1.82  tff(c_1878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1872, c_968])).
% 4.50/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.82  
% 4.50/1.82  Inference rules
% 4.50/1.82  ----------------------
% 4.50/1.82  #Ref     : 0
% 4.50/1.82  #Sup     : 477
% 4.50/1.82  #Fact    : 0
% 4.50/1.82  #Define  : 0
% 4.50/1.82  #Split   : 1
% 4.50/1.82  #Chain   : 0
% 4.50/1.82  #Close   : 0
% 4.50/1.82  
% 4.50/1.82  Ordering : KBO
% 4.50/1.82  
% 4.50/1.82  Simplification rules
% 4.50/1.82  ----------------------
% 4.50/1.82  #Subsume      : 47
% 4.50/1.82  #Demod        : 235
% 4.50/1.82  #Tautology    : 108
% 4.50/1.82  #SimpNegUnit  : 0
% 4.50/1.82  #BackRed      : 3
% 4.50/1.82  
% 4.50/1.82  #Partial instantiations: 0
% 4.50/1.82  #Strategies tried      : 1
% 4.50/1.82  
% 4.50/1.82  Timing (in seconds)
% 4.50/1.82  ----------------------
% 4.78/1.82  Preprocessing        : 0.30
% 4.78/1.82  Parsing              : 0.16
% 4.78/1.82  CNF conversion       : 0.02
% 4.78/1.82  Main loop            : 0.77
% 4.78/1.82  Inferencing          : 0.23
% 4.78/1.82  Reduction            : 0.35
% 4.78/1.82  Demodulation         : 0.31
% 4.78/1.82  BG Simplification    : 0.04
% 4.78/1.82  Subsumption          : 0.10
% 4.78/1.82  Abstraction          : 0.05
% 4.78/1.82  MUC search           : 0.00
% 4.78/1.82  Cooper               : 0.00
% 4.78/1.82  Total                : 1.10
% 4.78/1.82  Index Insertion      : 0.00
% 4.78/1.82  Index Deletion       : 0.00
% 4.78/1.82  Index Matching       : 0.00
% 4.78/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
