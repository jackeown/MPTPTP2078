%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:27 EST 2020

% Result     : Theorem 7.21s
% Output     : CNFRefutation 7.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  65 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   37 (  51 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_32,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_221,plain,(
    ! [A_67,B_68] : k5_xboole_0(k5_xboole_0(A_67,B_68),k2_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_728,plain,(
    ! [B_89,A_90] : k5_xboole_0(k5_xboole_0(B_89,A_90),k2_xboole_0(A_90,B_89)) = k3_xboole_0(A_90,B_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_221])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k5_xboole_0(k5_xboole_0(A_5,B_6),C_7) = k5_xboole_0(A_5,k5_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_755,plain,(
    ! [B_89,A_90] : k5_xboole_0(B_89,k5_xboole_0(A_90,k2_xboole_0(A_90,B_89))) = k3_xboole_0(A_90,B_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_6])).

tff(c_10,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_126,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(B_55,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_102])).

tff(c_24,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_132,plain,(
    ! [B_55,A_54] : k2_xboole_0(B_55,A_54) = k2_xboole_0(A_54,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_24])).

tff(c_4237,plain,(
    ! [B_138,A_139] : k5_xboole_0(k5_xboole_0(B_138,A_139),k2_xboole_0(A_139,B_138)) = k3_xboole_0(B_138,A_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_221])).

tff(c_262,plain,(
    ! [A_69,B_70,C_71] : k5_xboole_0(k5_xboole_0(A_69,B_70),C_71) = k5_xboole_0(A_69,k5_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_407,plain,(
    ! [C_79,A_80,B_81] : k5_xboole_0(C_79,k5_xboole_0(A_80,B_81)) = k5_xboole_0(A_80,k5_xboole_0(B_81,C_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_2])).

tff(c_969,plain,(
    ! [A_105,A_104,B_106] : k5_xboole_0(A_105,k5_xboole_0(A_104,B_106)) = k5_xboole_0(A_104,k5_xboole_0(A_105,B_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_407])).

tff(c_1096,plain,(
    ! [A_105,B_106,A_104] : k5_xboole_0(k5_xboole_0(A_105,B_106),A_104) = k5_xboole_0(A_105,k5_xboole_0(A_104,B_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_969,c_2])).

tff(c_4255,plain,(
    ! [B_138,A_139] : k5_xboole_0(B_138,k5_xboole_0(k2_xboole_0(A_139,B_138),A_139)) = k3_xboole_0(B_138,A_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_4237,c_1096])).

tff(c_4479,plain,(
    ! [B_140,A_141] : k3_xboole_0(B_140,A_141) = k3_xboole_0(A_141,B_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_2,c_4255])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4530,plain,(
    ! [B_142,A_143] : r1_tarski(k3_xboole_0(B_142,A_143),A_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_4479,c_4])).

tff(c_4539,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4530])).

tff(c_30,plain,(
    ! [A_41,C_43,B_42] :
      ( r2_hidden(A_41,C_43)
      | ~ r1_tarski(k2_tarski(A_41,B_42),C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4548,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_4539,c_30])).

tff(c_4553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_4548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:54:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.21/2.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.62  
% 7.21/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.62  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 7.21/2.62  
% 7.21/2.62  %Foreground sorts:
% 7.21/2.62  
% 7.21/2.62  
% 7.21/2.62  %Background operators:
% 7.21/2.62  
% 7.21/2.62  
% 7.21/2.62  %Foreground operators:
% 7.21/2.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.21/2.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.21/2.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.21/2.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.21/2.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.21/2.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.21/2.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.21/2.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.21/2.62  tff('#skF_2', type, '#skF_2': $i).
% 7.21/2.62  tff('#skF_3', type, '#skF_3': $i).
% 7.21/2.62  tff('#skF_1', type, '#skF_1': $i).
% 7.21/2.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.21/2.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.21/2.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.21/2.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.21/2.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.21/2.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.21/2.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.21/2.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.21/2.62  
% 7.21/2.63  tff(f_60, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 7.21/2.63  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.21/2.63  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.21/2.63  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.21/2.63  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.21/2.63  tff(f_49, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.21/2.63  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.21/2.63  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 7.21/2.63  tff(c_32, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.21/2.63  tff(c_34, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.21/2.63  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.21/2.63  tff(c_221, plain, (![A_67, B_68]: (k5_xboole_0(k5_xboole_0(A_67, B_68), k2_xboole_0(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.21/2.63  tff(c_728, plain, (![B_89, A_90]: (k5_xboole_0(k5_xboole_0(B_89, A_90), k2_xboole_0(A_90, B_89))=k3_xboole_0(A_90, B_89))), inference(superposition, [status(thm), theory('equality')], [c_2, c_221])).
% 7.21/2.63  tff(c_6, plain, (![A_5, B_6, C_7]: (k5_xboole_0(k5_xboole_0(A_5, B_6), C_7)=k5_xboole_0(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.21/2.63  tff(c_755, plain, (![B_89, A_90]: (k5_xboole_0(B_89, k5_xboole_0(A_90, k2_xboole_0(A_90, B_89)))=k3_xboole_0(A_90, B_89))), inference(superposition, [status(thm), theory('equality')], [c_728, c_6])).
% 7.21/2.63  tff(c_10, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.21/2.63  tff(c_102, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.21/2.63  tff(c_126, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(B_55, A_54))), inference(superposition, [status(thm), theory('equality')], [c_10, c_102])).
% 7.21/2.63  tff(c_24, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.21/2.63  tff(c_132, plain, (![B_55, A_54]: (k2_xboole_0(B_55, A_54)=k2_xboole_0(A_54, B_55))), inference(superposition, [status(thm), theory('equality')], [c_126, c_24])).
% 7.21/2.63  tff(c_4237, plain, (![B_138, A_139]: (k5_xboole_0(k5_xboole_0(B_138, A_139), k2_xboole_0(A_139, B_138))=k3_xboole_0(B_138, A_139))), inference(superposition, [status(thm), theory('equality')], [c_132, c_221])).
% 7.21/2.63  tff(c_262, plain, (![A_69, B_70, C_71]: (k5_xboole_0(k5_xboole_0(A_69, B_70), C_71)=k5_xboole_0(A_69, k5_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.21/2.63  tff(c_407, plain, (![C_79, A_80, B_81]: (k5_xboole_0(C_79, k5_xboole_0(A_80, B_81))=k5_xboole_0(A_80, k5_xboole_0(B_81, C_79)))), inference(superposition, [status(thm), theory('equality')], [c_262, c_2])).
% 7.21/2.63  tff(c_969, plain, (![A_105, A_104, B_106]: (k5_xboole_0(A_105, k5_xboole_0(A_104, B_106))=k5_xboole_0(A_104, k5_xboole_0(A_105, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_407])).
% 7.21/2.63  tff(c_1096, plain, (![A_105, B_106, A_104]: (k5_xboole_0(k5_xboole_0(A_105, B_106), A_104)=k5_xboole_0(A_105, k5_xboole_0(A_104, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_969, c_2])).
% 7.21/2.63  tff(c_4255, plain, (![B_138, A_139]: (k5_xboole_0(B_138, k5_xboole_0(k2_xboole_0(A_139, B_138), A_139))=k3_xboole_0(B_138, A_139))), inference(superposition, [status(thm), theory('equality')], [c_4237, c_1096])).
% 7.21/2.63  tff(c_4479, plain, (![B_140, A_141]: (k3_xboole_0(B_140, A_141)=k3_xboole_0(A_141, B_140))), inference(demodulation, [status(thm), theory('equality')], [c_755, c_2, c_4255])).
% 7.21/2.63  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.21/2.63  tff(c_4530, plain, (![B_142, A_143]: (r1_tarski(k3_xboole_0(B_142, A_143), A_143))), inference(superposition, [status(thm), theory('equality')], [c_4479, c_4])).
% 7.21/2.63  tff(c_4539, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_4530])).
% 7.21/2.63  tff(c_30, plain, (![A_41, C_43, B_42]: (r2_hidden(A_41, C_43) | ~r1_tarski(k2_tarski(A_41, B_42), C_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.21/2.63  tff(c_4548, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_4539, c_30])).
% 7.21/2.63  tff(c_4553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_4548])).
% 7.21/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.63  
% 7.21/2.63  Inference rules
% 7.21/2.63  ----------------------
% 7.21/2.63  #Ref     : 0
% 7.21/2.63  #Sup     : 1215
% 7.21/2.63  #Fact    : 0
% 7.21/2.63  #Define  : 0
% 7.21/2.63  #Split   : 0
% 7.21/2.63  #Chain   : 0
% 7.21/2.63  #Close   : 0
% 7.21/2.63  
% 7.21/2.63  Ordering : KBO
% 7.21/2.63  
% 7.21/2.63  Simplification rules
% 7.21/2.63  ----------------------
% 7.21/2.63  #Subsume      : 94
% 7.21/2.63  #Demod        : 858
% 7.21/2.63  #Tautology    : 231
% 7.21/2.63  #SimpNegUnit  : 1
% 7.21/2.63  #BackRed      : 0
% 7.21/2.63  
% 7.21/2.63  #Partial instantiations: 0
% 7.21/2.63  #Strategies tried      : 1
% 7.21/2.63  
% 7.21/2.63  Timing (in seconds)
% 7.21/2.63  ----------------------
% 7.21/2.63  Preprocessing        : 0.31
% 7.21/2.63  Parsing              : 0.17
% 7.21/2.64  CNF conversion       : 0.02
% 7.21/2.64  Main loop            : 1.57
% 7.21/2.64  Inferencing          : 0.32
% 7.21/2.64  Reduction            : 1.01
% 7.21/2.64  Demodulation         : 0.94
% 7.21/2.64  BG Simplification    : 0.06
% 7.21/2.64  Subsumption          : 0.13
% 7.21/2.64  Abstraction          : 0.08
% 7.21/2.64  MUC search           : 0.00
% 7.21/2.64  Cooper               : 0.00
% 7.21/2.64  Total                : 1.91
% 7.21/2.64  Index Insertion      : 0.00
% 7.21/2.64  Index Deletion       : 0.00
% 7.21/2.64  Index Matching       : 0.00
% 7.21/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
