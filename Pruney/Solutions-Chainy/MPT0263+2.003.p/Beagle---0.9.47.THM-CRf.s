%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:14 EST 2020

% Result     : Theorem 7.06s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :   51 (  66 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   37 (  53 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_62,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_89,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(k1_tarski(A_50),B_51)
      | r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_93,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_36])).

tff(c_30,plain,(
    ! [B_42,A_41] :
      ( k3_xboole_0(B_42,k1_tarski(A_41)) = k1_tarski(A_41)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_138,plain,(
    ! [B_57,A_58] : k3_tarski(k2_tarski(B_57,A_58)) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_94])).

tff(c_32,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_144,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_32])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : k4_xboole_0(k2_xboole_0(A_8,B_9),k3_xboole_0(A_8,B_9)) = k2_xboole_0(k4_xboole_0(A_8,B_9),k4_xboole_0(B_9,A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_219,plain,(
    ! [A_66,B_67] : k2_xboole_0(k4_xboole_0(A_66,B_67),k4_xboole_0(B_67,A_66)) = k5_xboole_0(A_66,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_1109,plain,(
    ! [B_112,A_113] : k2_xboole_0(k4_xboole_0(B_112,A_113),k4_xboole_0(A_113,B_112)) = k5_xboole_0(A_113,B_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_219])).

tff(c_37,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),k4_xboole_0(B_9,A_8)) = k5_xboole_0(A_8,B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_1186,plain,(
    ! [B_114,A_115] : k5_xboole_0(B_114,A_115) = k5_xboole_0(A_115,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_1109,c_37])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(k5_xboole_0(A_10,B_11),k2_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5241,plain,(
    ! [A_151,B_152] : k5_xboole_0(k5_xboole_0(A_151,B_152),k2_xboole_0(B_152,A_151)) = k3_xboole_0(B_152,A_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_10])).

tff(c_342,plain,(
    ! [A_74,B_75] : k5_xboole_0(k5_xboole_0(A_74,B_75),k2_xboole_0(A_74,B_75)) = k3_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_363,plain,(
    ! [A_58,B_57] : k5_xboole_0(k5_xboole_0(A_58,B_57),k2_xboole_0(B_57,A_58)) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_342])).

tff(c_5266,plain,(
    ! [B_152,A_151] : k3_xboole_0(B_152,A_151) = k3_xboole_0(A_151,B_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_5241,c_363])).

tff(c_34,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5432,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5266,c_34])).

tff(c_5506,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_5432])).

tff(c_5510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_5506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:13:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.06/2.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.06/2.51  
% 7.06/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.51  %$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 7.11/2.51  
% 7.11/2.51  %Foreground sorts:
% 7.11/2.51  
% 7.11/2.51  
% 7.11/2.51  %Background operators:
% 7.11/2.51  
% 7.11/2.51  
% 7.11/2.51  %Foreground operators:
% 7.11/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.11/2.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.11/2.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.11/2.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.11/2.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.11/2.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.11/2.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.11/2.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.11/2.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.11/2.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.11/2.51  tff('#skF_2', type, '#skF_2': $i).
% 7.11/2.51  tff('#skF_1', type, '#skF_1': $i).
% 7.11/2.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.11/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.11/2.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.11/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.11/2.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.11/2.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.11/2.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.11/2.51  
% 7.11/2.52  tff(f_56, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.11/2.52  tff(f_67, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 7.11/2.52  tff(f_60, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 7.11/2.52  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.11/2.52  tff(f_62, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.11/2.52  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 7.11/2.52  tff(f_33, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_xboole_1)).
% 7.11/2.52  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.11/2.52  tff(c_89, plain, (![A_50, B_51]: (r1_xboole_0(k1_tarski(A_50), B_51) | r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.11/2.52  tff(c_36, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.11/2.52  tff(c_93, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_89, c_36])).
% 7.11/2.52  tff(c_30, plain, (![B_42, A_41]: (k3_xboole_0(B_42, k1_tarski(A_41))=k1_tarski(A_41) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.11/2.52  tff(c_12, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.11/2.52  tff(c_94, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.11/2.52  tff(c_138, plain, (![B_57, A_58]: (k3_tarski(k2_tarski(B_57, A_58))=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_12, c_94])).
% 7.11/2.52  tff(c_32, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.11/2.52  tff(c_144, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_138, c_32])).
% 7.11/2.52  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.11/2.52  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(k2_xboole_0(A_8, B_9), k3_xboole_0(A_8, B_9))=k2_xboole_0(k4_xboole_0(A_8, B_9), k4_xboole_0(B_9, A_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.11/2.52  tff(c_219, plain, (![A_66, B_67]: (k2_xboole_0(k4_xboole_0(A_66, B_67), k4_xboole_0(B_67, A_66))=k5_xboole_0(A_66, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8])).
% 7.11/2.52  tff(c_1109, plain, (![B_112, A_113]: (k2_xboole_0(k4_xboole_0(B_112, A_113), k4_xboole_0(A_113, B_112))=k5_xboole_0(A_113, B_112))), inference(superposition, [status(thm), theory('equality')], [c_144, c_219])).
% 7.11/2.52  tff(c_37, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), k4_xboole_0(B_9, A_8))=k5_xboole_0(A_8, B_9))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8])).
% 7.11/2.52  tff(c_1186, plain, (![B_114, A_115]: (k5_xboole_0(B_114, A_115)=k5_xboole_0(A_115, B_114))), inference(superposition, [status(thm), theory('equality')], [c_1109, c_37])).
% 7.11/2.52  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(k5_xboole_0(A_10, B_11), k2_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.11/2.52  tff(c_5241, plain, (![A_151, B_152]: (k5_xboole_0(k5_xboole_0(A_151, B_152), k2_xboole_0(B_152, A_151))=k3_xboole_0(B_152, A_151))), inference(superposition, [status(thm), theory('equality')], [c_1186, c_10])).
% 7.11/2.52  tff(c_342, plain, (![A_74, B_75]: (k5_xboole_0(k5_xboole_0(A_74, B_75), k2_xboole_0(A_74, B_75))=k3_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.11/2.52  tff(c_363, plain, (![A_58, B_57]: (k5_xboole_0(k5_xboole_0(A_58, B_57), k2_xboole_0(B_57, A_58))=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_144, c_342])).
% 7.11/2.52  tff(c_5266, plain, (![B_152, A_151]: (k3_xboole_0(B_152, A_151)=k3_xboole_0(A_151, B_152))), inference(superposition, [status(thm), theory('equality')], [c_5241, c_363])).
% 7.11/2.52  tff(c_34, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.11/2.52  tff(c_5432, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5266, c_34])).
% 7.11/2.52  tff(c_5506, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_5432])).
% 7.11/2.52  tff(c_5510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_5506])).
% 7.11/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.52  
% 7.11/2.52  Inference rules
% 7.11/2.52  ----------------------
% 7.11/2.52  #Ref     : 0
% 7.11/2.52  #Sup     : 1477
% 7.11/2.52  #Fact    : 0
% 7.11/2.52  #Define  : 0
% 7.11/2.52  #Split   : 0
% 7.11/2.52  #Chain   : 0
% 7.11/2.52  #Close   : 0
% 7.11/2.52  
% 7.11/2.52  Ordering : KBO
% 7.11/2.52  
% 7.11/2.52  Simplification rules
% 7.11/2.52  ----------------------
% 7.11/2.52  #Subsume      : 149
% 7.11/2.52  #Demod        : 497
% 7.11/2.52  #Tautology    : 261
% 7.11/2.52  #SimpNegUnit  : 0
% 7.11/2.52  #BackRed      : 1
% 7.11/2.52  
% 7.11/2.52  #Partial instantiations: 0
% 7.11/2.52  #Strategies tried      : 1
% 7.11/2.52  
% 7.11/2.52  Timing (in seconds)
% 7.11/2.52  ----------------------
% 7.11/2.53  Preprocessing        : 0.31
% 7.11/2.53  Parsing              : 0.17
% 7.11/2.53  CNF conversion       : 0.02
% 7.11/2.53  Main loop            : 1.44
% 7.11/2.53  Inferencing          : 0.36
% 7.11/2.53  Reduction            : 0.80
% 7.11/2.53  Demodulation         : 0.71
% 7.11/2.53  BG Simplification    : 0.07
% 7.11/2.53  Subsumption          : 0.15
% 7.11/2.53  Abstraction          : 0.09
% 7.11/2.53  MUC search           : 0.00
% 7.11/2.53  Cooper               : 0.00
% 7.11/2.53  Total                : 1.78
% 7.11/2.53  Index Insertion      : 0.00
% 7.11/2.53  Index Deletion       : 0.00
% 7.11/2.53  Index Matching       : 0.00
% 7.11/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
