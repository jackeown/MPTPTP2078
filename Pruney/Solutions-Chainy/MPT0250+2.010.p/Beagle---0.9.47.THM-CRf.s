%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:33 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   64 (  92 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  87 expanded)
%              Number of equality atoms :   34 (  59 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(c_40,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [B_56,A_57] : k5_xboole_0(B_56,A_57) = k5_xboole_0(A_57,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [A_57] : k5_xboole_0(k1_xboole_0,A_57) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_10])).

tff(c_16,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_444,plain,(
    ! [A_80,B_81,C_82] : k5_xboole_0(k5_xboole_0(A_80,B_81),C_82) = k5_xboole_0(A_80,k5_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_490,plain,(
    ! [A_11,C_82] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_82)) = k5_xboole_0(k1_xboole_0,C_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_444])).

tff(c_511,plain,(
    ! [A_83,C_84] : k5_xboole_0(A_83,k5_xboole_0(A_83,C_84)) = C_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_490])).

tff(c_573,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k5_xboole_0(B_86,A_85)) = B_86 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_511])).

tff(c_551,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_511])).

tff(c_576,plain,(
    ! [B_86,A_85] : k5_xboole_0(k5_xboole_0(B_86,A_85),B_86) = A_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_551])).

tff(c_20,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_220,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_279,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(B_68,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_220])).

tff(c_38,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_335,plain,(
    ! [B_72,A_73] : k2_xboole_0(B_72,A_73) = k2_xboole_0(A_73,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_38])).

tff(c_12,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_285,plain,(
    ! [B_68,A_67] : k2_xboole_0(B_68,A_67) = k2_xboole_0(A_67,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_38])).

tff(c_42,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_238,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ r1_tarski(B_63,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_245,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_238])).

tff(c_305,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_306,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_305])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_306])).

tff(c_311,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_350,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_311])).

tff(c_743,plain,(
    ! [A_89,B_90] : k5_xboole_0(k5_xboole_0(A_89,B_90),k2_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_795,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') = k3_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_743])).

tff(c_834,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_795])).

tff(c_36,plain,(
    ! [B_45,A_44] :
      ( r2_hidden(B_45,A_44)
      | k3_xboole_0(A_44,k1_tarski(B_45)) != k1_tarski(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_896,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_36])).

tff(c_902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_896])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:07:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.38  
% 2.69/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.38  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.69/1.38  
% 2.69/1.38  %Foreground sorts:
% 2.69/1.38  
% 2.69/1.38  
% 2.69/1.38  %Background operators:
% 2.69/1.38  
% 2.69/1.38  
% 2.69/1.38  %Foreground operators:
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.69/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.38  
% 2.69/1.39  tff(f_70, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.69/1.39  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.69/1.39  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.69/1.39  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.69/1.39  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.69/1.39  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.69/1.39  tff(f_65, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.69/1.39  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.69/1.39  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.69/1.39  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.69/1.39  tff(f_63, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.69/1.39  tff(c_40, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.69/1.39  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.39  tff(c_114, plain, (![B_56, A_57]: (k5_xboole_0(B_56, A_57)=k5_xboole_0(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.39  tff(c_10, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.39  tff(c_130, plain, (![A_57]: (k5_xboole_0(k1_xboole_0, A_57)=A_57)), inference(superposition, [status(thm), theory('equality')], [c_114, c_10])).
% 2.69/1.39  tff(c_16, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.69/1.39  tff(c_444, plain, (![A_80, B_81, C_82]: (k5_xboole_0(k5_xboole_0(A_80, B_81), C_82)=k5_xboole_0(A_80, k5_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.39  tff(c_490, plain, (![A_11, C_82]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_82))=k5_xboole_0(k1_xboole_0, C_82))), inference(superposition, [status(thm), theory('equality')], [c_16, c_444])).
% 2.69/1.39  tff(c_511, plain, (![A_83, C_84]: (k5_xboole_0(A_83, k5_xboole_0(A_83, C_84))=C_84)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_490])).
% 2.69/1.39  tff(c_573, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k5_xboole_0(B_86, A_85))=B_86)), inference(superposition, [status(thm), theory('equality')], [c_2, c_511])).
% 2.69/1.39  tff(c_551, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_511])).
% 2.69/1.39  tff(c_576, plain, (![B_86, A_85]: (k5_xboole_0(k5_xboole_0(B_86, A_85), B_86)=A_85)), inference(superposition, [status(thm), theory('equality')], [c_573, c_551])).
% 2.69/1.39  tff(c_20, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.39  tff(c_220, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.69/1.39  tff(c_279, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(B_68, A_67))), inference(superposition, [status(thm), theory('equality')], [c_20, c_220])).
% 2.69/1.39  tff(c_38, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.69/1.39  tff(c_335, plain, (![B_72, A_73]: (k2_xboole_0(B_72, A_73)=k2_xboole_0(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_279, c_38])).
% 2.69/1.39  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.39  tff(c_285, plain, (![B_68, A_67]: (k2_xboole_0(B_68, A_67)=k2_xboole_0(A_67, B_68))), inference(superposition, [status(thm), theory('equality')], [c_279, c_38])).
% 2.69/1.39  tff(c_42, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.69/1.39  tff(c_238, plain, (![B_63, A_64]: (B_63=A_64 | ~r1_tarski(B_63, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.39  tff(c_245, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_238])).
% 2.69/1.39  tff(c_305, plain, (~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_245])).
% 2.69/1.39  tff(c_306, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_305])).
% 2.69/1.39  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_306])).
% 2.69/1.39  tff(c_311, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_245])).
% 2.69/1.39  tff(c_350, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_335, c_311])).
% 2.69/1.39  tff(c_743, plain, (![A_89, B_90]: (k5_xboole_0(k5_xboole_0(A_89, B_90), k2_xboole_0(A_89, B_90))=k3_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.69/1.39  tff(c_795, plain, (k5_xboole_0(k5_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')=k3_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_350, c_743])).
% 2.69/1.39  tff(c_834, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_576, c_795])).
% 2.69/1.39  tff(c_36, plain, (![B_45, A_44]: (r2_hidden(B_45, A_44) | k3_xboole_0(A_44, k1_tarski(B_45))!=k1_tarski(B_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.69/1.39  tff(c_896, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_834, c_36])).
% 2.69/1.39  tff(c_902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_896])).
% 2.69/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  
% 2.69/1.39  Inference rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Ref     : 0
% 2.69/1.39  #Sup     : 216
% 2.69/1.39  #Fact    : 0
% 2.69/1.39  #Define  : 0
% 2.69/1.39  #Split   : 2
% 2.69/1.39  #Chain   : 0
% 2.69/1.39  #Close   : 0
% 2.69/1.39  
% 2.69/1.39  Ordering : KBO
% 2.69/1.39  
% 2.69/1.39  Simplification rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Subsume      : 9
% 2.69/1.39  #Demod        : 95
% 2.69/1.39  #Tautology    : 140
% 2.69/1.39  #SimpNegUnit  : 1
% 2.69/1.39  #BackRed      : 3
% 2.69/1.39  
% 2.69/1.39  #Partial instantiations: 0
% 2.69/1.39  #Strategies tried      : 1
% 2.69/1.39  
% 2.69/1.39  Timing (in seconds)
% 2.69/1.39  ----------------------
% 2.69/1.39  Preprocessing        : 0.32
% 2.69/1.39  Parsing              : 0.17
% 2.69/1.39  CNF conversion       : 0.02
% 2.69/1.39  Main loop            : 0.30
% 2.69/1.39  Inferencing          : 0.10
% 2.69/1.39  Reduction            : 0.12
% 2.69/1.39  Demodulation         : 0.10
% 2.69/1.39  BG Simplification    : 0.02
% 2.69/1.39  Subsumption          : 0.05
% 2.69/1.39  Abstraction          : 0.02
% 2.69/1.39  MUC search           : 0.00
% 2.69/1.39  Cooper               : 0.00
% 2.69/1.39  Total                : 0.64
% 2.69/1.39  Index Insertion      : 0.00
% 2.69/1.39  Index Deletion       : 0.00
% 2.69/1.39  Index Matching       : 0.00
% 2.69/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
