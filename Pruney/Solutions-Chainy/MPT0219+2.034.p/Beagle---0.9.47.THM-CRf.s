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
% DateTime   : Thu Dec  3 09:47:54 EST 2020

% Result     : Theorem 7.36s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :   53 (  61 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 (  63 expanded)
%              Number of equality atoms :   39 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_36,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_170,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = k1_xboole_0
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_182,plain,(
    ! [A_13,B_14] : k3_xboole_0(k4_xboole_0(A_13,B_14),B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_170])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_183,plain,(
    ! [A_56,B_57] : k3_xboole_0(k4_xboole_0(A_56,B_57),B_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_170])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_188,plain,(
    ! [B_57,A_56] : k3_xboole_0(B_57,k4_xboole_0(A_56,B_57)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_2])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_147,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = A_48
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_251,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,B_67) = A_66
      | k3_xboole_0(A_66,B_67) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_147])).

tff(c_24,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1967,plain,(
    ! [B_120,A_121] :
      ( k5_xboole_0(B_120,A_121) = k2_xboole_0(B_120,A_121)
      | k3_xboole_0(A_121,B_120) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_24])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2658,plain,(
    ! [A_144,B_145] :
      ( k5_xboole_0(A_144,B_145) = k2_xboole_0(B_145,A_144)
      | k3_xboole_0(A_144,B_145) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1967,c_4])).

tff(c_2729,plain,(
    ! [B_18,A_144] :
      ( k2_xboole_0(k4_xboole_0(B_18,A_144),A_144) = k2_xboole_0(A_144,B_18)
      | k3_xboole_0(A_144,k4_xboole_0(B_18,A_144)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2658,c_24])).

tff(c_2830,plain,(
    ! [B_147,A_148] : k2_xboole_0(k4_xboole_0(B_147,A_148),A_148) = k2_xboole_0(A_148,B_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_2729])).

tff(c_16,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11971,plain,(
    ! [B_239,A_240] : k3_xboole_0(k4_xboole_0(B_239,A_240),k2_xboole_0(A_240,B_239)) = k4_xboole_0(B_239,A_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_2830,c_16])).

tff(c_12152,plain,(
    k3_xboole_0(k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')),k1_tarski('#skF_1')) = k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_11971])).

tff(c_12208,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_12152])).

tff(c_161,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | k4_xboole_0(A_52,B_53) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [B_30,A_29] :
      ( B_30 = A_29
      | ~ r1_tarski(k1_tarski(A_29),k1_tarski(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_168,plain,(
    ! [B_30,A_29] :
      ( B_30 = A_29
      | k4_xboole_0(k1_tarski(A_29),k1_tarski(B_30)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_161,c_34])).

tff(c_12550,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12208,c_168])).

tff(c_12582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_12550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:23:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.36/2.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/2.81  
% 7.36/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/2.82  %$ r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.36/2.82  
% 7.36/2.82  %Foreground sorts:
% 7.36/2.82  
% 7.36/2.82  
% 7.36/2.82  %Background operators:
% 7.36/2.82  
% 7.36/2.82  
% 7.36/2.82  %Foreground operators:
% 7.36/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.36/2.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.36/2.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.36/2.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.36/2.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.36/2.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.36/2.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.36/2.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.36/2.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.36/2.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.36/2.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.36/2.82  tff('#skF_2', type, '#skF_2': $i).
% 7.36/2.82  tff('#skF_1', type, '#skF_1': $i).
% 7.36/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.36/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.36/2.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.36/2.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.36/2.82  
% 7.54/2.83  tff(f_66, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 7.54/2.83  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.54/2.83  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.54/2.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.54/2.83  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.54/2.83  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.54/2.83  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.54/2.83  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 7.54/2.83  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.54/2.83  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 7.54/2.83  tff(c_36, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.54/2.83  tff(c_18, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.54/2.83  tff(c_170, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=k1_xboole_0 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.54/2.83  tff(c_182, plain, (![A_13, B_14]: (k3_xboole_0(k4_xboole_0(A_13, B_14), B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_170])).
% 7.54/2.83  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.54/2.83  tff(c_183, plain, (![A_56, B_57]: (k3_xboole_0(k4_xboole_0(A_56, B_57), B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_170])).
% 7.54/2.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.54/2.83  tff(c_188, plain, (![B_57, A_56]: (k3_xboole_0(B_57, k4_xboole_0(A_56, B_57))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_183, c_2])).
% 7.54/2.83  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.54/2.83  tff(c_147, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=A_48 | ~r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.54/2.83  tff(c_251, plain, (![A_66, B_67]: (k4_xboole_0(A_66, B_67)=A_66 | k3_xboole_0(A_66, B_67)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_147])).
% 7.54/2.83  tff(c_24, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.54/2.83  tff(c_1967, plain, (![B_120, A_121]: (k5_xboole_0(B_120, A_121)=k2_xboole_0(B_120, A_121) | k3_xboole_0(A_121, B_120)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_251, c_24])).
% 7.54/2.83  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.54/2.83  tff(c_2658, plain, (![A_144, B_145]: (k5_xboole_0(A_144, B_145)=k2_xboole_0(B_145, A_144) | k3_xboole_0(A_144, B_145)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1967, c_4])).
% 7.54/2.83  tff(c_2729, plain, (![B_18, A_144]: (k2_xboole_0(k4_xboole_0(B_18, A_144), A_144)=k2_xboole_0(A_144, B_18) | k3_xboole_0(A_144, k4_xboole_0(B_18, A_144))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2658, c_24])).
% 7.54/2.83  tff(c_2830, plain, (![B_147, A_148]: (k2_xboole_0(k4_xboole_0(B_147, A_148), A_148)=k2_xboole_0(A_148, B_147))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_2729])).
% 7.54/2.83  tff(c_16, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.54/2.83  tff(c_11971, plain, (![B_239, A_240]: (k3_xboole_0(k4_xboole_0(B_239, A_240), k2_xboole_0(A_240, B_239))=k4_xboole_0(B_239, A_240))), inference(superposition, [status(thm), theory('equality')], [c_2830, c_16])).
% 7.54/2.83  tff(c_12152, plain, (k3_xboole_0(k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1')), k1_tarski('#skF_1'))=k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_11971])).
% 7.54/2.83  tff(c_12208, plain, (k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_182, c_12152])).
% 7.54/2.83  tff(c_161, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | k4_xboole_0(A_52, B_53)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.54/2.83  tff(c_34, plain, (![B_30, A_29]: (B_30=A_29 | ~r1_tarski(k1_tarski(A_29), k1_tarski(B_30)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.54/2.83  tff(c_168, plain, (![B_30, A_29]: (B_30=A_29 | k4_xboole_0(k1_tarski(A_29), k1_tarski(B_30))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_161, c_34])).
% 7.54/2.83  tff(c_12550, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12208, c_168])).
% 7.54/2.83  tff(c_12582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_12550])).
% 7.54/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.54/2.83  
% 7.54/2.83  Inference rules
% 7.54/2.83  ----------------------
% 7.54/2.83  #Ref     : 0
% 7.54/2.83  #Sup     : 2929
% 7.54/2.83  #Fact    : 0
% 7.54/2.83  #Define  : 0
% 7.54/2.83  #Split   : 1
% 7.54/2.83  #Chain   : 0
% 7.54/2.83  #Close   : 0
% 7.54/2.83  
% 7.54/2.83  Ordering : KBO
% 7.54/2.83  
% 7.54/2.83  Simplification rules
% 7.54/2.83  ----------------------
% 7.54/2.83  #Subsume      : 440
% 7.54/2.83  #Demod        : 3166
% 7.54/2.83  #Tautology    : 1826
% 7.54/2.83  #SimpNegUnit  : 19
% 7.54/2.83  #BackRed      : 18
% 7.54/2.83  
% 7.54/2.83  #Partial instantiations: 0
% 7.54/2.83  #Strategies tried      : 1
% 7.54/2.83  
% 7.54/2.83  Timing (in seconds)
% 7.54/2.83  ----------------------
% 7.54/2.83  Preprocessing        : 0.29
% 7.54/2.83  Parsing              : 0.16
% 7.54/2.83  CNF conversion       : 0.02
% 7.54/2.83  Main loop            : 1.77
% 7.54/2.83  Inferencing          : 0.43
% 7.54/2.83  Reduction            : 0.92
% 7.54/2.83  Demodulation         : 0.79
% 7.54/2.83  BG Simplification    : 0.04
% 7.54/2.83  Subsumption          : 0.27
% 7.54/2.83  Abstraction          : 0.07
% 7.54/2.83  MUC search           : 0.00
% 7.54/2.83  Cooper               : 0.00
% 7.54/2.83  Total                : 2.09
% 7.54/2.83  Index Insertion      : 0.00
% 7.54/2.83  Index Deletion       : 0.00
% 7.54/2.83  Index Matching       : 0.00
% 7.54/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
