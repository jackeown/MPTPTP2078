%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:54 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   59 (  90 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :   43 (  75 expanded)
%              Number of equality atoms :   37 (  69 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_34,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [B_51,A_52] : k5_xboole_0(B_51,A_52) = k5_xboole_0(A_52,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    ! [A_52] : k5_xboole_0(k1_xboole_0,A_52) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_8])).

tff(c_357,plain,(
    ! [A_71,B_72,C_73] : k5_xboole_0(k5_xboole_0(A_71,B_72),C_73) = k5_xboole_0(A_71,k5_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_443,plain,(
    ! [A_13,C_73] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_73)) = k5_xboole_0(k1_xboole_0,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_357])).

tff(c_457,plain,(
    ! [A_74,C_75] : k5_xboole_0(A_74,k5_xboole_0(A_74,C_75)) = C_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_443])).

tff(c_1055,plain,(
    ! [A_110,B_111] : k5_xboole_0(A_110,k2_xboole_0(A_110,B_111)) = k4_xboole_0(B_111,A_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_457])).

tff(c_1091,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1055])).

tff(c_1100,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1091])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_493,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_457])).

tff(c_1105,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1100,c_493])).

tff(c_1114,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1105])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_256,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_272,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_256])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_556,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k5_xboole_0(B_78,A_77)) = B_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_457])).

tff(c_2441,plain,(
    ! [A_130,B_131] : k5_xboole_0(k3_xboole_0(A_130,B_131),k4_xboole_0(B_131,A_130)) = B_131 ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_556])).

tff(c_2491,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_2441])).

tff(c_3379,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2491,c_16])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3399,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3379,c_10])).

tff(c_32,plain,(
    ! [B_45,A_44] :
      ( B_45 = A_44
      | ~ r1_tarski(k1_tarski(A_44),k1_tarski(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3405,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3399,c_32])).

tff(c_3409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3405])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:02:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.81  
% 4.32/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.81  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.32/1.81  
% 4.32/1.81  %Foreground sorts:
% 4.32/1.81  
% 4.32/1.81  
% 4.32/1.81  %Background operators:
% 4.32/1.81  
% 4.32/1.81  
% 4.32/1.81  %Foreground operators:
% 4.32/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.32/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.32/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.32/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.32/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.32/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.32/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.32/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.32/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.32/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.32/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.32/1.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.32/1.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.32/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.32/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.32/1.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.32/1.81  
% 4.56/1.82  tff(f_64, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 4.56/1.82  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.56/1.82  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.56/1.82  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.56/1.82  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.56/1.82  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.56/1.82  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.56/1.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.56/1.82  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.56/1.82  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 4.56/1.82  tff(c_34, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.56/1.82  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.56/1.82  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.56/1.82  tff(c_36, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.56/1.82  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.56/1.82  tff(c_73, plain, (![B_51, A_52]: (k5_xboole_0(B_51, A_52)=k5_xboole_0(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.56/1.82  tff(c_89, plain, (![A_52]: (k5_xboole_0(k1_xboole_0, A_52)=A_52)), inference(superposition, [status(thm), theory('equality')], [c_73, c_8])).
% 4.56/1.82  tff(c_357, plain, (![A_71, B_72, C_73]: (k5_xboole_0(k5_xboole_0(A_71, B_72), C_73)=k5_xboole_0(A_71, k5_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.56/1.82  tff(c_443, plain, (![A_13, C_73]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_73))=k5_xboole_0(k1_xboole_0, C_73))), inference(superposition, [status(thm), theory('equality')], [c_14, c_357])).
% 4.56/1.82  tff(c_457, plain, (![A_74, C_75]: (k5_xboole_0(A_74, k5_xboole_0(A_74, C_75))=C_75)), inference(demodulation, [status(thm), theory('equality')], [c_89, c_443])).
% 4.56/1.82  tff(c_1055, plain, (![A_110, B_111]: (k5_xboole_0(A_110, k2_xboole_0(A_110, B_111))=k4_xboole_0(B_111, A_110))), inference(superposition, [status(thm), theory('equality')], [c_16, c_457])).
% 4.56/1.82  tff(c_1091, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1055])).
% 4.56/1.82  tff(c_1100, plain, (k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1091])).
% 4.56/1.82  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.56/1.82  tff(c_493, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_457])).
% 4.56/1.82  tff(c_1105, plain, (k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1100, c_493])).
% 4.56/1.82  tff(c_1114, plain, (k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1105])).
% 4.56/1.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.56/1.82  tff(c_256, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.56/1.82  tff(c_272, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_256])).
% 4.56/1.82  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.56/1.82  tff(c_556, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k5_xboole_0(B_78, A_77))=B_78)), inference(superposition, [status(thm), theory('equality')], [c_4, c_457])).
% 4.56/1.82  tff(c_2441, plain, (![A_130, B_131]: (k5_xboole_0(k3_xboole_0(A_130, B_131), k4_xboole_0(B_131, A_130))=B_131)), inference(superposition, [status(thm), theory('equality')], [c_272, c_556])).
% 4.56/1.82  tff(c_2491, plain, (k5_xboole_0(k1_tarski('#skF_2'), k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1114, c_2441])).
% 4.56/1.82  tff(c_3379, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2491, c_16])).
% 4.56/1.82  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.56/1.82  tff(c_3399, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3379, c_10])).
% 4.56/1.82  tff(c_32, plain, (![B_45, A_44]: (B_45=A_44 | ~r1_tarski(k1_tarski(A_44), k1_tarski(B_45)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.56/1.82  tff(c_3405, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_3399, c_32])).
% 4.56/1.82  tff(c_3409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_3405])).
% 4.56/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.82  
% 4.56/1.82  Inference rules
% 4.56/1.82  ----------------------
% 4.56/1.82  #Ref     : 0
% 4.56/1.82  #Sup     : 873
% 4.56/1.82  #Fact    : 0
% 4.56/1.82  #Define  : 0
% 4.56/1.82  #Split   : 0
% 4.56/1.82  #Chain   : 0
% 4.56/1.82  #Close   : 0
% 4.56/1.82  
% 4.56/1.82  Ordering : KBO
% 4.56/1.82  
% 4.56/1.82  Simplification rules
% 4.56/1.82  ----------------------
% 4.56/1.82  #Subsume      : 39
% 4.56/1.82  #Demod        : 627
% 4.56/1.82  #Tautology    : 439
% 4.56/1.82  #SimpNegUnit  : 1
% 4.56/1.82  #BackRed      : 0
% 4.56/1.82  
% 4.56/1.82  #Partial instantiations: 0
% 4.56/1.82  #Strategies tried      : 1
% 4.56/1.82  
% 4.56/1.82  Timing (in seconds)
% 4.56/1.82  ----------------------
% 4.56/1.82  Preprocessing        : 0.31
% 4.56/1.82  Parsing              : 0.17
% 4.56/1.83  CNF conversion       : 0.02
% 4.56/1.83  Main loop            : 0.74
% 4.56/1.83  Inferencing          : 0.22
% 4.56/1.83  Reduction            : 0.35
% 4.56/1.83  Demodulation         : 0.30
% 4.56/1.83  BG Simplification    : 0.04
% 4.56/1.83  Subsumption          : 0.09
% 4.56/1.83  Abstraction          : 0.04
% 4.56/1.83  MUC search           : 0.00
% 4.56/1.83  Cooper               : 0.00
% 4.56/1.83  Total                : 1.09
% 4.56/1.83  Index Insertion      : 0.00
% 4.56/1.83  Index Deletion       : 0.00
% 4.56/1.83  Index Matching       : 0.00
% 4.56/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
