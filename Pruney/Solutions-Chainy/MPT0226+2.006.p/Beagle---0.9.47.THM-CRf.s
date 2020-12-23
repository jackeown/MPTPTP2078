%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:38 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   55 (  60 expanded)
%              Number of leaves         :   29 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :   47 (  55 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ! [C_23] : r2_hidden(C_23,k1_tarski(C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden(A_3,B_4)
      | ~ r2_hidden(A_3,C_5)
      | r2_hidden(A_3,k5_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_56,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_136,plain,(
    ! [B_48,A_49] : k5_xboole_0(B_48,A_49) = k5_xboole_0(A_49,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_152,plain,(
    ! [A_49] : k5_xboole_0(k1_xboole_0,A_49) = A_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_20])).

tff(c_24,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_410,plain,(
    ! [A_71,B_72,C_73] : k5_xboole_0(k5_xboole_0(A_71,B_72),C_73) = k5_xboole_0(A_71,k5_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_491,plain,(
    ! [A_14,C_73] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_73)) = k5_xboole_0(k1_xboole_0,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_410])).

tff(c_505,plain,(
    ! [A_74,C_75] : k5_xboole_0(A_74,k5_xboole_0(A_74,C_75)) = C_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_491])).

tff(c_1358,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k4_xboole_0(A_114,B_115)) = k3_xboole_0(A_114,B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_505])).

tff(c_1442,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k5_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1358])).

tff(c_1449,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1442])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_183,plain,(
    ! [A_50,B_51] : r1_xboole_0(k3_xboole_0(A_50,B_51),k5_xboole_0(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_186,plain,(
    ! [A_1,B_2] : r1_xboole_0(k3_xboole_0(A_1,B_2),k5_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_183])).

tff(c_1502,plain,(
    r1_xboole_0(k1_tarski('#skF_3'),k5_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1449,c_186])).

tff(c_52,plain,(
    ! [A_38,B_39] :
      ( ~ r2_hidden(A_38,B_39)
      | ~ r1_xboole_0(k1_tarski(A_38),B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2027,plain,(
    ~ r2_hidden('#skF_3',k5_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1502,c_52])).

tff(c_2030,plain,
    ( r2_hidden('#skF_3',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_2027])).

tff(c_2036,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2030])).

tff(c_30,plain,(
    ! [C_23,A_19] :
      ( C_23 = A_19
      | ~ r2_hidden(C_23,k1_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2042,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2036,c_30])).

tff(c_2046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2042])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/2.16  
% 4.45/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/2.16  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.45/2.16  
% 4.45/2.16  %Foreground sorts:
% 4.45/2.16  
% 4.45/2.16  
% 4.45/2.16  %Background operators:
% 4.45/2.16  
% 4.45/2.16  
% 4.45/2.16  %Foreground operators:
% 4.45/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.45/2.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.45/2.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.45/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/2.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.45/2.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.45/2.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.45/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.45/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.45/2.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.45/2.16  tff('#skF_3', type, '#skF_3': $i).
% 4.45/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/2.16  tff('#skF_4', type, '#skF_4': $i).
% 4.45/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/2.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.45/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/2.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.45/2.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.45/2.16  
% 4.45/2.18  tff(f_75, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 4.45/2.18  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.45/2.18  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 4.45/2.18  tff(f_40, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.45/2.18  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.45/2.18  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.45/2.18  tff(f_44, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.45/2.18  tff(f_42, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.45/2.18  tff(f_36, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 4.45/2.18  tff(f_70, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 4.45/2.18  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.45/2.18  tff(c_32, plain, (![C_23]: (r2_hidden(C_23, k1_tarski(C_23)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.45/2.18  tff(c_12, plain, (![A_3, B_4, C_5]: (r2_hidden(A_3, B_4) | ~r2_hidden(A_3, C_5) | r2_hidden(A_3, k5_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.45/2.18  tff(c_20, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.45/2.18  tff(c_56, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.45/2.18  tff(c_18, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.45/2.18  tff(c_136, plain, (![B_48, A_49]: (k5_xboole_0(B_48, A_49)=k5_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/2.18  tff(c_152, plain, (![A_49]: (k5_xboole_0(k1_xboole_0, A_49)=A_49)), inference(superposition, [status(thm), theory('equality')], [c_136, c_20])).
% 4.45/2.18  tff(c_24, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.45/2.18  tff(c_410, plain, (![A_71, B_72, C_73]: (k5_xboole_0(k5_xboole_0(A_71, B_72), C_73)=k5_xboole_0(A_71, k5_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.45/2.18  tff(c_491, plain, (![A_14, C_73]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_73))=k5_xboole_0(k1_xboole_0, C_73))), inference(superposition, [status(thm), theory('equality')], [c_24, c_410])).
% 4.45/2.18  tff(c_505, plain, (![A_74, C_75]: (k5_xboole_0(A_74, k5_xboole_0(A_74, C_75))=C_75)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_491])).
% 4.45/2.18  tff(c_1358, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k4_xboole_0(A_114, B_115))=k3_xboole_0(A_114, B_115))), inference(superposition, [status(thm), theory('equality')], [c_18, c_505])).
% 4.45/2.18  tff(c_1442, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k5_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_1358])).
% 4.45/2.18  tff(c_1449, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1442])).
% 4.45/2.18  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/2.18  tff(c_183, plain, (![A_50, B_51]: (r1_xboole_0(k3_xboole_0(A_50, B_51), k5_xboole_0(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.45/2.18  tff(c_186, plain, (![A_1, B_2]: (r1_xboole_0(k3_xboole_0(A_1, B_2), k5_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_183])).
% 4.45/2.18  tff(c_1502, plain, (r1_xboole_0(k1_tarski('#skF_3'), k5_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1449, c_186])).
% 4.45/2.18  tff(c_52, plain, (![A_38, B_39]: (~r2_hidden(A_38, B_39) | ~r1_xboole_0(k1_tarski(A_38), B_39))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.45/2.18  tff(c_2027, plain, (~r2_hidden('#skF_3', k5_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_1502, c_52])).
% 4.45/2.18  tff(c_2030, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_2027])).
% 4.45/2.18  tff(c_2036, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2030])).
% 4.45/2.18  tff(c_30, plain, (![C_23, A_19]: (C_23=A_19 | ~r2_hidden(C_23, k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.45/2.18  tff(c_2042, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_2036, c_30])).
% 4.45/2.18  tff(c_2046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2042])).
% 4.45/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/2.18  
% 4.45/2.18  Inference rules
% 4.45/2.18  ----------------------
% 4.45/2.18  #Ref     : 0
% 4.45/2.18  #Sup     : 529
% 4.45/2.18  #Fact    : 0
% 4.45/2.18  #Define  : 0
% 4.45/2.18  #Split   : 0
% 4.45/2.18  #Chain   : 0
% 4.45/2.18  #Close   : 0
% 4.45/2.18  
% 4.45/2.18  Ordering : KBO
% 4.45/2.18  
% 4.45/2.18  Simplification rules
% 4.45/2.18  ----------------------
% 4.45/2.18  #Subsume      : 8
% 4.45/2.18  #Demod        : 206
% 4.45/2.18  #Tautology    : 276
% 4.45/2.18  #SimpNegUnit  : 1
% 4.45/2.18  #BackRed      : 1
% 4.45/2.18  
% 4.45/2.18  #Partial instantiations: 0
% 4.45/2.18  #Strategies tried      : 1
% 4.45/2.18  
% 4.45/2.18  Timing (in seconds)
% 4.45/2.18  ----------------------
% 4.45/2.18  Preprocessing        : 0.52
% 4.45/2.18  Parsing              : 0.26
% 4.45/2.18  CNF conversion       : 0.03
% 4.45/2.18  Main loop            : 0.76
% 4.45/2.18  Inferencing          : 0.25
% 4.45/2.18  Reduction            : 0.30
% 4.45/2.18  Demodulation         : 0.25
% 4.45/2.18  BG Simplification    : 0.04
% 4.45/2.18  Subsumption          : 0.11
% 4.45/2.19  Abstraction          : 0.04
% 4.45/2.19  MUC search           : 0.00
% 4.45/2.19  Cooper               : 0.00
% 4.45/2.19  Total                : 1.33
% 4.45/2.19  Index Insertion      : 0.00
% 4.45/2.19  Index Deletion       : 0.00
% 4.45/2.19  Index Matching       : 0.00
% 4.45/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
