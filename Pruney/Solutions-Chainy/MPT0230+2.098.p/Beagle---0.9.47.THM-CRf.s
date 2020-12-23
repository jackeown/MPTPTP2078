%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:08 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   75 (  99 expanded)
%              Number of leaves         :   35 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 138 expanded)
%              Number of equality atoms :   43 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_81,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(c_66,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_108,plain,(
    ! [D_45,A_46] : r2_hidden(D_45,k2_tarski(A_46,D_45)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_111,plain,(
    ! [A_32] : r2_hidden(A_32,k1_tarski(A_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_108])).

tff(c_14,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_182,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(A_73,B_74) = k1_xboole_0
      | ~ r1_xboole_0(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_293,plain,(
    ! [A_90,B_91] :
      ( k3_xboole_0(A_90,B_91) = k1_xboole_0
      | k4_xboole_0(A_90,B_91) != A_90 ) ),
    inference(resolution,[status(thm)],[c_22,c_182])).

tff(c_303,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_293])).

tff(c_195,plain,(
    ! [A_75,B_76] : k4_xboole_0(A_75,k4_xboole_0(A_75,B_76)) = k3_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_210,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_195])).

tff(c_327,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_210])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_335,plain,(
    ! [A_93] : k4_xboole_0(A_93,k1_xboole_0) = k3_xboole_0(A_93,A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_16])).

tff(c_347,plain,(
    ! [A_93] : k3_xboole_0(A_93,A_93) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_335])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    ! [A_65,B_66] :
      ( ~ r2_hidden(A_65,B_66)
      | ~ r1_xboole_0(k1_tarski(A_65),B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_484,plain,(
    ! [A_107,B_108] :
      ( ~ r2_hidden(A_107,B_108)
      | k3_xboole_0(k1_tarski(A_107),B_108) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_488,plain,(
    ! [A_107] :
      ( ~ r2_hidden(A_107,k1_tarski(A_107))
      | k1_tarski(A_107) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_484])).

tff(c_497,plain,(
    ! [A_107] : k1_tarski(A_107) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_488])).

tff(c_78,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_76,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_74,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(k1_tarski(A_40),B_41)
      | r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_194,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(k1_tarski(A_40),B_41) = k1_xboole_0
      | r2_hidden(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_74,c_182])).

tff(c_80,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,k2_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_421,plain,(
    ! [A_100,B_101,C_102] :
      ( r1_tarski(A_100,B_101)
      | ~ r1_xboole_0(A_100,C_102)
      | ~ r1_tarski(A_100,k2_xboole_0(B_101,C_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_622,plain,(
    ! [A_120,C_121,B_122] :
      ( r1_tarski(A_120,C_121)
      | ~ r1_xboole_0(A_120,B_122)
      | ~ r1_tarski(A_120,B_122) ) ),
    inference(resolution,[status(thm)],[c_8,c_421])).

tff(c_709,plain,(
    ! [A_130,C_131,B_132] :
      ( r1_tarski(A_130,C_131)
      | ~ r1_tarski(A_130,B_132)
      | k3_xboole_0(A_130,B_132) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_622])).

tff(c_715,plain,(
    ! [C_131] :
      ( r1_tarski(k1_tarski('#skF_5'),C_131)
      | k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80,c_709])).

tff(c_723,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_715])).

tff(c_727,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_723])).

tff(c_48,plain,(
    ! [D_31,B_27,A_26] :
      ( D_31 = B_27
      | D_31 = A_26
      | ~ r2_hidden(D_31,k2_tarski(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_730,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_727,c_48])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_76,c_730])).

tff(c_738,plain,(
    ! [C_136] : r1_tarski(k1_tarski('#skF_5'),C_136) ),
    inference(splitRight,[status(thm)],[c_715])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_763,plain,(
    ! [C_137] : k2_xboole_0(k1_tarski('#skF_5'),C_137) = C_137 ),
    inference(resolution,[status(thm)],[c_738,c_10])).

tff(c_12,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_776,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_12])).

tff(c_786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.48  
% 2.99/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 2.99/1.48  
% 2.99/1.48  %Foreground sorts:
% 2.99/1.48  
% 2.99/1.48  
% 2.99/1.48  %Background operators:
% 2.99/1.48  
% 2.99/1.48  
% 2.99/1.48  %Foreground operators:
% 2.99/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.99/1.48  tff('#skF_7', type, '#skF_7': $i).
% 2.99/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.99/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.99/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.99/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.99/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.99/1.48  
% 3.03/1.49  tff(f_81, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.03/1.49  tff(f_79, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.03/1.49  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.03/1.49  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.03/1.49  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.03/1.49  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.03/1.49  tff(f_90, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.03/1.49  tff(f_105, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.03/1.49  tff(f_95, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.03/1.49  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.03/1.49  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 3.03/1.49  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.03/1.49  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.03/1.49  tff(c_66, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.03/1.49  tff(c_108, plain, (![D_45, A_46]: (r2_hidden(D_45, k2_tarski(A_46, D_45)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.03/1.49  tff(c_111, plain, (![A_32]: (r2_hidden(A_32, k1_tarski(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_108])).
% 3.03/1.49  tff(c_14, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.03/1.49  tff(c_22, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.03/1.49  tff(c_182, plain, (![A_73, B_74]: (k3_xboole_0(A_73, B_74)=k1_xboole_0 | ~r1_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.03/1.49  tff(c_293, plain, (![A_90, B_91]: (k3_xboole_0(A_90, B_91)=k1_xboole_0 | k4_xboole_0(A_90, B_91)!=A_90)), inference(resolution, [status(thm)], [c_22, c_182])).
% 3.03/1.49  tff(c_303, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_293])).
% 3.03/1.49  tff(c_195, plain, (![A_75, B_76]: (k4_xboole_0(A_75, k4_xboole_0(A_75, B_76))=k3_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.03/1.49  tff(c_210, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_195])).
% 3.03/1.49  tff(c_327, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_303, c_210])).
% 3.03/1.49  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.03/1.49  tff(c_335, plain, (![A_93]: (k4_xboole_0(A_93, k1_xboole_0)=k3_xboole_0(A_93, A_93))), inference(superposition, [status(thm), theory('equality')], [c_327, c_16])).
% 3.03/1.49  tff(c_347, plain, (![A_93]: (k3_xboole_0(A_93, A_93)=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_335])).
% 3.03/1.49  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.03/1.49  tff(c_128, plain, (![A_65, B_66]: (~r2_hidden(A_65, B_66) | ~r1_xboole_0(k1_tarski(A_65), B_66))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.03/1.49  tff(c_484, plain, (![A_107, B_108]: (~r2_hidden(A_107, B_108) | k3_xboole_0(k1_tarski(A_107), B_108)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_128])).
% 3.03/1.49  tff(c_488, plain, (![A_107]: (~r2_hidden(A_107, k1_tarski(A_107)) | k1_tarski(A_107)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_347, c_484])).
% 3.03/1.49  tff(c_497, plain, (![A_107]: (k1_tarski(A_107)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_488])).
% 3.03/1.49  tff(c_78, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.03/1.49  tff(c_76, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.03/1.49  tff(c_74, plain, (![A_40, B_41]: (r1_xboole_0(k1_tarski(A_40), B_41) | r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.03/1.49  tff(c_194, plain, (![A_40, B_41]: (k3_xboole_0(k1_tarski(A_40), B_41)=k1_xboole_0 | r2_hidden(A_40, B_41))), inference(resolution, [status(thm)], [c_74, c_182])).
% 3.03/1.49  tff(c_80, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.03/1.49  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, k2_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.03/1.49  tff(c_421, plain, (![A_100, B_101, C_102]: (r1_tarski(A_100, B_101) | ~r1_xboole_0(A_100, C_102) | ~r1_tarski(A_100, k2_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.03/1.49  tff(c_622, plain, (![A_120, C_121, B_122]: (r1_tarski(A_120, C_121) | ~r1_xboole_0(A_120, B_122) | ~r1_tarski(A_120, B_122))), inference(resolution, [status(thm)], [c_8, c_421])).
% 3.03/1.49  tff(c_709, plain, (![A_130, C_131, B_132]: (r1_tarski(A_130, C_131) | ~r1_tarski(A_130, B_132) | k3_xboole_0(A_130, B_132)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_622])).
% 3.03/1.49  tff(c_715, plain, (![C_131]: (r1_tarski(k1_tarski('#skF_5'), C_131) | k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_709])).
% 3.03/1.49  tff(c_723, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_715])).
% 3.03/1.49  tff(c_727, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_194, c_723])).
% 3.03/1.49  tff(c_48, plain, (![D_31, B_27, A_26]: (D_31=B_27 | D_31=A_26 | ~r2_hidden(D_31, k2_tarski(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.03/1.49  tff(c_730, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_727, c_48])).
% 3.03/1.49  tff(c_734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_76, c_730])).
% 3.03/1.49  tff(c_738, plain, (![C_136]: (r1_tarski(k1_tarski('#skF_5'), C_136))), inference(splitRight, [status(thm)], [c_715])).
% 3.03/1.49  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.03/1.49  tff(c_763, plain, (![C_137]: (k2_xboole_0(k1_tarski('#skF_5'), C_137)=C_137)), inference(resolution, [status(thm)], [c_738, c_10])).
% 3.03/1.49  tff(c_12, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.03/1.49  tff(c_776, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_763, c_12])).
% 3.03/1.49  tff(c_786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_497, c_776])).
% 3.03/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.49  
% 3.03/1.49  Inference rules
% 3.03/1.49  ----------------------
% 3.03/1.49  #Ref     : 0
% 3.03/1.49  #Sup     : 160
% 3.03/1.49  #Fact    : 0
% 3.03/1.49  #Define  : 0
% 3.03/1.49  #Split   : 1
% 3.03/1.49  #Chain   : 0
% 3.03/1.49  #Close   : 0
% 3.03/1.49  
% 3.03/1.49  Ordering : KBO
% 3.03/1.49  
% 3.03/1.49  Simplification rules
% 3.03/1.49  ----------------------
% 3.03/1.49  #Subsume      : 10
% 3.03/1.49  #Demod        : 50
% 3.03/1.49  #Tautology    : 98
% 3.03/1.49  #SimpNegUnit  : 6
% 3.03/1.49  #BackRed      : 1
% 3.03/1.49  
% 3.03/1.49  #Partial instantiations: 0
% 3.03/1.49  #Strategies tried      : 1
% 3.03/1.49  
% 3.03/1.49  Timing (in seconds)
% 3.03/1.49  ----------------------
% 3.03/1.50  Preprocessing        : 0.36
% 3.03/1.50  Parsing              : 0.19
% 3.03/1.50  CNF conversion       : 0.03
% 3.03/1.50  Main loop            : 0.30
% 3.03/1.50  Inferencing          : 0.10
% 3.03/1.50  Reduction            : 0.10
% 3.03/1.50  Demodulation         : 0.07
% 3.03/1.50  BG Simplification    : 0.02
% 3.03/1.50  Subsumption          : 0.06
% 3.03/1.50  Abstraction          : 0.02
% 3.03/1.50  MUC search           : 0.00
% 3.03/1.50  Cooper               : 0.00
% 3.03/1.50  Total                : 0.70
% 3.03/1.50  Index Insertion      : 0.00
% 3.03/1.50  Index Deletion       : 0.00
% 3.03/1.50  Index Matching       : 0.00
% 3.03/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
