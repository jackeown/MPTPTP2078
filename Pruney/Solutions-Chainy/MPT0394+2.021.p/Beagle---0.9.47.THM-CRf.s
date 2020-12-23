%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:23 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 117 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :   67 ( 151 expanded)
%              Number of equality atoms :   52 ( 110 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_81,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_42,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_125,plain,(
    ! [A_54,B_55] : k1_enumset1(A_54,A_54,B_55) = k2_tarski(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [E_14,A_8,B_9] : r2_hidden(E_14,k1_enumset1(A_8,B_9,E_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_143,plain,(
    ! [B_56,A_57] : r2_hidden(B_56,k2_tarski(A_57,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_16])).

tff(c_146,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_143])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = A_49
      | ~ r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = A_1
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_174,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_315,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k3_xboole_0(A_87,k4_xboole_0(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_8])).

tff(c_344,plain,(
    ! [A_89] : k3_xboole_0(A_89,k4_xboole_0(A_89,k1_xboole_0)) = k4_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_315])).

tff(c_361,plain,(
    ! [A_1] :
      ( k4_xboole_0(A_1,k1_xboole_0) = k3_xboole_0(A_1,A_1)
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_344])).

tff(c_367,plain,(
    ! [A_90] : k4_xboole_0(A_90,k1_xboole_0) = k3_xboole_0(A_90,A_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_361])).

tff(c_385,plain,(
    ! [A_90] :
      ( k3_xboole_0(A_90,A_90) = A_90
      | k3_xboole_0(A_90,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_95])).

tff(c_417,plain,(
    ! [A_91] : k3_xboole_0(A_91,A_91) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_385])).

tff(c_148,plain,(
    ! [A_59,B_60] :
      ( ~ r2_hidden(A_59,B_60)
      | ~ r1_xboole_0(k1_tarski(A_59),B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_153,plain,(
    ! [A_59,B_2] :
      ( ~ r2_hidden(A_59,B_2)
      | k3_xboole_0(k1_tarski(A_59),B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_148])).

tff(c_427,plain,(
    ! [A_59] :
      ( ~ r2_hidden(A_59,k1_tarski(A_59))
      | k1_tarski(A_59) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_153])).

tff(c_441,plain,(
    ! [A_59] : k1_tarski(A_59) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_427])).

tff(c_54,plain,(
    ! [A_32] : k1_setfam_1(k1_tarski(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),k1_tarski(B_16)) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_507,plain,(
    ! [A_98,B_99] :
      ( k3_xboole_0(k1_setfam_1(A_98),k1_setfam_1(B_99)) = k1_setfam_1(k2_xboole_0(A_98,B_99))
      | k1_xboole_0 = B_99
      | k1_xboole_0 = A_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_527,plain,(
    ! [A_32,B_99] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_32),B_99)) = k3_xboole_0(A_32,k1_setfam_1(B_99))
      | k1_xboole_0 = B_99
      | k1_tarski(A_32) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_507])).

tff(c_812,plain,(
    ! [A_134,B_135] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_134),B_135)) = k3_xboole_0(A_134,k1_setfam_1(B_135))
      | k1_xboole_0 = B_135 ) ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_527])).

tff(c_838,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,k1_setfam_1(k1_tarski(B_16))) = k1_setfam_1(k2_tarski(A_15,B_16))
      | k1_tarski(B_16) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_812])).

tff(c_849,plain,(
    ! [A_15,B_16] :
      ( k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(A_15,B_16)
      | k1_tarski(B_16) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_838])).

tff(c_850,plain,(
    ! [A_15,B_16] : k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_849])).

tff(c_56,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.44  
% 2.76/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.45  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.76/1.45  
% 2.76/1.45  %Foreground sorts:
% 2.76/1.45  
% 2.76/1.45  
% 2.76/1.45  %Background operators:
% 2.76/1.45  
% 2.76/1.45  
% 2.76/1.45  %Foreground operators:
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.76/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.76/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.76/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.76/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.76/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.76/1.45  
% 2.84/1.46  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.84/1.46  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.84/1.46  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.84/1.46  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.84/1.46  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.84/1.46  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.84/1.46  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.84/1.46  tff(f_67, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.84/1.46  tff(f_81, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.84/1.46  tff(f_54, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.84/1.46  tff(f_79, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.84/1.46  tff(f_84, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.84/1.46  tff(c_42, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.84/1.46  tff(c_125, plain, (![A_54, B_55]: (k1_enumset1(A_54, A_54, B_55)=k2_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.84/1.46  tff(c_16, plain, (![E_14, A_8, B_9]: (r2_hidden(E_14, k1_enumset1(A_8, B_9, E_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.84/1.46  tff(c_143, plain, (![B_56, A_57]: (r2_hidden(B_56, k2_tarski(A_57, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_16])).
% 2.84/1.46  tff(c_146, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_143])).
% 2.84/1.46  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.46  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.84/1.46  tff(c_91, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=A_49 | ~r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.46  tff(c_95, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_91])).
% 2.84/1.46  tff(c_174, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.46  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.46  tff(c_315, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k3_xboole_0(A_87, k4_xboole_0(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_174, c_8])).
% 2.84/1.46  tff(c_344, plain, (![A_89]: (k3_xboole_0(A_89, k4_xboole_0(A_89, k1_xboole_0))=k4_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_315])).
% 2.84/1.46  tff(c_361, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=k3_xboole_0(A_1, A_1) | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_95, c_344])).
% 2.84/1.46  tff(c_367, plain, (![A_90]: (k4_xboole_0(A_90, k1_xboole_0)=k3_xboole_0(A_90, A_90))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_361])).
% 2.84/1.46  tff(c_385, plain, (![A_90]: (k3_xboole_0(A_90, A_90)=A_90 | k3_xboole_0(A_90, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_367, c_95])).
% 2.84/1.46  tff(c_417, plain, (![A_91]: (k3_xboole_0(A_91, A_91)=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_385])).
% 2.84/1.46  tff(c_148, plain, (![A_59, B_60]: (~r2_hidden(A_59, B_60) | ~r1_xboole_0(k1_tarski(A_59), B_60))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.84/1.46  tff(c_153, plain, (![A_59, B_2]: (~r2_hidden(A_59, B_2) | k3_xboole_0(k1_tarski(A_59), B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_148])).
% 2.84/1.46  tff(c_427, plain, (![A_59]: (~r2_hidden(A_59, k1_tarski(A_59)) | k1_tarski(A_59)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_417, c_153])).
% 2.84/1.46  tff(c_441, plain, (![A_59]: (k1_tarski(A_59)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_427])).
% 2.84/1.46  tff(c_54, plain, (![A_32]: (k1_setfam_1(k1_tarski(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.84/1.46  tff(c_38, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(B_16))=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.46  tff(c_507, plain, (![A_98, B_99]: (k3_xboole_0(k1_setfam_1(A_98), k1_setfam_1(B_99))=k1_setfam_1(k2_xboole_0(A_98, B_99)) | k1_xboole_0=B_99 | k1_xboole_0=A_98)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.84/1.46  tff(c_527, plain, (![A_32, B_99]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_32), B_99))=k3_xboole_0(A_32, k1_setfam_1(B_99)) | k1_xboole_0=B_99 | k1_tarski(A_32)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_507])).
% 2.84/1.46  tff(c_812, plain, (![A_134, B_135]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_134), B_135))=k3_xboole_0(A_134, k1_setfam_1(B_135)) | k1_xboole_0=B_135)), inference(negUnitSimplification, [status(thm)], [c_441, c_527])).
% 2.84/1.46  tff(c_838, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k1_setfam_1(k1_tarski(B_16)))=k1_setfam_1(k2_tarski(A_15, B_16)) | k1_tarski(B_16)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_812])).
% 2.84/1.46  tff(c_849, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(A_15, B_16) | k1_tarski(B_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_838])).
% 2.84/1.46  tff(c_850, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(negUnitSimplification, [status(thm)], [c_441, c_849])).
% 2.84/1.46  tff(c_56, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.84/1.46  tff(c_855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_850, c_56])).
% 2.84/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.46  
% 2.84/1.46  Inference rules
% 2.84/1.46  ----------------------
% 2.84/1.46  #Ref     : 0
% 2.84/1.46  #Sup     : 180
% 2.84/1.46  #Fact    : 0
% 2.84/1.46  #Define  : 0
% 2.84/1.46  #Split   : 0
% 2.84/1.46  #Chain   : 0
% 2.84/1.46  #Close   : 0
% 2.84/1.46  
% 2.84/1.46  Ordering : KBO
% 2.84/1.46  
% 2.84/1.46  Simplification rules
% 2.84/1.46  ----------------------
% 2.84/1.46  #Subsume      : 10
% 2.84/1.46  #Demod        : 97
% 2.84/1.46  #Tautology    : 111
% 2.84/1.46  #SimpNegUnit  : 8
% 2.84/1.46  #BackRed      : 3
% 2.84/1.46  
% 2.84/1.46  #Partial instantiations: 0
% 2.84/1.46  #Strategies tried      : 1
% 2.84/1.46  
% 2.84/1.46  Timing (in seconds)
% 2.84/1.46  ----------------------
% 2.84/1.46  Preprocessing        : 0.31
% 2.84/1.46  Parsing              : 0.16
% 2.84/1.46  CNF conversion       : 0.02
% 2.84/1.46  Main loop            : 0.32
% 2.84/1.46  Inferencing          : 0.12
% 2.84/1.46  Reduction            : 0.10
% 2.84/1.46  Demodulation         : 0.07
% 2.84/1.46  BG Simplification    : 0.02
% 2.84/1.46  Subsumption          : 0.06
% 2.84/1.46  Abstraction          : 0.02
% 2.84/1.46  MUC search           : 0.00
% 2.84/1.46  Cooper               : 0.00
% 2.84/1.47  Total                : 0.67
% 2.84/1.47  Index Insertion      : 0.00
% 2.84/1.47  Index Deletion       : 0.00
% 2.84/1.47  Index Matching       : 0.00
% 2.84/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
