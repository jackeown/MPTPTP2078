%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:23 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   64 (  70 expanded)
%              Number of leaves         :   35 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 (  56 expanded)
%              Number of equality atoms :   42 (  49 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_66,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_54,plain,(
    ! [A_30,B_31] : k1_enumset1(A_30,A_30,B_31) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_56,plain,(
    ! [A_32,B_33,C_34] : k2_enumset1(A_32,A_32,B_33,C_34) = k1_enumset1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1399,plain,(
    ! [A_2310,B_2311,C_2312,D_2313] : k2_xboole_0(k1_enumset1(A_2310,B_2311,C_2312),k1_tarski(D_2313)) = k2_enumset1(A_2310,B_2311,C_2312,D_2313) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1497,plain,(
    ! [A_30,B_31,D_2313] : k2_xboole_0(k2_tarski(A_30,B_31),k1_tarski(D_2313)) = k2_enumset1(A_30,A_30,B_31,D_2313) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1399])).

tff(c_1508,plain,(
    ! [A_2370,B_2371,D_2372] : k2_xboole_0(k2_tarski(A_2370,B_2371),k1_tarski(D_2372)) = k1_enumset1(A_2370,B_2371,D_2372) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1497])).

tff(c_1594,plain,(
    ! [A_29,D_2372] : k2_xboole_0(k1_tarski(A_29),k1_tarski(D_2372)) = k1_enumset1(A_29,A_29,D_2372) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1508])).

tff(c_1605,plain,(
    ! [A_2429,D_2430] : k2_xboole_0(k1_tarski(A_2429),k1_tarski(D_2430)) = k2_tarski(A_2429,D_2430) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1594])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_159,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_168,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_159])).

tff(c_174,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_168])).

tff(c_68,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_171,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_159])).

tff(c_259,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_171])).

tff(c_10,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_263,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_10])).

tff(c_266,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_263])).

tff(c_1635,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1605,c_266])).

tff(c_117,plain,(
    ! [A_75,B_76] : k1_enumset1(A_75,A_75,B_76) = k2_tarski(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_129,plain,(
    ! [B_76,A_75] : r2_hidden(B_76,k2_tarski(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_14])).

tff(c_1766,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1635,c_129])).

tff(c_36,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1797,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1766,c_36])).

tff(c_1838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1797])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:22:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.62  
% 3.37/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.62  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 3.37/1.62  
% 3.37/1.62  %Foreground sorts:
% 3.37/1.62  
% 3.37/1.62  
% 3.37/1.62  %Background operators:
% 3.37/1.62  
% 3.37/1.62  
% 3.37/1.62  %Foreground operators:
% 3.37/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.37/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.37/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.37/1.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.37/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.37/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.37/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.37/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.37/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.37/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.37/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.37/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.37/1.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.37/1.62  
% 3.37/1.64  tff(f_80, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.37/1.64  tff(f_65, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.37/1.64  tff(f_63, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.37/1.64  tff(f_67, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.37/1.64  tff(f_61, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.37/1.64  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.37/1.64  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.37/1.64  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.37/1.64  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.37/1.64  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.37/1.64  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.37/1.64  tff(f_57, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.37/1.64  tff(c_66, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.37/1.64  tff(c_54, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.37/1.64  tff(c_52, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.37/1.64  tff(c_56, plain, (![A_32, B_33, C_34]: (k2_enumset1(A_32, A_32, B_33, C_34)=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.37/1.64  tff(c_1399, plain, (![A_2310, B_2311, C_2312, D_2313]: (k2_xboole_0(k1_enumset1(A_2310, B_2311, C_2312), k1_tarski(D_2313))=k2_enumset1(A_2310, B_2311, C_2312, D_2313))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.37/1.64  tff(c_1497, plain, (![A_30, B_31, D_2313]: (k2_xboole_0(k2_tarski(A_30, B_31), k1_tarski(D_2313))=k2_enumset1(A_30, A_30, B_31, D_2313))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1399])).
% 3.37/1.64  tff(c_1508, plain, (![A_2370, B_2371, D_2372]: (k2_xboole_0(k2_tarski(A_2370, B_2371), k1_tarski(D_2372))=k1_enumset1(A_2370, B_2371, D_2372))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1497])).
% 3.37/1.64  tff(c_1594, plain, (![A_29, D_2372]: (k2_xboole_0(k1_tarski(A_29), k1_tarski(D_2372))=k1_enumset1(A_29, A_29, D_2372))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1508])).
% 3.37/1.64  tff(c_1605, plain, (![A_2429, D_2430]: (k2_xboole_0(k1_tarski(A_2429), k1_tarski(D_2430))=k2_tarski(A_2429, D_2430))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1594])).
% 3.37/1.64  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.37/1.64  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.37/1.64  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.37/1.64  tff(c_159, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.37/1.64  tff(c_168, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_159])).
% 3.37/1.64  tff(c_174, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_168])).
% 3.37/1.64  tff(c_68, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.37/1.64  tff(c_171, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_159])).
% 3.37/1.64  tff(c_259, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_174, c_171])).
% 3.37/1.64  tff(c_10, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.37/1.64  tff(c_263, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_259, c_10])).
% 3.37/1.64  tff(c_266, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_263])).
% 3.37/1.64  tff(c_1635, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1605, c_266])).
% 3.37/1.64  tff(c_117, plain, (![A_75, B_76]: (k1_enumset1(A_75, A_75, B_76)=k2_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.37/1.64  tff(c_14, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.37/1.64  tff(c_129, plain, (![B_76, A_75]: (r2_hidden(B_76, k2_tarski(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_117, c_14])).
% 3.37/1.64  tff(c_1766, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1635, c_129])).
% 3.37/1.64  tff(c_36, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.37/1.64  tff(c_1797, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1766, c_36])).
% 3.37/1.64  tff(c_1838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1797])).
% 3.37/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.64  
% 3.37/1.64  Inference rules
% 3.37/1.64  ----------------------
% 3.37/1.64  #Ref     : 0
% 3.37/1.64  #Sup     : 253
% 3.37/1.64  #Fact    : 0
% 3.37/1.64  #Define  : 0
% 3.37/1.64  #Split   : 2
% 3.37/1.64  #Chain   : 0
% 3.37/1.64  #Close   : 0
% 3.37/1.64  
% 3.37/1.64  Ordering : KBO
% 3.37/1.64  
% 3.37/1.64  Simplification rules
% 3.37/1.64  ----------------------
% 3.37/1.64  #Subsume      : 4
% 3.37/1.64  #Demod        : 150
% 3.37/1.64  #Tautology    : 132
% 3.37/1.64  #SimpNegUnit  : 1
% 3.37/1.64  #BackRed      : 0
% 3.37/1.64  
% 3.37/1.64  #Partial instantiations: 836
% 3.37/1.64  #Strategies tried      : 1
% 3.37/1.64  
% 3.37/1.64  Timing (in seconds)
% 3.37/1.64  ----------------------
% 3.37/1.64  Preprocessing        : 0.35
% 3.37/1.64  Parsing              : 0.17
% 3.37/1.64  CNF conversion       : 0.03
% 3.37/1.64  Main loop            : 0.51
% 3.37/1.64  Inferencing          : 0.23
% 3.37/1.64  Reduction            : 0.15
% 3.37/1.64  Demodulation         : 0.12
% 3.37/1.64  BG Simplification    : 0.03
% 3.37/1.64  Subsumption          : 0.07
% 3.37/1.64  Abstraction          : 0.02
% 3.37/1.64  MUC search           : 0.00
% 3.37/1.64  Cooper               : 0.00
% 3.37/1.64  Total                : 0.89
% 3.37/1.64  Index Insertion      : 0.00
% 3.37/1.64  Index Deletion       : 0.00
% 3.37/1.64  Index Matching       : 0.00
% 3.37/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
