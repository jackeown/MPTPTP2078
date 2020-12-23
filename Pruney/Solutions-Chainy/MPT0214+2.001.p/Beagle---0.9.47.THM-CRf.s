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
% DateTime   : Thu Dec  3 09:47:30 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   67 (  73 expanded)
%              Number of leaves         :   36 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  61 expanded)
%              Number of equality atoms :   43 (  49 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_66,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_54,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,(
    ! [A_33,B_34,C_35] : k2_enumset1(A_33,A_33,B_34,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1350,plain,(
    ! [A_1993,B_1994,C_1995,D_1996] : k2_xboole_0(k1_enumset1(A_1993,B_1994,C_1995),k1_tarski(D_1996)) = k2_enumset1(A_1993,B_1994,C_1995,D_1996) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1434,plain,(
    ! [A_31,B_32,D_1996] : k2_xboole_0(k2_tarski(A_31,B_32),k1_tarski(D_1996)) = k2_enumset1(A_31,A_31,B_32,D_1996) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1350])).

tff(c_1445,plain,(
    ! [A_2045,B_2046,D_2047] : k2_xboole_0(k2_tarski(A_2045,B_2046),k1_tarski(D_2047)) = k1_enumset1(A_2045,B_2046,D_2047) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1434])).

tff(c_1535,plain,(
    ! [A_30,D_2047] : k2_xboole_0(k1_tarski(A_30),k1_tarski(D_2047)) = k1_enumset1(A_30,A_30,D_2047) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1445])).

tff(c_1547,plain,(
    ! [A_2144,D_2145] : k2_xboole_0(k1_tarski(A_2144),k1_tarski(D_2145)) = k2_tarski(A_2144,D_2145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1535])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_200,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_212,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_200])).

tff(c_215,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_212])).

tff(c_68,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_176,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_180,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_176])).

tff(c_209,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_200])).

tff(c_378,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_209])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_382,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_12])).

tff(c_385,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_382])).

tff(c_1556,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1547,c_385])).

tff(c_146,plain,(
    ! [A_71,B_72] : k1_enumset1(A_71,A_71,B_72) = k2_tarski(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_158,plain,(
    ! [B_72,A_71] : r2_hidden(B_72,k2_tarski(A_71,B_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_18])).

tff(c_1703,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1556,c_158])).

tff(c_40,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1733,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1703,c_40])).

tff(c_1773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.48  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 3.22/1.48  
% 3.22/1.48  %Foreground sorts:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Background operators:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Foreground operators:
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.22/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.22/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.22/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.22/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.22/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.22/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.22/1.48  
% 3.22/1.50  tff(f_82, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 3.22/1.50  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.22/1.50  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.22/1.50  tff(f_71, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.22/1.50  tff(f_65, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.22/1.50  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.22/1.50  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.22/1.50  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.22/1.50  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.22/1.50  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.22/1.50  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.22/1.50  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.22/1.50  tff(f_63, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.22/1.50  tff(c_66, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.22/1.50  tff(c_56, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.22/1.50  tff(c_54, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.50  tff(c_58, plain, (![A_33, B_34, C_35]: (k2_enumset1(A_33, A_33, B_34, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.22/1.50  tff(c_1350, plain, (![A_1993, B_1994, C_1995, D_1996]: (k2_xboole_0(k1_enumset1(A_1993, B_1994, C_1995), k1_tarski(D_1996))=k2_enumset1(A_1993, B_1994, C_1995, D_1996))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.22/1.50  tff(c_1434, plain, (![A_31, B_32, D_1996]: (k2_xboole_0(k2_tarski(A_31, B_32), k1_tarski(D_1996))=k2_enumset1(A_31, A_31, B_32, D_1996))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1350])).
% 3.22/1.50  tff(c_1445, plain, (![A_2045, B_2046, D_2047]: (k2_xboole_0(k2_tarski(A_2045, B_2046), k1_tarski(D_2047))=k1_enumset1(A_2045, B_2046, D_2047))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1434])).
% 3.22/1.50  tff(c_1535, plain, (![A_30, D_2047]: (k2_xboole_0(k1_tarski(A_30), k1_tarski(D_2047))=k1_enumset1(A_30, A_30, D_2047))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1445])).
% 3.22/1.50  tff(c_1547, plain, (![A_2144, D_2145]: (k2_xboole_0(k1_tarski(A_2144), k1_tarski(D_2145))=k2_tarski(A_2144, D_2145))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1535])).
% 3.22/1.50  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.50  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.50  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.50  tff(c_200, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.50  tff(c_212, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_200])).
% 3.22/1.50  tff(c_215, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_212])).
% 3.22/1.50  tff(c_68, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.22/1.50  tff(c_176, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.50  tff(c_180, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_68, c_176])).
% 3.22/1.50  tff(c_209, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_180, c_200])).
% 3.22/1.50  tff(c_378, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_215, c_209])).
% 3.22/1.50  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.50  tff(c_382, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_378, c_12])).
% 3.22/1.50  tff(c_385, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_382])).
% 3.22/1.50  tff(c_1556, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1547, c_385])).
% 3.22/1.50  tff(c_146, plain, (![A_71, B_72]: (k1_enumset1(A_71, A_71, B_72)=k2_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.22/1.50  tff(c_18, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.50  tff(c_158, plain, (![B_72, A_71]: (r2_hidden(B_72, k2_tarski(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_18])).
% 3.22/1.50  tff(c_1703, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1556, c_158])).
% 3.22/1.50  tff(c_40, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.22/1.50  tff(c_1733, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1703, c_40])).
% 3.22/1.50  tff(c_1773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1733])).
% 3.22/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  Inference rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Ref     : 0
% 3.22/1.50  #Sup     : 229
% 3.22/1.50  #Fact    : 0
% 3.22/1.50  #Define  : 0
% 3.22/1.50  #Split   : 1
% 3.22/1.50  #Chain   : 0
% 3.22/1.50  #Close   : 0
% 3.22/1.50  
% 3.22/1.50  Ordering : KBO
% 3.22/1.50  
% 3.22/1.50  Simplification rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Subsume      : 0
% 3.22/1.50  #Demod        : 118
% 3.22/1.50  #Tautology    : 108
% 3.22/1.50  #SimpNegUnit  : 1
% 3.22/1.50  #BackRed      : 0
% 3.22/1.50  
% 3.22/1.50  #Partial instantiations: 792
% 3.22/1.50  #Strategies tried      : 1
% 3.22/1.50  
% 3.22/1.50  Timing (in seconds)
% 3.22/1.50  ----------------------
% 3.22/1.50  Preprocessing        : 0.32
% 3.22/1.50  Parsing              : 0.17
% 3.22/1.50  CNF conversion       : 0.02
% 3.22/1.50  Main loop            : 0.42
% 3.22/1.50  Inferencing          : 0.20
% 3.22/1.50  Reduction            : 0.12
% 3.22/1.50  Demodulation         : 0.09
% 3.22/1.50  BG Simplification    : 0.02
% 3.22/1.50  Subsumption          : 0.06
% 3.22/1.50  Abstraction          : 0.02
% 3.22/1.50  MUC search           : 0.00
% 3.22/1.50  Cooper               : 0.00
% 3.22/1.50  Total                : 0.76
% 3.22/1.50  Index Insertion      : 0.00
% 3.22/1.50  Index Deletion       : 0.00
% 3.22/1.50  Index Matching       : 0.00
% 3.22/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
