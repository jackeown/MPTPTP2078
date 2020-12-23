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
% DateTime   : Thu Dec  3 09:48:58 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   63 (  68 expanded)
%              Number of leaves         :   35 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   55 (  70 expanded)
%              Number of equality atoms :   45 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_58,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    ! [A_33,B_34,C_35] : k2_enumset1(A_33,A_33,B_34,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_241,plain,(
    ! [A_92,B_93,C_94,D_95] : k2_xboole_0(k2_tarski(A_92,B_93),k2_tarski(C_94,D_95)) = k2_enumset1(A_92,B_93,C_94,D_95) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_262,plain,(
    ! [A_30,C_94,D_95] : k2_xboole_0(k1_tarski(A_30),k2_tarski(C_94,D_95)) = k2_enumset1(A_30,A_30,C_94,D_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_241])).

tff(c_269,plain,(
    ! [A_96,C_97,D_98] : k2_xboole_0(k1_tarski(A_96),k2_tarski(C_97,D_98)) = k1_enumset1(A_96,C_97,D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_262])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_161,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_161])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_187,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_4])).

tff(c_190,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_187])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_195,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_12])).

tff(c_198,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_195])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_212,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_2])).

tff(c_275,plain,(
    k1_enumset1('#skF_3','#skF_4','#skF_5') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_212])).

tff(c_20,plain,(
    ! [E_17,B_12,C_13] : r2_hidden(E_17,k1_enumset1(E_17,B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_302,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_20])).

tff(c_44,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_418,plain,(
    ! [E_103,C_104,B_105,A_106] :
      ( E_103 = C_104
      | E_103 = B_105
      | E_103 = A_106
      | ~ r2_hidden(E_103,k1_enumset1(A_106,B_105,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_758,plain,(
    ! [E_139,B_140,A_141] :
      ( E_139 = B_140
      | E_139 = A_141
      | E_139 = A_141
      | ~ r2_hidden(E_139,k2_tarski(A_141,B_140)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_418])).

tff(c_761,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_302,c_758])).

tff(c_774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_58,c_56,c_761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.41  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.74/1.41  
% 2.74/1.41  %Foreground sorts:
% 2.74/1.41  
% 2.74/1.41  
% 2.74/1.41  %Background operators:
% 2.74/1.41  
% 2.74/1.41  
% 2.74/1.41  %Foreground operators:
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.74/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.74/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.74/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.74/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.74/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.74/1.41  
% 2.74/1.43  tff(f_82, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.74/1.43  tff(f_64, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.74/1.43  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.74/1.43  tff(f_56, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.74/1.43  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.74/1.43  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.74/1.43  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.74/1.43  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.74/1.43  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.74/1.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.74/1.43  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.74/1.43  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.74/1.43  tff(c_58, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.74/1.43  tff(c_56, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.74/1.43  tff(c_46, plain, (![A_33, B_34, C_35]: (k2_enumset1(A_33, A_33, B_34, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.74/1.43  tff(c_42, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.74/1.43  tff(c_241, plain, (![A_92, B_93, C_94, D_95]: (k2_xboole_0(k2_tarski(A_92, B_93), k2_tarski(C_94, D_95))=k2_enumset1(A_92, B_93, C_94, D_95))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.74/1.43  tff(c_262, plain, (![A_30, C_94, D_95]: (k2_xboole_0(k1_tarski(A_30), k2_tarski(C_94, D_95))=k2_enumset1(A_30, A_30, C_94, D_95))), inference(superposition, [status(thm), theory('equality')], [c_42, c_241])).
% 2.74/1.43  tff(c_269, plain, (![A_96, C_97, D_98]: (k2_xboole_0(k1_tarski(A_96), k2_tarski(C_97, D_98))=k1_enumset1(A_96, C_97, D_98))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_262])).
% 2.74/1.43  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.74/1.43  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.43  tff(c_60, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.74/1.43  tff(c_161, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.43  tff(c_165, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_60, c_161])).
% 2.74/1.43  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.74/1.43  tff(c_187, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_4])).
% 2.74/1.43  tff(c_190, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_187])).
% 2.74/1.43  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.43  tff(c_195, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_190, c_12])).
% 2.74/1.43  tff(c_198, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_195])).
% 2.74/1.43  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.43  tff(c_212, plain, (k2_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_198, c_2])).
% 2.74/1.43  tff(c_275, plain, (k1_enumset1('#skF_3', '#skF_4', '#skF_5')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_269, c_212])).
% 2.74/1.43  tff(c_20, plain, (![E_17, B_12, C_13]: (r2_hidden(E_17, k1_enumset1(E_17, B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.74/1.43  tff(c_302, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_275, c_20])).
% 2.74/1.43  tff(c_44, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.74/1.43  tff(c_418, plain, (![E_103, C_104, B_105, A_106]: (E_103=C_104 | E_103=B_105 | E_103=A_106 | ~r2_hidden(E_103, k1_enumset1(A_106, B_105, C_104)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.74/1.43  tff(c_758, plain, (![E_139, B_140, A_141]: (E_139=B_140 | E_139=A_141 | E_139=A_141 | ~r2_hidden(E_139, k2_tarski(A_141, B_140)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_418])).
% 2.74/1.43  tff(c_761, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_302, c_758])).
% 2.74/1.43  tff(c_774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_58, c_56, c_761])).
% 2.74/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.43  
% 2.74/1.43  Inference rules
% 2.74/1.43  ----------------------
% 2.74/1.43  #Ref     : 0
% 2.74/1.43  #Sup     : 180
% 2.74/1.43  #Fact    : 0
% 2.74/1.43  #Define  : 0
% 2.74/1.43  #Split   : 0
% 2.74/1.43  #Chain   : 0
% 2.74/1.43  #Close   : 0
% 2.74/1.43  
% 2.74/1.43  Ordering : KBO
% 2.74/1.43  
% 2.74/1.43  Simplification rules
% 2.74/1.43  ----------------------
% 2.74/1.43  #Subsume      : 19
% 2.74/1.43  #Demod        : 59
% 2.74/1.43  #Tautology    : 127
% 2.74/1.43  #SimpNegUnit  : 4
% 2.74/1.43  #BackRed      : 0
% 2.74/1.43  
% 2.74/1.43  #Partial instantiations: 0
% 2.74/1.43  #Strategies tried      : 1
% 2.74/1.43  
% 2.74/1.43  Timing (in seconds)
% 2.74/1.43  ----------------------
% 2.74/1.43  Preprocessing        : 0.34
% 2.74/1.43  Parsing              : 0.18
% 2.74/1.43  CNF conversion       : 0.02
% 2.74/1.43  Main loop            : 0.31
% 2.74/1.43  Inferencing          : 0.11
% 2.74/1.43  Reduction            : 0.11
% 2.74/1.43  Demodulation         : 0.09
% 2.74/1.43  BG Simplification    : 0.02
% 2.74/1.43  Subsumption          : 0.05
% 2.74/1.43  Abstraction          : 0.02
% 2.74/1.43  MUC search           : 0.00
% 2.74/1.43  Cooper               : 0.00
% 2.74/1.43  Total                : 0.68
% 2.74/1.43  Index Insertion      : 0.00
% 2.74/1.43  Index Deletion       : 0.00
% 2.74/1.43  Index Matching       : 0.00
% 2.74/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
