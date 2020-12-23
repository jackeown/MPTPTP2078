%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:36 EST 2020

% Result     : Theorem 5.03s
% Output     : CNFRefutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 178 expanded)
%              Number of leaves         :   34 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :   63 ( 197 expanded)
%              Number of equality atoms :   53 ( 171 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_58,axiom,(
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

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_56,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    ! [A_27,B_28] : k1_enumset1(A_27,A_27,B_28) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [A_29,B_30,C_31] : k2_enumset1(A_29,A_29,B_30,C_31) = k1_enumset1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_551,plain,(
    ! [A_103,B_104,C_105,D_106] : k2_xboole_0(k1_enumset1(A_103,B_104,C_105),k1_tarski(D_106)) = k2_enumset1(A_103,B_104,C_105,D_106) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_596,plain,(
    ! [A_27,B_28,D_106] : k2_xboole_0(k2_tarski(A_27,B_28),k1_tarski(D_106)) = k2_enumset1(A_27,A_27,B_28,D_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_551])).

tff(c_607,plain,(
    ! [A_107,B_108,D_109] : k2_xboole_0(k2_tarski(A_107,B_108),k1_tarski(D_109)) = k1_enumset1(A_107,B_108,D_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_596])).

tff(c_643,plain,(
    ! [A_26,D_109] : k2_xboole_0(k1_tarski(A_26),k1_tarski(D_109)) = k1_enumset1(A_26,A_26,D_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_607])).

tff(c_653,plain,(
    ! [A_26,D_109] : k2_xboole_0(k1_tarski(A_26),k1_tarski(D_109)) = k2_tarski(A_26,D_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_643])).

tff(c_654,plain,(
    ! [A_110,D_111] : k2_xboole_0(k1_tarski(A_110),k1_tarski(D_111)) = k2_tarski(A_110,D_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_643])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_255,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_267,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_255])).

tff(c_270,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_267])).

tff(c_58,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_125,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = A_76
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_129,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_125])).

tff(c_264,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_255])).

tff(c_354,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_264])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_358,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_12])).

tff(c_361,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_358])).

tff(c_675,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_361])).

tff(c_606,plain,(
    ! [A_27,B_28,D_106] : k2_xboole_0(k2_tarski(A_27,B_28),k1_tarski(D_106)) = k1_enumset1(A_27,B_28,D_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_596])).

tff(c_714,plain,(
    ! [D_106] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_106)) = k1_enumset1('#skF_4','#skF_3',D_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_606])).

tff(c_785,plain,(
    ! [D_119] : k1_enumset1('#skF_4','#skF_3',D_119) = k2_tarski('#skF_4',D_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_714])).

tff(c_18,plain,(
    ! [E_18,A_12,C_14] : r2_hidden(E_18,k1_enumset1(A_12,E_18,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_810,plain,(
    ! [D_119] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_18])).

tff(c_727,plain,(
    ! [E_112,C_113,B_114,A_115] :
      ( E_112 = C_113
      | E_112 = B_114
      | E_112 = A_115
      | ~ r2_hidden(E_112,k1_enumset1(A_115,B_114,C_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2218,plain,(
    ! [E_203,B_204,A_205] :
      ( E_203 = B_204
      | E_203 = A_205
      | E_203 = A_205
      | ~ r2_hidden(E_203,k2_tarski(A_205,B_204)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_727])).

tff(c_2224,plain,(
    ! [D_119] :
      ( D_119 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_810,c_2218])).

tff(c_2245,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_2224])).

tff(c_2239,plain,(
    ! [D_119] : D_119 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_2224])).

tff(c_2578,plain,(
    ! [D_4016] : D_4016 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2245,c_2239])).

tff(c_2891,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2578,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.03/2.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/2.60  
% 5.22/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/2.61  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.22/2.61  
% 5.22/2.61  %Foreground sorts:
% 5.22/2.61  
% 5.22/2.61  
% 5.22/2.61  %Background operators:
% 5.22/2.61  
% 5.22/2.61  
% 5.22/2.61  %Foreground operators:
% 5.22/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.22/2.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.22/2.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.22/2.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.22/2.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.22/2.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.22/2.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.22/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.22/2.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.22/2.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.22/2.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.22/2.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.22/2.61  tff('#skF_3', type, '#skF_3': $i).
% 5.22/2.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.22/2.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.22/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.22/2.61  tff('#skF_4', type, '#skF_4': $i).
% 5.22/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.22/2.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.22/2.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.22/2.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.22/2.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.22/2.61  
% 5.22/2.64  tff(f_77, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 5.22/2.64  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.22/2.64  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.22/2.64  tff(f_64, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.22/2.64  tff(f_58, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 5.22/2.64  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.22/2.64  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.22/2.64  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 5.22/2.64  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.22/2.64  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.22/2.64  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.22/2.64  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.22/2.64  tff(c_56, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.22/2.64  tff(c_44, plain, (![A_27, B_28]: (k1_enumset1(A_27, A_27, B_28)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.22/2.64  tff(c_42, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.22/2.64  tff(c_46, plain, (![A_29, B_30, C_31]: (k2_enumset1(A_29, A_29, B_30, C_31)=k1_enumset1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.22/2.64  tff(c_551, plain, (![A_103, B_104, C_105, D_106]: (k2_xboole_0(k1_enumset1(A_103, B_104, C_105), k1_tarski(D_106))=k2_enumset1(A_103, B_104, C_105, D_106))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.22/2.64  tff(c_596, plain, (![A_27, B_28, D_106]: (k2_xboole_0(k2_tarski(A_27, B_28), k1_tarski(D_106))=k2_enumset1(A_27, A_27, B_28, D_106))), inference(superposition, [status(thm), theory('equality')], [c_44, c_551])).
% 5.22/2.64  tff(c_607, plain, (![A_107, B_108, D_109]: (k2_xboole_0(k2_tarski(A_107, B_108), k1_tarski(D_109))=k1_enumset1(A_107, B_108, D_109))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_596])).
% 5.22/2.64  tff(c_643, plain, (![A_26, D_109]: (k2_xboole_0(k1_tarski(A_26), k1_tarski(D_109))=k1_enumset1(A_26, A_26, D_109))), inference(superposition, [status(thm), theory('equality')], [c_42, c_607])).
% 5.22/2.64  tff(c_653, plain, (![A_26, D_109]: (k2_xboole_0(k1_tarski(A_26), k1_tarski(D_109))=k2_tarski(A_26, D_109))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_643])).
% 5.22/2.64  tff(c_654, plain, (![A_110, D_111]: (k2_xboole_0(k1_tarski(A_110), k1_tarski(D_111))=k2_tarski(A_110, D_111))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_643])).
% 5.22/2.64  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.22/2.64  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.22/2.64  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.22/2.64  tff(c_255, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.22/2.64  tff(c_267, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_255])).
% 5.22/2.64  tff(c_270, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_267])).
% 5.22/2.64  tff(c_58, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.22/2.64  tff(c_125, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=A_76 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.22/2.64  tff(c_129, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_58, c_125])).
% 5.22/2.64  tff(c_264, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_255])).
% 5.22/2.64  tff(c_354, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_270, c_264])).
% 5.22/2.64  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.22/2.64  tff(c_358, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_354, c_12])).
% 5.22/2.64  tff(c_361, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_358])).
% 5.22/2.64  tff(c_675, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_654, c_361])).
% 5.22/2.64  tff(c_606, plain, (![A_27, B_28, D_106]: (k2_xboole_0(k2_tarski(A_27, B_28), k1_tarski(D_106))=k1_enumset1(A_27, B_28, D_106))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_596])).
% 5.22/2.64  tff(c_714, plain, (![D_106]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_106))=k1_enumset1('#skF_4', '#skF_3', D_106))), inference(superposition, [status(thm), theory('equality')], [c_675, c_606])).
% 5.22/2.64  tff(c_785, plain, (![D_119]: (k1_enumset1('#skF_4', '#skF_3', D_119)=k2_tarski('#skF_4', D_119))), inference(demodulation, [status(thm), theory('equality')], [c_653, c_714])).
% 5.22/2.64  tff(c_18, plain, (![E_18, A_12, C_14]: (r2_hidden(E_18, k1_enumset1(A_12, E_18, C_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.22/2.64  tff(c_810, plain, (![D_119]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_119)))), inference(superposition, [status(thm), theory('equality')], [c_785, c_18])).
% 5.22/2.64  tff(c_727, plain, (![E_112, C_113, B_114, A_115]: (E_112=C_113 | E_112=B_114 | E_112=A_115 | ~r2_hidden(E_112, k1_enumset1(A_115, B_114, C_113)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.22/2.64  tff(c_2218, plain, (![E_203, B_204, A_205]: (E_203=B_204 | E_203=A_205 | E_203=A_205 | ~r2_hidden(E_203, k2_tarski(A_205, B_204)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_727])).
% 5.22/2.64  tff(c_2224, plain, (![D_119]: (D_119='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_810, c_2218])).
% 5.22/2.64  tff(c_2245, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_2224])).
% 5.22/2.64  tff(c_2239, plain, (![D_119]: (D_119='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_2224])).
% 5.22/2.64  tff(c_2578, plain, (![D_4016]: (D_4016='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2245, c_2239])).
% 5.22/2.64  tff(c_2891, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2578, c_56])).
% 5.22/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/2.64  
% 5.22/2.64  Inference rules
% 5.22/2.64  ----------------------
% 5.22/2.64  #Ref     : 0
% 5.22/2.64  #Sup     : 821
% 5.22/2.64  #Fact    : 0
% 5.22/2.64  #Define  : 0
% 5.22/2.64  #Split   : 0
% 5.22/2.64  #Chain   : 0
% 5.22/2.64  #Close   : 0
% 5.22/2.64  
% 5.22/2.64  Ordering : KBO
% 5.22/2.64  
% 5.22/2.64  Simplification rules
% 5.22/2.64  ----------------------
% 5.22/2.64  #Subsume      : 120
% 5.22/2.64  #Demod        : 615
% 5.22/2.64  #Tautology    : 465
% 5.22/2.64  #SimpNegUnit  : 9
% 5.22/2.64  #BackRed      : 0
% 5.22/2.64  
% 5.22/2.64  #Partial instantiations: 73
% 5.22/2.64  #Strategies tried      : 1
% 5.22/2.64  
% 5.22/2.64  Timing (in seconds)
% 5.22/2.64  ----------------------
% 5.22/2.64  Preprocessing        : 0.53
% 5.22/2.64  Parsing              : 0.27
% 5.22/2.64  CNF conversion       : 0.04
% 5.22/2.64  Main loop            : 1.17
% 5.22/2.64  Inferencing          : 0.46
% 5.22/2.64  Reduction            : 0.45
% 5.22/2.65  Demodulation         : 0.37
% 5.22/2.65  BG Simplification    : 0.04
% 5.22/2.65  Subsumption          : 0.15
% 5.22/2.65  Abstraction          : 0.06
% 5.22/2.65  MUC search           : 0.00
% 5.22/2.65  Cooper               : 0.00
% 5.22/2.65  Total                : 1.76
% 5.22/2.65  Index Insertion      : 0.00
% 5.22/2.65  Index Deletion       : 0.00
% 5.22/2.65  Index Matching       : 0.00
% 5.22/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
