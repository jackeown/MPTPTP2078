%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:34 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 101 expanded)
%              Number of leaves         :   36 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 127 expanded)
%              Number of equality atoms :   55 (  88 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_76,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_74,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_276,plain,(
    ! [A_85,B_86] : k1_enumset1(A_85,A_85,B_86) = k2_tarski(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [E_22,A_16,C_18] : r2_hidden(E_22,k1_enumset1(A_16,E_22,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_282,plain,(
    ! [A_85,B_86] : r2_hidden(A_85,k2_tarski(A_85,B_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_22])).

tff(c_12,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_344,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = k4_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_368,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_344])).

tff(c_373,plain,(
    ! [A_101] : k4_xboole_0(A_101,k1_xboole_0) = A_101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_368])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_379,plain,(
    ! [A_101] : k4_xboole_0(A_101,A_101) = k3_xboole_0(A_101,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_14])).

tff(c_384,plain,(
    ! [A_101] : k4_xboole_0(A_101,A_101) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_379])).

tff(c_888,plain,(
    ! [A_130,C_131,B_132] :
      ( ~ r2_hidden(A_130,C_131)
      | k4_xboole_0(k2_tarski(A_130,B_132),C_131) != k1_tarski(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_896,plain,(
    ! [A_130,B_132] :
      ( ~ r2_hidden(A_130,k2_tarski(A_130,B_132))
      | k1_tarski(A_130) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_888])).

tff(c_909,plain,(
    ! [A_130] : k1_tarski(A_130) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_896])).

tff(c_70,plain,(
    ! [B_55,C_56] : r1_tarski(k1_tarski(B_55),k2_tarski(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_78,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_243,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = A_83
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_271,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_243])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_299,plain,(
    ! [A_90,B_91,C_92] :
      ( r1_tarski(A_90,B_91)
      | ~ r1_tarski(A_90,k3_xboole_0(B_91,C_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_552,plain,(
    ! [A_109,B_110,A_111] :
      ( r1_tarski(A_109,B_110)
      | ~ r1_tarski(A_109,k3_xboole_0(A_111,B_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_299])).

tff(c_816,plain,(
    ! [A_127] :
      ( r1_tarski(A_127,k2_tarski('#skF_5','#skF_6'))
      | ~ r1_tarski(A_127,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_552])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1515,plain,(
    ! [A_172] :
      ( k3_xboole_0(A_172,k2_tarski('#skF_5','#skF_6')) = A_172
      | ~ r1_tarski(A_172,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_816,c_10])).

tff(c_1545,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1515])).

tff(c_42,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    ! [B_52,C_53] :
      ( k4_xboole_0(k2_tarski(B_52,B_52),C_53) = k1_tarski(B_52)
      | r2_hidden(B_52,C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_446,plain,(
    ! [B_104,C_105] :
      ( k4_xboole_0(k1_tarski(B_104),C_105) = k1_tarski(B_104)
      | r2_hidden(B_104,C_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_60])).

tff(c_460,plain,(
    ! [B_104,C_105] :
      ( k4_xboole_0(k1_tarski(B_104),k1_tarski(B_104)) = k3_xboole_0(k1_tarski(B_104),C_105)
      | r2_hidden(B_104,C_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_14])).

tff(c_483,plain,(
    ! [B_104,C_105] :
      ( k3_xboole_0(k1_tarski(B_104),C_105) = k1_xboole_0
      | r2_hidden(B_104,C_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_460])).

tff(c_1641,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1545,c_483])).

tff(c_1662,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_909,c_1641])).

tff(c_44,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1610,plain,(
    ! [E_173,C_174,B_175,A_176] :
      ( E_173 = C_174
      | E_173 = B_175
      | E_173 = A_176
      | ~ r2_hidden(E_173,k1_enumset1(A_176,B_175,C_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1747,plain,(
    ! [E_187,B_188,A_189] :
      ( E_187 = B_188
      | E_187 = A_189
      | E_187 = A_189
      | ~ r2_hidden(E_187,k2_tarski(A_189,B_188)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1610])).

tff(c_1750,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1662,c_1747])).

tff(c_1766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_76,c_74,c_1750])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.66  
% 3.51/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.66  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.51/1.66  
% 3.51/1.66  %Foreground sorts:
% 3.51/1.66  
% 3.51/1.66  
% 3.51/1.66  %Background operators:
% 3.51/1.66  
% 3.51/1.66  
% 3.51/1.66  %Foreground operators:
% 3.51/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.51/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.51/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.51/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.51/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.51/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.51/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.51/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.51/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.51/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.51/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.51/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.51/1.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.51/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.51/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.51/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.51/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.51/1.66  
% 3.51/1.68  tff(f_108, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.51/1.68  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.51/1.68  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.51/1.68  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.51/1.68  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.51/1.68  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.51/1.68  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.51/1.68  tff(f_83, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 3.51/1.68  tff(f_98, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.51/1.68  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.51/1.68  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.51/1.68  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.51/1.68  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.51/1.68  tff(c_76, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.51/1.68  tff(c_74, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.51/1.68  tff(c_276, plain, (![A_85, B_86]: (k1_enumset1(A_85, A_85, B_86)=k2_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.51/1.68  tff(c_22, plain, (![E_22, A_16, C_18]: (r2_hidden(E_22, k1_enumset1(A_16, E_22, C_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.51/1.68  tff(c_282, plain, (![A_85, B_86]: (r2_hidden(A_85, k2_tarski(A_85, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_276, c_22])).
% 3.51/1.68  tff(c_12, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.51/1.68  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.51/1.68  tff(c_344, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k3_xboole_0(A_99, B_100))=k4_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.51/1.68  tff(c_368, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_344])).
% 3.51/1.68  tff(c_373, plain, (![A_101]: (k4_xboole_0(A_101, k1_xboole_0)=A_101)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_368])).
% 3.51/1.68  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.51/1.68  tff(c_379, plain, (![A_101]: (k4_xboole_0(A_101, A_101)=k3_xboole_0(A_101, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_373, c_14])).
% 3.51/1.68  tff(c_384, plain, (![A_101]: (k4_xboole_0(A_101, A_101)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_379])).
% 3.51/1.68  tff(c_888, plain, (![A_130, C_131, B_132]: (~r2_hidden(A_130, C_131) | k4_xboole_0(k2_tarski(A_130, B_132), C_131)!=k1_tarski(A_130))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.51/1.68  tff(c_896, plain, (![A_130, B_132]: (~r2_hidden(A_130, k2_tarski(A_130, B_132)) | k1_tarski(A_130)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_384, c_888])).
% 3.51/1.68  tff(c_909, plain, (![A_130]: (k1_tarski(A_130)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_282, c_896])).
% 3.51/1.68  tff(c_70, plain, (![B_55, C_56]: (r1_tarski(k1_tarski(B_55), k2_tarski(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.51/1.68  tff(c_78, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.51/1.68  tff(c_243, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=A_83 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.51/1.68  tff(c_271, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_243])).
% 3.51/1.68  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.51/1.68  tff(c_299, plain, (![A_90, B_91, C_92]: (r1_tarski(A_90, B_91) | ~r1_tarski(A_90, k3_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.51/1.68  tff(c_552, plain, (![A_109, B_110, A_111]: (r1_tarski(A_109, B_110) | ~r1_tarski(A_109, k3_xboole_0(A_111, B_110)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_299])).
% 3.51/1.68  tff(c_816, plain, (![A_127]: (r1_tarski(A_127, k2_tarski('#skF_5', '#skF_6')) | ~r1_tarski(A_127, k2_tarski('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_271, c_552])).
% 3.51/1.68  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.51/1.68  tff(c_1515, plain, (![A_172]: (k3_xboole_0(A_172, k2_tarski('#skF_5', '#skF_6'))=A_172 | ~r1_tarski(A_172, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_816, c_10])).
% 3.51/1.68  tff(c_1545, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1515])).
% 3.51/1.68  tff(c_42, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.51/1.68  tff(c_60, plain, (![B_52, C_53]: (k4_xboole_0(k2_tarski(B_52, B_52), C_53)=k1_tarski(B_52) | r2_hidden(B_52, C_53))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.51/1.68  tff(c_446, plain, (![B_104, C_105]: (k4_xboole_0(k1_tarski(B_104), C_105)=k1_tarski(B_104) | r2_hidden(B_104, C_105))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_60])).
% 3.51/1.68  tff(c_460, plain, (![B_104, C_105]: (k4_xboole_0(k1_tarski(B_104), k1_tarski(B_104))=k3_xboole_0(k1_tarski(B_104), C_105) | r2_hidden(B_104, C_105))), inference(superposition, [status(thm), theory('equality')], [c_446, c_14])).
% 3.51/1.68  tff(c_483, plain, (![B_104, C_105]: (k3_xboole_0(k1_tarski(B_104), C_105)=k1_xboole_0 | r2_hidden(B_104, C_105))), inference(demodulation, [status(thm), theory('equality')], [c_384, c_460])).
% 3.51/1.68  tff(c_1641, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1545, c_483])).
% 3.51/1.68  tff(c_1662, plain, (r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_909, c_1641])).
% 3.51/1.68  tff(c_44, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.51/1.68  tff(c_1610, plain, (![E_173, C_174, B_175, A_176]: (E_173=C_174 | E_173=B_175 | E_173=A_176 | ~r2_hidden(E_173, k1_enumset1(A_176, B_175, C_174)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.51/1.68  tff(c_1747, plain, (![E_187, B_188, A_189]: (E_187=B_188 | E_187=A_189 | E_187=A_189 | ~r2_hidden(E_187, k2_tarski(A_189, B_188)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1610])).
% 3.51/1.68  tff(c_1750, plain, ('#skF_6'='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_1662, c_1747])).
% 3.51/1.68  tff(c_1766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_76, c_74, c_1750])).
% 3.51/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.68  
% 3.51/1.68  Inference rules
% 3.51/1.68  ----------------------
% 3.51/1.68  #Ref     : 0
% 3.51/1.68  #Sup     : 399
% 3.51/1.68  #Fact    : 0
% 3.51/1.68  #Define  : 0
% 3.51/1.68  #Split   : 0
% 3.51/1.68  #Chain   : 0
% 3.51/1.68  #Close   : 0
% 3.51/1.68  
% 3.51/1.68  Ordering : KBO
% 3.51/1.68  
% 3.51/1.68  Simplification rules
% 3.51/1.68  ----------------------
% 3.51/1.68  #Subsume      : 43
% 3.51/1.68  #Demod        : 223
% 3.51/1.68  #Tautology    : 255
% 3.51/1.68  #SimpNegUnit  : 28
% 3.51/1.68  #BackRed      : 0
% 3.51/1.68  
% 3.51/1.68  #Partial instantiations: 0
% 3.51/1.68  #Strategies tried      : 1
% 3.51/1.68  
% 3.51/1.68  Timing (in seconds)
% 3.51/1.68  ----------------------
% 3.51/1.68  Preprocessing        : 0.36
% 3.51/1.68  Parsing              : 0.19
% 3.51/1.68  CNF conversion       : 0.03
% 3.51/1.68  Main loop            : 0.50
% 3.51/1.68  Inferencing          : 0.17
% 3.51/1.68  Reduction            : 0.19
% 3.51/1.68  Demodulation         : 0.15
% 3.51/1.68  BG Simplification    : 0.03
% 3.51/1.68  Subsumption          : 0.09
% 3.51/1.68  Abstraction          : 0.02
% 3.51/1.68  MUC search           : 0.00
% 3.51/1.68  Cooper               : 0.00
% 3.51/1.68  Total                : 0.90
% 3.51/1.68  Index Insertion      : 0.00
% 3.51/1.68  Index Deletion       : 0.00
% 3.51/1.68  Index Matching       : 0.00
% 3.51/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
