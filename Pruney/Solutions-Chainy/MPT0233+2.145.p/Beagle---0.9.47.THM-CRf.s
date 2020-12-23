%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:39 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 111 expanded)
%              Number of leaves         :   40 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :   84 ( 146 expanded)
%              Number of equality atoms :   47 (  74 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_78,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_78,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_76,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_20,plain,(
    ! [A_20] : r1_xboole_0(A_20,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_248,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r1_xboole_0(A_96,B_97)
      | ~ r2_hidden(C_98,k3_xboole_0(A_96,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_326,plain,(
    ! [A_105,B_106] :
      ( ~ r1_xboole_0(A_105,B_106)
      | k3_xboole_0(A_105,B_106) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_248])).

tff(c_330,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_326])).

tff(c_18,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_331,plain,(
    ! [A_107] : k3_xboole_0(A_107,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_326])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_339,plain,(
    ! [A_107] : k5_xboole_0(A_107,k1_xboole_0) = k4_xboole_0(A_107,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_10])).

tff(c_358,plain,(
    ! [A_108] : k4_xboole_0(A_108,k1_xboole_0) = A_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_339])).

tff(c_16,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_364,plain,(
    ! [A_108] : k4_xboole_0(A_108,A_108) = k3_xboole_0(A_108,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_16])).

tff(c_369,plain,(
    ! [A_108] : k4_xboole_0(A_108,A_108) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_364])).

tff(c_72,plain,(
    ! [B_62] : k4_xboole_0(k1_tarski(B_62),k1_tarski(B_62)) != k1_tarski(B_62) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_391,plain,(
    ! [B_62] : k1_tarski(B_62) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_72])).

tff(c_68,plain,(
    ! [B_59,C_60] : r1_tarski(k1_tarski(B_59),k2_tarski(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_80,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_723,plain,(
    ! [A_132,C_133,B_134] :
      ( r1_tarski(A_132,C_133)
      | ~ r1_tarski(B_134,C_133)
      | ~ r1_tarski(A_132,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_868,plain,(
    ! [A_147] :
      ( r1_tarski(A_147,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_147,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_80,c_723])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_962,plain,(
    ! [A_159] :
      ( k3_xboole_0(A_159,k2_tarski('#skF_7','#skF_8')) = A_159
      | ~ r1_tarski(A_159,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_868,c_14])).

tff(c_986,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_962])).

tff(c_40,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_58,plain,(
    ! [B_56,C_57] :
      ( k4_xboole_0(k2_tarski(B_56,B_56),C_57) = k1_tarski(B_56)
      | r2_hidden(B_56,C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_507,plain,(
    ! [B_120,C_121] :
      ( k4_xboole_0(k1_tarski(B_120),C_121) = k1_tarski(B_120)
      | r2_hidden(B_120,C_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_58])).

tff(c_529,plain,(
    ! [B_120,C_121] :
      ( k4_xboole_0(k1_tarski(B_120),k1_tarski(B_120)) = k3_xboole_0(k1_tarski(B_120),C_121)
      | r2_hidden(B_120,C_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_16])).

tff(c_563,plain,(
    ! [B_120,C_121] :
      ( k3_xboole_0(k1_tarski(B_120),C_121) = k1_xboole_0
      | r2_hidden(B_120,C_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_529])).

tff(c_993,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_563])).

tff(c_1005,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_993])).

tff(c_22,plain,(
    ! [D_26,B_22,A_21] :
      ( D_26 = B_22
      | D_26 = A_21
      | ~ r2_hidden(D_26,k2_tarski(A_21,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1011,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1005,c_22])).

tff(c_1015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_76,c_1011])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:35:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.41  
% 2.91/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 2.91/1.41  
% 2.91/1.41  %Foreground sorts:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Background operators:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Foreground operators:
% 2.91/1.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.91/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.91/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.91/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.91/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.91/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.91/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.91/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.91/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.91/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.91/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.41  
% 2.91/1.42  tff(f_129, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.91/1.42  tff(f_67, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.91/1.42  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.91/1.42  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.91/1.42  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.91/1.42  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.91/1.42  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.91/1.42  tff(f_119, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.91/1.42  tff(f_114, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.91/1.42  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.91/1.42  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.91/1.42  tff(f_78, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.91/1.42  tff(f_99, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.91/1.42  tff(f_76, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.91/1.42  tff(c_78, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.91/1.42  tff(c_76, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.91/1.42  tff(c_20, plain, (![A_20]: (r1_xboole_0(A_20, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.91/1.42  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.91/1.42  tff(c_248, plain, (![A_96, B_97, C_98]: (~r1_xboole_0(A_96, B_97) | ~r2_hidden(C_98, k3_xboole_0(A_96, B_97)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.91/1.42  tff(c_326, plain, (![A_105, B_106]: (~r1_xboole_0(A_105, B_106) | k3_xboole_0(A_105, B_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_248])).
% 2.91/1.42  tff(c_330, plain, (![A_20]: (k3_xboole_0(A_20, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_326])).
% 2.91/1.42  tff(c_18, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.91/1.42  tff(c_331, plain, (![A_107]: (k3_xboole_0(A_107, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_326])).
% 2.91/1.42  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.91/1.42  tff(c_339, plain, (![A_107]: (k5_xboole_0(A_107, k1_xboole_0)=k4_xboole_0(A_107, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_331, c_10])).
% 2.91/1.42  tff(c_358, plain, (![A_108]: (k4_xboole_0(A_108, k1_xboole_0)=A_108)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_339])).
% 2.91/1.42  tff(c_16, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.91/1.42  tff(c_364, plain, (![A_108]: (k4_xboole_0(A_108, A_108)=k3_xboole_0(A_108, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_358, c_16])).
% 2.91/1.42  tff(c_369, plain, (![A_108]: (k4_xboole_0(A_108, A_108)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_330, c_364])).
% 2.91/1.42  tff(c_72, plain, (![B_62]: (k4_xboole_0(k1_tarski(B_62), k1_tarski(B_62))!=k1_tarski(B_62))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.42  tff(c_391, plain, (![B_62]: (k1_tarski(B_62)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_369, c_72])).
% 2.91/1.42  tff(c_68, plain, (![B_59, C_60]: (r1_tarski(k1_tarski(B_59), k2_tarski(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.91/1.42  tff(c_80, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.91/1.42  tff(c_723, plain, (![A_132, C_133, B_134]: (r1_tarski(A_132, C_133) | ~r1_tarski(B_134, C_133) | ~r1_tarski(A_132, B_134))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.91/1.42  tff(c_868, plain, (![A_147]: (r1_tarski(A_147, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_147, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_80, c_723])).
% 2.91/1.42  tff(c_14, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.91/1.42  tff(c_962, plain, (![A_159]: (k3_xboole_0(A_159, k2_tarski('#skF_7', '#skF_8'))=A_159 | ~r1_tarski(A_159, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_868, c_14])).
% 2.91/1.42  tff(c_986, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_68, c_962])).
% 2.91/1.42  tff(c_40, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.91/1.42  tff(c_58, plain, (![B_56, C_57]: (k4_xboole_0(k2_tarski(B_56, B_56), C_57)=k1_tarski(B_56) | r2_hidden(B_56, C_57))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.91/1.42  tff(c_507, plain, (![B_120, C_121]: (k4_xboole_0(k1_tarski(B_120), C_121)=k1_tarski(B_120) | r2_hidden(B_120, C_121))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_58])).
% 2.91/1.42  tff(c_529, plain, (![B_120, C_121]: (k4_xboole_0(k1_tarski(B_120), k1_tarski(B_120))=k3_xboole_0(k1_tarski(B_120), C_121) | r2_hidden(B_120, C_121))), inference(superposition, [status(thm), theory('equality')], [c_507, c_16])).
% 2.91/1.42  tff(c_563, plain, (![B_120, C_121]: (k3_xboole_0(k1_tarski(B_120), C_121)=k1_xboole_0 | r2_hidden(B_120, C_121))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_529])).
% 2.91/1.42  tff(c_993, plain, (k1_tarski('#skF_5')=k1_xboole_0 | r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_986, c_563])).
% 2.91/1.42  tff(c_1005, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_391, c_993])).
% 2.91/1.42  tff(c_22, plain, (![D_26, B_22, A_21]: (D_26=B_22 | D_26=A_21 | ~r2_hidden(D_26, k2_tarski(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.91/1.42  tff(c_1011, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1005, c_22])).
% 2.91/1.42  tff(c_1015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_76, c_1011])).
% 2.91/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.42  
% 2.91/1.42  Inference rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Ref     : 0
% 2.91/1.42  #Sup     : 213
% 2.91/1.42  #Fact    : 0
% 2.91/1.42  #Define  : 0
% 2.91/1.42  #Split   : 1
% 2.91/1.42  #Chain   : 0
% 2.91/1.42  #Close   : 0
% 2.91/1.42  
% 2.91/1.42  Ordering : KBO
% 2.91/1.42  
% 2.91/1.42  Simplification rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Subsume      : 23
% 2.91/1.42  #Demod        : 66
% 2.91/1.42  #Tautology    : 132
% 2.91/1.42  #SimpNegUnit  : 28
% 2.91/1.42  #BackRed      : 2
% 2.91/1.42  
% 2.91/1.42  #Partial instantiations: 0
% 2.91/1.42  #Strategies tried      : 1
% 2.91/1.42  
% 2.91/1.42  Timing (in seconds)
% 2.91/1.42  ----------------------
% 2.91/1.42  Preprocessing        : 0.34
% 2.91/1.42  Parsing              : 0.18
% 2.91/1.42  CNF conversion       : 0.02
% 2.91/1.42  Main loop            : 0.33
% 2.91/1.43  Inferencing          : 0.12
% 2.91/1.43  Reduction            : 0.11
% 2.91/1.43  Demodulation         : 0.08
% 2.91/1.43  BG Simplification    : 0.02
% 2.91/1.43  Subsumption          : 0.06
% 2.91/1.43  Abstraction          : 0.02
% 2.91/1.43  MUC search           : 0.00
% 2.91/1.43  Cooper               : 0.00
% 2.91/1.43  Total                : 0.69
% 2.91/1.43  Index Insertion      : 0.00
% 2.91/1.43  Index Deletion       : 0.00
% 2.91/1.43  Index Matching       : 0.00
% 2.91/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
