%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:54 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 149 expanded)
%              Number of leaves         :   29 (  60 expanded)
%              Depth                    :   20
%              Number of atoms          :   99 ( 177 expanded)
%              Number of equality atoms :   61 ( 117 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_81,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_685,plain,(
    ! [A_81,B_82] : k4_xboole_0(k2_xboole_0(A_81,B_82),B_82) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_704,plain,(
    ! [A_81] : k4_xboole_0(A_81,k1_xboole_0) = k2_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_22])).

tff(c_739,plain,(
    ! [A_81] : k2_xboole_0(A_81,k1_xboole_0) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_704])).

tff(c_32,plain,(
    ! [A_29] : r1_xboole_0(A_29,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_101,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_29] : k3_xboole_0(A_29,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_101])).

tff(c_279,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_303,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_279])).

tff(c_308,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_303])).

tff(c_30,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_309,plain,(
    ! [A_65] : k4_xboole_0(A_65,A_65) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_303])).

tff(c_314,plain,(
    ! [A_65] : k4_xboole_0(A_65,k1_xboole_0) = k3_xboole_0(A_65,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_30])).

tff(c_335,plain,(
    ! [A_65] : k3_xboole_0(A_65,A_65) = A_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_314])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_343,plain,(
    ! [A_66] : k3_xboole_0(A_66,A_66) = A_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_314])).

tff(c_16,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_444,plain,(
    ! [A_69,C_70] :
      ( ~ r1_xboole_0(A_69,A_69)
      | ~ r2_hidden(C_70,A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_16])).

tff(c_450,plain,(
    ! [C_70,B_4] :
      ( ~ r2_hidden(C_70,B_4)
      | k3_xboole_0(B_4,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_444])).

tff(c_580,plain,(
    ! [C_74,B_75] :
      ( ~ r2_hidden(C_74,B_75)
      | k1_xboole_0 != B_75 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_450])).

tff(c_606,plain,(
    ! [A_78,B_79] :
      ( k1_xboole_0 != A_78
      | r1_xboole_0(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_12,c_580])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1534,plain,(
    ! [A_109,B_110] :
      ( k3_xboole_0(A_109,B_110) = k1_xboole_0
      | k1_xboole_0 != A_109 ) ),
    inference(resolution,[status(thm)],[c_606,c_4])).

tff(c_28,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k3_xboole_0(A_25,B_26)) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1557,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,k1_xboole_0) = k4_xboole_0(A_109,B_110)
      | k1_xboole_0 != A_109 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1534,c_28])).

tff(c_1730,plain,(
    ! [A_117,B_118] :
      ( k4_xboole_0(A_117,B_118) = A_117
      | k1_xboole_0 != A_117 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1557])).

tff(c_2037,plain,(
    ! [A_121,B_122] :
      ( k3_xboole_0(A_121,B_122) = A_121
      | k1_xboole_0 != A_121 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1730])).

tff(c_2066,plain,(
    ! [A_121,B_122] :
      ( k4_xboole_0(A_121,B_122) = k4_xboole_0(A_121,A_121)
      | k1_xboole_0 != A_121 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2037,c_28])).

tff(c_2179,plain,(
    ! [A_128,B_129] :
      ( k4_xboole_0(A_128,B_129) = k1_xboole_0
      | k1_xboole_0 != A_128 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_2066])).

tff(c_20,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2248,plain,(
    ! [B_129,A_128] :
      ( k2_xboole_0(B_129,k1_xboole_0) = k2_xboole_0(B_129,A_128)
      | k1_xboole_0 != A_128 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2179,c_20])).

tff(c_2308,plain,(
    ! [B_129] : k2_xboole_0(B_129,k1_xboole_0) = B_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_2248])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_109,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_101])).

tff(c_458,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_485,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_458])).

tff(c_496,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_485])).

tff(c_979,plain,(
    ! [A_92,B_93,C_94] : k4_xboole_0(k4_xboole_0(A_92,B_93),C_94) = k4_xboole_0(A_92,k2_xboole_0(B_93,C_94)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3680,plain,(
    ! [C_165] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_165)) = k4_xboole_0('#skF_3',C_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_979])).

tff(c_4792,plain,(
    ! [A_180] : k4_xboole_0('#skF_3',k2_xboole_0(A_180,'#skF_5')) = k4_xboole_0('#skF_3',A_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3680])).

tff(c_40,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_126,plain,(
    ! [A_45,B_46] :
      ( k2_xboole_0(A_45,B_46) = B_46
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_137,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_126])).

tff(c_722,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),k2_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_685])).

tff(c_745,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_722])).

tff(c_4833,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4792,c_745])).

tff(c_4955,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4833,c_20])).

tff(c_4978,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_4955])).

tff(c_52,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_30,B_31] : r1_tarski(A_30,k2_xboole_0(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_67,plain,(
    ! [A_37,B_36] : r1_tarski(A_37,k2_xboole_0(B_36,A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_34])).

tff(c_5210,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4978,c_67])).

tff(c_5244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_5210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:55:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.64/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.86  
% 4.64/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.86  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.64/1.86  
% 4.64/1.86  %Foreground sorts:
% 4.64/1.86  
% 4.64/1.86  
% 4.64/1.86  %Background operators:
% 4.64/1.86  
% 4.64/1.86  
% 4.64/1.86  %Foreground operators:
% 4.64/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.64/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.64/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.64/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.64/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.64/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.64/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.64/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.64/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.64/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.64/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.64/1.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.64/1.86  
% 4.64/1.88  tff(f_90, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.64/1.88  tff(f_71, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.64/1.88  tff(f_73, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.64/1.88  tff(f_81, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.64/1.88  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.64/1.88  tff(f_79, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.64/1.88  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.64/1.88  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.64/1.88  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.64/1.88  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.64/1.88  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.64/1.88  tff(f_75, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.64/1.88  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.64/1.88  tff(f_83, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.64/1.88  tff(c_36, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.64/1.88  tff(c_22, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.64/1.88  tff(c_685, plain, (![A_81, B_82]: (k4_xboole_0(k2_xboole_0(A_81, B_82), B_82)=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.64/1.88  tff(c_704, plain, (![A_81]: (k4_xboole_0(A_81, k1_xboole_0)=k2_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_685, c_22])).
% 4.64/1.88  tff(c_739, plain, (![A_81]: (k2_xboole_0(A_81, k1_xboole_0)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_704])).
% 4.64/1.88  tff(c_32, plain, (![A_29]: (r1_xboole_0(A_29, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.64/1.88  tff(c_101, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.64/1.88  tff(c_108, plain, (![A_29]: (k3_xboole_0(A_29, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_101])).
% 4.64/1.88  tff(c_279, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.64/1.88  tff(c_303, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_279])).
% 4.64/1.88  tff(c_308, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_303])).
% 4.64/1.88  tff(c_30, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.64/1.88  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.64/1.88  tff(c_309, plain, (![A_65]: (k4_xboole_0(A_65, A_65)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_303])).
% 4.64/1.88  tff(c_314, plain, (![A_65]: (k4_xboole_0(A_65, k1_xboole_0)=k3_xboole_0(A_65, A_65))), inference(superposition, [status(thm), theory('equality')], [c_309, c_30])).
% 4.64/1.88  tff(c_335, plain, (![A_65]: (k3_xboole_0(A_65, A_65)=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_314])).
% 4.64/1.88  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.64/1.88  tff(c_343, plain, (![A_66]: (k3_xboole_0(A_66, A_66)=A_66)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_314])).
% 4.64/1.88  tff(c_16, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.64/1.88  tff(c_444, plain, (![A_69, C_70]: (~r1_xboole_0(A_69, A_69) | ~r2_hidden(C_70, A_69))), inference(superposition, [status(thm), theory('equality')], [c_343, c_16])).
% 4.64/1.88  tff(c_450, plain, (![C_70, B_4]: (~r2_hidden(C_70, B_4) | k3_xboole_0(B_4, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_444])).
% 4.64/1.88  tff(c_580, plain, (![C_74, B_75]: (~r2_hidden(C_74, B_75) | k1_xboole_0!=B_75)), inference(demodulation, [status(thm), theory('equality')], [c_335, c_450])).
% 4.64/1.88  tff(c_606, plain, (![A_78, B_79]: (k1_xboole_0!=A_78 | r1_xboole_0(A_78, B_79))), inference(resolution, [status(thm)], [c_12, c_580])).
% 4.64/1.88  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.64/1.88  tff(c_1534, plain, (![A_109, B_110]: (k3_xboole_0(A_109, B_110)=k1_xboole_0 | k1_xboole_0!=A_109)), inference(resolution, [status(thm)], [c_606, c_4])).
% 4.64/1.88  tff(c_28, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k3_xboole_0(A_25, B_26))=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.64/1.88  tff(c_1557, plain, (![A_109, B_110]: (k4_xboole_0(A_109, k1_xboole_0)=k4_xboole_0(A_109, B_110) | k1_xboole_0!=A_109)), inference(superposition, [status(thm), theory('equality')], [c_1534, c_28])).
% 4.64/1.88  tff(c_1730, plain, (![A_117, B_118]: (k4_xboole_0(A_117, B_118)=A_117 | k1_xboole_0!=A_117)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1557])).
% 4.64/1.88  tff(c_2037, plain, (![A_121, B_122]: (k3_xboole_0(A_121, B_122)=A_121 | k1_xboole_0!=A_121)), inference(superposition, [status(thm), theory('equality')], [c_30, c_1730])).
% 4.64/1.88  tff(c_2066, plain, (![A_121, B_122]: (k4_xboole_0(A_121, B_122)=k4_xboole_0(A_121, A_121) | k1_xboole_0!=A_121)), inference(superposition, [status(thm), theory('equality')], [c_2037, c_28])).
% 4.64/1.88  tff(c_2179, plain, (![A_128, B_129]: (k4_xboole_0(A_128, B_129)=k1_xboole_0 | k1_xboole_0!=A_128)), inference(demodulation, [status(thm), theory('equality')], [c_308, c_2066])).
% 4.64/1.88  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.64/1.88  tff(c_2248, plain, (![B_129, A_128]: (k2_xboole_0(B_129, k1_xboole_0)=k2_xboole_0(B_129, A_128) | k1_xboole_0!=A_128)), inference(superposition, [status(thm), theory('equality')], [c_2179, c_20])).
% 4.64/1.88  tff(c_2308, plain, (![B_129]: (k2_xboole_0(B_129, k1_xboole_0)=B_129)), inference(demodulation, [status(thm), theory('equality')], [c_739, c_2248])).
% 4.64/1.88  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.64/1.88  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.64/1.88  tff(c_109, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_101])).
% 4.64/1.88  tff(c_458, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.64/1.88  tff(c_485, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_109, c_458])).
% 4.64/1.88  tff(c_496, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_485])).
% 4.64/1.88  tff(c_979, plain, (![A_92, B_93, C_94]: (k4_xboole_0(k4_xboole_0(A_92, B_93), C_94)=k4_xboole_0(A_92, k2_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.64/1.88  tff(c_3680, plain, (![C_165]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_165))=k4_xboole_0('#skF_3', C_165))), inference(superposition, [status(thm), theory('equality')], [c_496, c_979])).
% 4.64/1.88  tff(c_4792, plain, (![A_180]: (k4_xboole_0('#skF_3', k2_xboole_0(A_180, '#skF_5'))=k4_xboole_0('#skF_3', A_180))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3680])).
% 4.64/1.88  tff(c_40, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.64/1.88  tff(c_126, plain, (![A_45, B_46]: (k2_xboole_0(A_45, B_46)=B_46 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.64/1.88  tff(c_137, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_126])).
% 4.64/1.88  tff(c_722, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), k2_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_685])).
% 4.64/1.88  tff(c_745, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_308, c_722])).
% 4.64/1.88  tff(c_4833, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4792, c_745])).
% 4.64/1.88  tff(c_4955, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4833, c_20])).
% 4.64/1.88  tff(c_4978, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2308, c_4955])).
% 4.64/1.88  tff(c_52, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.64/1.88  tff(c_34, plain, (![A_30, B_31]: (r1_tarski(A_30, k2_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.64/1.88  tff(c_67, plain, (![A_37, B_36]: (r1_tarski(A_37, k2_xboole_0(B_36, A_37)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_34])).
% 4.64/1.88  tff(c_5210, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4978, c_67])).
% 4.64/1.88  tff(c_5244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_5210])).
% 4.64/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.88  
% 4.64/1.88  Inference rules
% 4.64/1.88  ----------------------
% 4.64/1.88  #Ref     : 1
% 4.64/1.88  #Sup     : 1335
% 4.64/1.88  #Fact    : 0
% 4.64/1.88  #Define  : 0
% 4.64/1.88  #Split   : 2
% 4.64/1.88  #Chain   : 0
% 4.64/1.88  #Close   : 0
% 4.64/1.88  
% 4.64/1.88  Ordering : KBO
% 4.64/1.88  
% 4.64/1.88  Simplification rules
% 4.64/1.88  ----------------------
% 4.64/1.88  #Subsume      : 231
% 4.64/1.88  #Demod        : 1040
% 4.64/1.88  #Tautology    : 799
% 4.64/1.88  #SimpNegUnit  : 22
% 4.64/1.88  #BackRed      : 3
% 4.64/1.88  
% 4.64/1.88  #Partial instantiations: 0
% 4.64/1.88  #Strategies tried      : 1
% 4.64/1.88  
% 4.64/1.88  Timing (in seconds)
% 4.64/1.88  ----------------------
% 4.64/1.88  Preprocessing        : 0.28
% 4.64/1.88  Parsing              : 0.16
% 4.64/1.88  CNF conversion       : 0.02
% 4.64/1.88  Main loop            : 0.85
% 4.64/1.88  Inferencing          : 0.25
% 4.64/1.88  Reduction            : 0.39
% 4.64/1.88  Demodulation         : 0.32
% 4.64/1.88  BG Simplification    : 0.03
% 4.64/1.89  Subsumption          : 0.13
% 4.64/1.89  Abstraction          : 0.03
% 4.64/1.89  MUC search           : 0.00
% 4.64/1.89  Cooper               : 0.00
% 4.64/1.89  Total                : 1.16
% 4.64/1.89  Index Insertion      : 0.00
% 4.64/1.89  Index Deletion       : 0.00
% 4.64/1.89  Index Matching       : 0.00
% 4.64/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
