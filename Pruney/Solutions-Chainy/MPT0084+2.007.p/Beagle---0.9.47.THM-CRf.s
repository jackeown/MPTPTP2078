%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:05 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 184 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :   80 ( 194 expanded)
%              Number of equality atoms :   50 ( 148 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_38,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_164,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_167,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,k4_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_22])).

tff(c_679,plain,(
    ! [A_70,B_71] : k3_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_167])).

tff(c_28,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_359,plain,(
    ! [A_58,B_59] : k2_xboole_0(A_58,k4_xboole_0(B_59,A_58)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_382,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_xboole_0(A_16,B_17),k4_xboole_0(A_16,B_17)) = k2_xboole_0(k3_xboole_0(A_16,B_17),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_359])).

tff(c_395,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2,c_382])).

tff(c_692,plain,(
    ! [A_70,B_71] : k2_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = A_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_395])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_91,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_99,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_91])).

tff(c_185,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_164])).

tff(c_194,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_185])).

tff(c_1258,plain,(
    ! [A_86,B_87,C_88] : k2_xboole_0(k4_xboole_0(A_86,B_87),k3_xboole_0(A_86,C_88)) = k4_xboole_0(A_86,k4_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1309,plain,(
    ! [B_87] : k4_xboole_0('#skF_3',k4_xboole_0(B_87,'#skF_5')) = k2_xboole_0(k4_xboole_0('#skF_3',B_87),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_1258])).

tff(c_1347,plain,(
    ! [B_87] : k4_xboole_0('#skF_3',k4_xboole_0(B_87,'#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_2,c_1309])).

tff(c_14,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_117,plain,(
    ! [A_44,B_45] : k2_xboole_0(k3_xboole_0(A_44,B_45),k4_xboole_0(A_44,B_45)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_132,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_12,k1_xboole_0)) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_117])).

tff(c_138,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_132])).

tff(c_34,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_324,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,k3_xboole_0(A_52,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_559,plain,(
    ! [A_65,B_66] :
      ( ~ r1_xboole_0(A_65,B_66)
      | k3_xboole_0(A_65,B_66) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_324])).

tff(c_566,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_559])).

tff(c_1294,plain,(
    ! [B_87] : k4_xboole_0('#skF_3',k4_xboole_0(B_87,k3_xboole_0('#skF_4','#skF_5'))) = k2_xboole_0(k4_xboole_0('#skF_3',B_87),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_1258])).

tff(c_2071,plain,(
    ! [B_105] : k4_xboole_0('#skF_3',k4_xboole_0(B_105,k3_xboole_0('#skF_4','#skF_5'))) = k4_xboole_0('#skF_3',B_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_2,c_1294])).

tff(c_2146,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2071])).

tff(c_2161,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_2146])).

tff(c_188,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_164])).

tff(c_196,plain,(
    ! [A_49] : k4_xboole_0(A_49,A_49) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_188])).

tff(c_201,plain,(
    ! [A_49] : k4_xboole_0(A_49,k1_xboole_0) = k3_xboole_0(A_49,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_22])).

tff(c_216,plain,(
    ! [A_49] : k3_xboole_0(A_49,A_49) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_201])).

tff(c_1306,plain,(
    ! [A_49,B_87] : k4_xboole_0(A_49,k4_xboole_0(B_87,A_49)) = k2_xboole_0(k4_xboole_0(A_49,B_87),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_1258])).

tff(c_1346,plain,(
    ! [A_49,B_87] : k4_xboole_0(A_49,k4_xboole_0(B_87,A_49)) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_2,c_1306])).

tff(c_32,plain,(
    ! [A_31] : r1_xboole_0(A_31,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_337,plain,(
    ! [A_12,C_54] :
      ( ~ r1_xboole_0(A_12,k1_xboole_0)
      | ~ r2_hidden(C_54,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_324])).

tff(c_340,plain,(
    ! [C_54] : ~ r2_hidden(C_54,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_337])).

tff(c_195,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_188])).

tff(c_1354,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(B_90,A_89)) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_2,c_1306])).

tff(c_1391,plain,(
    ! [A_89,B_90] : k3_xboole_0(A_89,k4_xboole_0(B_90,A_89)) = k4_xboole_0(A_89,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_1354,c_22])).

tff(c_1517,plain,(
    ! [A_92,B_93] : k3_xboole_0(A_92,k4_xboole_0(B_93,A_92)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_1391])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1537,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92,k4_xboole_0(B_93,A_92)),k1_xboole_0)
      | r1_xboole_0(A_92,k4_xboole_0(B_93,A_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_4])).

tff(c_1709,plain,(
    ! [A_95,B_96] : r1_xboole_0(A_95,k4_xboole_0(B_96,A_95)) ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_1537])).

tff(c_1721,plain,(
    ! [B_87,A_49] : r1_xboole_0(k4_xboole_0(B_87,A_49),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_1346,c_1709])).

tff(c_2165,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2161,c_1721])).

tff(c_2196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.56  
% 3.50/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.50/1.57  
% 3.50/1.57  %Foreground sorts:
% 3.50/1.57  
% 3.50/1.57  
% 3.50/1.57  %Background operators:
% 3.50/1.57  
% 3.50/1.57  
% 3.50/1.57  %Foreground operators:
% 3.50/1.57  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.50/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.50/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.50/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.50/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.50/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.50/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.50/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.50/1.57  
% 3.63/1.58  tff(f_82, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.63/1.58  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.63/1.58  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.63/1.58  tff(f_69, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.63/1.58  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.63/1.58  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.63/1.58  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.63/1.58  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.63/1.58  tff(f_71, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.63/1.58  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.63/1.58  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.63/1.58  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.63/1.58  tff(f_73, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.63/1.58  tff(c_38, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.63/1.58  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.63/1.58  tff(c_164, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.63/1.58  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.63/1.58  tff(c_167, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k3_xboole_0(A_47, k4_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_164, c_22])).
% 3.63/1.58  tff(c_679, plain, (![A_70, B_71]: (k3_xboole_0(A_70, k4_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_167])).
% 3.63/1.58  tff(c_28, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.63/1.58  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.63/1.58  tff(c_359, plain, (![A_58, B_59]: (k2_xboole_0(A_58, k4_xboole_0(B_59, A_58))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.63/1.58  tff(c_382, plain, (![A_16, B_17]: (k2_xboole_0(k3_xboole_0(A_16, B_17), k4_xboole_0(A_16, B_17))=k2_xboole_0(k3_xboole_0(A_16, B_17), A_16))), inference(superposition, [status(thm), theory('equality')], [c_20, c_359])).
% 3.63/1.58  tff(c_395, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k3_xboole_0(A_16, B_17))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2, c_382])).
% 3.63/1.58  tff(c_692, plain, (![A_70, B_71]: (k2_xboole_0(A_70, k4_xboole_0(A_70, B_71))=A_70)), inference(superposition, [status(thm), theory('equality')], [c_679, c_395])).
% 3.63/1.58  tff(c_18, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.63/1.58  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.63/1.58  tff(c_91, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.63/1.58  tff(c_99, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_91])).
% 3.63/1.58  tff(c_185, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_99, c_164])).
% 3.63/1.58  tff(c_194, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_185])).
% 3.63/1.58  tff(c_1258, plain, (![A_86, B_87, C_88]: (k2_xboole_0(k4_xboole_0(A_86, B_87), k3_xboole_0(A_86, C_88))=k4_xboole_0(A_86, k4_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.63/1.58  tff(c_1309, plain, (![B_87]: (k4_xboole_0('#skF_3', k4_xboole_0(B_87, '#skF_5'))=k2_xboole_0(k4_xboole_0('#skF_3', B_87), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_194, c_1258])).
% 3.63/1.58  tff(c_1347, plain, (![B_87]: (k4_xboole_0('#skF_3', k4_xboole_0(B_87, '#skF_5'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_692, c_2, c_1309])).
% 3.63/1.58  tff(c_14, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.63/1.58  tff(c_117, plain, (![A_44, B_45]: (k2_xboole_0(k3_xboole_0(A_44, B_45), k4_xboole_0(A_44, B_45))=A_44)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.63/1.58  tff(c_132, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_12, k1_xboole_0))=A_12)), inference(superposition, [status(thm), theory('equality')], [c_14, c_117])).
% 3.63/1.58  tff(c_138, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, A_12)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_132])).
% 3.63/1.58  tff(c_34, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.63/1.58  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.63/1.58  tff(c_324, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, k3_xboole_0(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.63/1.58  tff(c_559, plain, (![A_65, B_66]: (~r1_xboole_0(A_65, B_66) | k3_xboole_0(A_65, B_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_324])).
% 3.63/1.58  tff(c_566, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_559])).
% 3.63/1.58  tff(c_1294, plain, (![B_87]: (k4_xboole_0('#skF_3', k4_xboole_0(B_87, k3_xboole_0('#skF_4', '#skF_5')))=k2_xboole_0(k4_xboole_0('#skF_3', B_87), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_566, c_1258])).
% 3.63/1.58  tff(c_2071, plain, (![B_105]: (k4_xboole_0('#skF_3', k4_xboole_0(B_105, k3_xboole_0('#skF_4', '#skF_5')))=k4_xboole_0('#skF_3', B_105))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_2, c_1294])).
% 3.63/1.58  tff(c_2146, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20, c_2071])).
% 3.63/1.58  tff(c_2161, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_2146])).
% 3.63/1.58  tff(c_188, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_164])).
% 3.63/1.58  tff(c_196, plain, (![A_49]: (k4_xboole_0(A_49, A_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_188])).
% 3.63/1.58  tff(c_201, plain, (![A_49]: (k4_xboole_0(A_49, k1_xboole_0)=k3_xboole_0(A_49, A_49))), inference(superposition, [status(thm), theory('equality')], [c_196, c_22])).
% 3.63/1.58  tff(c_216, plain, (![A_49]: (k3_xboole_0(A_49, A_49)=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_201])).
% 3.63/1.58  tff(c_1306, plain, (![A_49, B_87]: (k4_xboole_0(A_49, k4_xboole_0(B_87, A_49))=k2_xboole_0(k4_xboole_0(A_49, B_87), A_49))), inference(superposition, [status(thm), theory('equality')], [c_216, c_1258])).
% 3.63/1.58  tff(c_1346, plain, (![A_49, B_87]: (k4_xboole_0(A_49, k4_xboole_0(B_87, A_49))=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_692, c_2, c_1306])).
% 3.63/1.58  tff(c_32, plain, (![A_31]: (r1_xboole_0(A_31, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.63/1.58  tff(c_337, plain, (![A_12, C_54]: (~r1_xboole_0(A_12, k1_xboole_0) | ~r2_hidden(C_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_324])).
% 3.63/1.58  tff(c_340, plain, (![C_54]: (~r2_hidden(C_54, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_337])).
% 3.63/1.58  tff(c_195, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_188])).
% 3.63/1.58  tff(c_1354, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(B_90, A_89))=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_692, c_2, c_1306])).
% 3.63/1.58  tff(c_1391, plain, (![A_89, B_90]: (k3_xboole_0(A_89, k4_xboole_0(B_90, A_89))=k4_xboole_0(A_89, A_89))), inference(superposition, [status(thm), theory('equality')], [c_1354, c_22])).
% 3.63/1.58  tff(c_1517, plain, (![A_92, B_93]: (k3_xboole_0(A_92, k4_xboole_0(B_93, A_92))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_1391])).
% 3.63/1.58  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.63/1.58  tff(c_1537, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92, k4_xboole_0(B_93, A_92)), k1_xboole_0) | r1_xboole_0(A_92, k4_xboole_0(B_93, A_92)))), inference(superposition, [status(thm), theory('equality')], [c_1517, c_4])).
% 3.63/1.58  tff(c_1709, plain, (![A_95, B_96]: (r1_xboole_0(A_95, k4_xboole_0(B_96, A_95)))), inference(negUnitSimplification, [status(thm)], [c_340, c_1537])).
% 3.63/1.58  tff(c_1721, plain, (![B_87, A_49]: (r1_xboole_0(k4_xboole_0(B_87, A_49), A_49))), inference(superposition, [status(thm), theory('equality')], [c_1346, c_1709])).
% 3.63/1.58  tff(c_2165, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2161, c_1721])).
% 3.63/1.58  tff(c_2196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_2165])).
% 3.63/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.58  
% 3.63/1.58  Inference rules
% 3.63/1.58  ----------------------
% 3.63/1.58  #Ref     : 0
% 3.63/1.58  #Sup     : 538
% 3.63/1.58  #Fact    : 0
% 3.63/1.58  #Define  : 0
% 3.63/1.58  #Split   : 1
% 3.63/1.58  #Chain   : 0
% 3.63/1.58  #Close   : 0
% 3.63/1.58  
% 3.63/1.58  Ordering : KBO
% 3.63/1.58  
% 3.63/1.58  Simplification rules
% 3.63/1.58  ----------------------
% 3.63/1.58  #Subsume      : 9
% 3.63/1.58  #Demod        : 471
% 3.63/1.58  #Tautology    : 350
% 3.63/1.58  #SimpNegUnit  : 10
% 3.63/1.58  #BackRed      : 1
% 3.63/1.58  
% 3.63/1.58  #Partial instantiations: 0
% 3.63/1.58  #Strategies tried      : 1
% 3.63/1.58  
% 3.63/1.58  Timing (in seconds)
% 3.63/1.58  ----------------------
% 3.63/1.59  Preprocessing        : 0.29
% 3.63/1.59  Parsing              : 0.16
% 3.63/1.59  CNF conversion       : 0.02
% 3.63/1.59  Main loop            : 0.51
% 3.63/1.59  Inferencing          : 0.17
% 3.63/1.59  Reduction            : 0.22
% 3.63/1.59  Demodulation         : 0.17
% 3.63/1.59  BG Simplification    : 0.02
% 3.63/1.59  Subsumption          : 0.07
% 3.63/1.59  Abstraction          : 0.03
% 3.63/1.59  MUC search           : 0.00
% 3.63/1.59  Cooper               : 0.00
% 3.63/1.59  Total                : 0.84
% 3.63/1.59  Index Insertion      : 0.00
% 3.63/1.59  Index Deletion       : 0.00
% 3.63/1.59  Index Matching       : 0.00
% 3.63/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
