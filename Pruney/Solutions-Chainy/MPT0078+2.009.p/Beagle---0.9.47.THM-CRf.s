%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:40 EST 2020

% Result     : Theorem 5.76s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 281 expanded)
%              Number of leaves         :   26 ( 109 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 318 expanded)
%              Number of equality atoms :   65 ( 267 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_26,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_231,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_283,plain,(
    ! [A_40,B_41] :
      ( ~ r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_231])).

tff(c_291,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_283])).

tff(c_396,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_405,plain,(
    ! [A_44,B_45] : k2_xboole_0(k4_xboole_0(A_44,B_45),k3_xboole_0(A_44,B_45)) = k2_xboole_0(k4_xboole_0(A_44,B_45),A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_16])).

tff(c_4986,plain,(
    ! [A_139,B_140] : k2_xboole_0(k4_xboole_0(A_139,B_140),k3_xboole_0(A_139,B_140)) = k2_xboole_0(A_139,k4_xboole_0(A_139,B_140)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_405])).

tff(c_5151,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_4986])).

tff(c_5223,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5151])).

tff(c_313,plain,(
    ! [A_42,B_43] : k4_xboole_0(k2_xboole_0(A_42,B_43),B_43) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_335,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_313])).

tff(c_32,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_33,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_32])).

tff(c_618,plain,(
    ! [B_57,A_58] : k4_xboole_0(k2_xboole_0(B_57,A_58),B_57) = k4_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_313])).

tff(c_660,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_618])).

tff(c_680,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_660])).

tff(c_840,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(k4_xboole_0(A_65,B_66),C_67) = k4_xboole_0(A_65,k2_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_417,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_396])).

tff(c_422,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_417])).

tff(c_850,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k2_xboole_0(B_66,k4_xboole_0(A_65,B_66))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_422])).

tff(c_928,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k2_xboole_0(B_69,A_68)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_850])).

tff(c_973,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_928])).

tff(c_7827,plain,(
    ! [C_173,A_174,B_175] : k2_xboole_0(C_173,k4_xboole_0(A_174,k2_xboole_0(B_175,C_173))) = k2_xboole_0(C_173,k4_xboole_0(A_174,B_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_16])).

tff(c_7982,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_5','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_7827])).

tff(c_8072,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5223,c_680,c_12,c_7982])).

tff(c_912,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k2_xboole_0(B_66,A_65)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_850])).

tff(c_319,plain,(
    ! [B_43,A_42] : k2_xboole_0(B_43,k4_xboole_0(A_42,B_43)) = k2_xboole_0(B_43,k2_xboole_0(A_42,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_16])).

tff(c_1239,plain,(
    ! [B_76,A_77] : k2_xboole_0(B_76,k2_xboole_0(A_77,B_76)) = k2_xboole_0(B_76,A_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_319])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(k2_xboole_0(A_17,B_18),B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1263,plain,(
    ! [B_76,A_77] : k4_xboole_0(k2_xboole_0(B_76,A_77),k2_xboole_0(A_77,B_76)) = k4_xboole_0(B_76,k2_xboole_0(A_77,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_20])).

tff(c_1307,plain,(
    ! [B_76,A_77] : k4_xboole_0(k2_xboole_0(B_76,A_77),k2_xboole_0(A_77,B_76)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_1263])).

tff(c_8322,plain,(
    ! [A_176] : k2_xboole_0('#skF_5',k4_xboole_0(A_176,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_5',k4_xboole_0(A_176,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_7827])).

tff(c_8407,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0(k2_xboole_0('#skF_3','#skF_4'),'#skF_4')) = k2_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1307,c_8322])).

tff(c_8462,plain,(
    k2_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8072,c_335,c_2,c_12,c_8407])).

tff(c_28,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_290,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_283])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_301,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_4])).

tff(c_24,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_770,plain,(
    k4_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_4')) = k3_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_24])).

tff(c_776,plain,(
    k4_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_4,c_770])).

tff(c_8093,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8072,c_776])).

tff(c_943,plain,(
    ! [A_68,B_69] : k3_xboole_0(A_68,k2_xboole_0(B_69,A_68)) = k4_xboole_0(A_68,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_24])).

tff(c_980,plain,(
    ! [A_68,B_69] : k3_xboole_0(A_68,k2_xboole_0(B_69,A_68)) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_943])).

tff(c_414,plain,(
    ! [A_17,B_18] : k4_xboole_0(k2_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = k3_xboole_0(k2_xboole_0(A_17,B_18),B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_396])).

tff(c_421,plain,(
    ! [A_17,B_18] : k4_xboole_0(k2_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = k3_xboole_0(B_18,k2_xboole_0(A_17,B_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_414])).

tff(c_8690,plain,(
    ! [A_177,B_178] : k4_xboole_0(k2_xboole_0(A_177,B_178),k4_xboole_0(A_177,B_178)) = B_178 ),
    inference(demodulation,[status(thm),theory(equality)],[c_980,c_421])).

tff(c_8767,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5','#skF_3'),k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8093,c_8690])).

tff(c_8922,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8462,c_18,c_2,c_8767])).

tff(c_8924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_8922])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:29:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.76/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.22  
% 5.76/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.22  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 5.76/2.22  
% 5.76/2.22  %Foreground sorts:
% 5.76/2.22  
% 5.76/2.22  
% 5.76/2.22  %Background operators:
% 5.76/2.22  
% 5.76/2.22  
% 5.76/2.22  %Foreground operators:
% 5.76/2.22  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.76/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.76/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.76/2.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.76/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.76/2.22  tff('#skF_5', type, '#skF_5': $i).
% 5.76/2.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.76/2.22  tff('#skF_3', type, '#skF_3': $i).
% 5.76/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.76/2.22  tff('#skF_4', type, '#skF_4': $i).
% 5.76/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.76/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.76/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.76/2.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.76/2.22  
% 5.76/2.23  tff(f_74, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 5.76/2.23  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.76/2.23  tff(f_53, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.76/2.23  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.76/2.23  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.76/2.23  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.76/2.23  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.76/2.23  tff(f_61, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.76/2.23  tff(f_63, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.76/2.23  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.76/2.23  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.76/2.23  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.76/2.23  tff(c_26, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.76/2.23  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.76/2.23  tff(c_12, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.76/2.23  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.76/2.23  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.76/2.23  tff(c_231, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.76/2.23  tff(c_283, plain, (![A_40, B_41]: (~r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_231])).
% 5.76/2.23  tff(c_291, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_283])).
% 5.76/2.23  tff(c_396, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.76/2.23  tff(c_16, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.76/2.23  tff(c_405, plain, (![A_44, B_45]: (k2_xboole_0(k4_xboole_0(A_44, B_45), k3_xboole_0(A_44, B_45))=k2_xboole_0(k4_xboole_0(A_44, B_45), A_44))), inference(superposition, [status(thm), theory('equality')], [c_396, c_16])).
% 5.76/2.23  tff(c_4986, plain, (![A_139, B_140]: (k2_xboole_0(k4_xboole_0(A_139, B_140), k3_xboole_0(A_139, B_140))=k2_xboole_0(A_139, k4_xboole_0(A_139, B_140)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_405])).
% 5.76/2.23  tff(c_5151, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)=k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_291, c_4986])).
% 5.76/2.23  tff(c_5223, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5151])).
% 5.76/2.23  tff(c_313, plain, (![A_42, B_43]: (k4_xboole_0(k2_xboole_0(A_42, B_43), B_43)=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.76/2.23  tff(c_335, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_313])).
% 5.76/2.23  tff(c_32, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.76/2.23  tff(c_33, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_32])).
% 5.76/2.23  tff(c_618, plain, (![B_57, A_58]: (k4_xboole_0(k2_xboole_0(B_57, A_58), B_57)=k4_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_2, c_313])).
% 5.76/2.23  tff(c_660, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_33, c_618])).
% 5.76/2.23  tff(c_680, plain, (k4_xboole_0('#skF_5', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_660])).
% 5.76/2.23  tff(c_840, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k4_xboole_0(A_65, B_66), C_67)=k4_xboole_0(A_65, k2_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.76/2.23  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.76/2.23  tff(c_18, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.76/2.23  tff(c_417, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_396])).
% 5.76/2.23  tff(c_422, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_417])).
% 5.76/2.23  tff(c_850, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k2_xboole_0(B_66, k4_xboole_0(A_65, B_66)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_840, c_422])).
% 5.76/2.23  tff(c_928, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k2_xboole_0(B_69, A_68))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_850])).
% 5.76/2.23  tff(c_973, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_33, c_928])).
% 5.76/2.23  tff(c_7827, plain, (![C_173, A_174, B_175]: (k2_xboole_0(C_173, k4_xboole_0(A_174, k2_xboole_0(B_175, C_173)))=k2_xboole_0(C_173, k4_xboole_0(A_174, B_175)))), inference(superposition, [status(thm), theory('equality')], [c_840, c_16])).
% 5.76/2.23  tff(c_7982, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_5', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_973, c_7827])).
% 5.76/2.23  tff(c_8072, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5223, c_680, c_12, c_7982])).
% 5.76/2.23  tff(c_912, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k2_xboole_0(B_66, A_65))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_850])).
% 5.76/2.23  tff(c_319, plain, (![B_43, A_42]: (k2_xboole_0(B_43, k4_xboole_0(A_42, B_43))=k2_xboole_0(B_43, k2_xboole_0(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_313, c_16])).
% 5.76/2.23  tff(c_1239, plain, (![B_76, A_77]: (k2_xboole_0(B_76, k2_xboole_0(A_77, B_76))=k2_xboole_0(B_76, A_77))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_319])).
% 5.76/2.23  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(k2_xboole_0(A_17, B_18), B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.76/2.23  tff(c_1263, plain, (![B_76, A_77]: (k4_xboole_0(k2_xboole_0(B_76, A_77), k2_xboole_0(A_77, B_76))=k4_xboole_0(B_76, k2_xboole_0(A_77, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_20])).
% 5.76/2.23  tff(c_1307, plain, (![B_76, A_77]: (k4_xboole_0(k2_xboole_0(B_76, A_77), k2_xboole_0(A_77, B_76))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_912, c_1263])).
% 5.76/2.23  tff(c_8322, plain, (![A_176]: (k2_xboole_0('#skF_5', k4_xboole_0(A_176, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_5', k4_xboole_0(A_176, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_33, c_7827])).
% 5.76/2.23  tff(c_8407, plain, (k2_xboole_0('#skF_5', k4_xboole_0(k2_xboole_0('#skF_3', '#skF_4'), '#skF_4'))=k2_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1307, c_8322])).
% 5.76/2.23  tff(c_8462, plain, (k2_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8072, c_335, c_2, c_12, c_8407])).
% 5.76/2.23  tff(c_28, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.76/2.23  tff(c_290, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_283])).
% 5.76/2.23  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.76/2.23  tff(c_301, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_290, c_4])).
% 5.76/2.23  tff(c_24, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.76/2.23  tff(c_770, plain, (k4_xboole_0('#skF_5', k4_xboole_0('#skF_3', '#skF_4'))=k3_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_680, c_24])).
% 5.76/2.23  tff(c_776, plain, (k4_xboole_0('#skF_5', k4_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_301, c_4, c_770])).
% 5.76/2.23  tff(c_8093, plain, (k4_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8072, c_776])).
% 5.76/2.23  tff(c_943, plain, (![A_68, B_69]: (k3_xboole_0(A_68, k2_xboole_0(B_69, A_68))=k4_xboole_0(A_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_928, c_24])).
% 5.76/2.23  tff(c_980, plain, (![A_68, B_69]: (k3_xboole_0(A_68, k2_xboole_0(B_69, A_68))=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_943])).
% 5.76/2.23  tff(c_414, plain, (![A_17, B_18]: (k4_xboole_0(k2_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=k3_xboole_0(k2_xboole_0(A_17, B_18), B_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_396])).
% 5.76/2.23  tff(c_421, plain, (![A_17, B_18]: (k4_xboole_0(k2_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=k3_xboole_0(B_18, k2_xboole_0(A_17, B_18)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_414])).
% 5.76/2.23  tff(c_8690, plain, (![A_177, B_178]: (k4_xboole_0(k2_xboole_0(A_177, B_178), k4_xboole_0(A_177, B_178))=B_178)), inference(demodulation, [status(thm), theory('equality')], [c_980, c_421])).
% 5.76/2.23  tff(c_8767, plain, (k4_xboole_0(k2_xboole_0('#skF_5', '#skF_3'), k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8093, c_8690])).
% 5.76/2.23  tff(c_8922, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8462, c_18, c_2, c_8767])).
% 5.76/2.23  tff(c_8924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_8922])).
% 5.76/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.23  
% 5.76/2.23  Inference rules
% 5.76/2.23  ----------------------
% 5.76/2.23  #Ref     : 0
% 5.76/2.23  #Sup     : 2252
% 5.76/2.23  #Fact    : 0
% 5.76/2.23  #Define  : 0
% 5.76/2.23  #Split   : 1
% 5.76/2.23  #Chain   : 0
% 5.76/2.23  #Close   : 0
% 5.76/2.23  
% 5.76/2.23  Ordering : KBO
% 5.76/2.23  
% 5.76/2.23  Simplification rules
% 5.76/2.23  ----------------------
% 5.76/2.23  #Subsume      : 31
% 5.76/2.23  #Demod        : 2455
% 5.76/2.23  #Tautology    : 1613
% 5.76/2.23  #SimpNegUnit  : 19
% 5.76/2.23  #BackRed      : 12
% 5.76/2.23  
% 5.76/2.23  #Partial instantiations: 0
% 5.76/2.23  #Strategies tried      : 1
% 5.76/2.23  
% 5.76/2.23  Timing (in seconds)
% 5.76/2.23  ----------------------
% 5.76/2.24  Preprocessing        : 0.30
% 5.76/2.24  Parsing              : 0.17
% 5.76/2.24  CNF conversion       : 0.02
% 5.76/2.24  Main loop            : 1.17
% 5.76/2.24  Inferencing          : 0.31
% 5.76/2.24  Reduction            : 0.60
% 5.76/2.24  Demodulation         : 0.52
% 5.76/2.24  BG Simplification    : 0.03
% 5.76/2.24  Subsumption          : 0.16
% 5.76/2.24  Abstraction          : 0.05
% 5.76/2.24  MUC search           : 0.00
% 5.76/2.24  Cooper               : 0.00
% 5.76/2.24  Total                : 1.50
% 5.76/2.24  Index Insertion      : 0.00
% 5.76/2.24  Index Deletion       : 0.00
% 5.76/2.24  Index Matching       : 0.00
% 5.76/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
