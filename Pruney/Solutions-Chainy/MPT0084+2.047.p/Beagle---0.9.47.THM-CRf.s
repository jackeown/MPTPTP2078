%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:10 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 202 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :   20
%              Number of atoms          :   86 ( 313 expanded)
%              Number of equality atoms :   32 (  81 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [A_37,B_38] :
      ( ~ r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_94,plain,(
    ! [A_21] : k3_xboole_0(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_78])).

tff(c_42,plain,(
    ! [B_27,A_28] :
      ( r1_xboole_0(B_27,A_28)
      | ~ r1_xboole_0(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_21] : r1_xboole_0(k1_xboole_0,A_21) ),
    inference(resolution,[status(thm)],[c_22,c_42])).

tff(c_95,plain,(
    ! [A_39] : k3_xboole_0(k1_xboole_0,A_39) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_78])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_100,plain,(
    ! [A_39,C_7] :
      ( ~ r1_xboole_0(k1_xboole_0,A_39)
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_6])).

tff(c_105,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_100])).

tff(c_512,plain,(
    ! [A_58,B_59,C_60] : k3_xboole_0(k3_xboole_0(A_58,B_59),C_60) = k3_xboole_0(A_58,k3_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_47,plain,(
    r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_42])).

tff(c_91,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_5'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47,c_78])).

tff(c_538,plain,(
    k3_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_91])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_629,plain,
    ( r2_hidden('#skF_1'('#skF_4',k3_xboole_0('#skF_5','#skF_3')),k1_xboole_0)
    | r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_4])).

tff(c_641,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_629])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_652,plain,(
    r1_xboole_0(k3_xboole_0('#skF_5','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_641,c_2])).

tff(c_77,plain,(
    ! [A_34,B_35] :
      ( ~ r1_xboole_0(A_34,B_35)
      | k3_xboole_0(A_34,B_35) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_660,plain,(
    k3_xboole_0(k3_xboole_0('#skF_5','#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_652,c_77])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k3_xboole_0(k3_xboole_0(A_12,B_13),C_14) = k3_xboole_0(A_12,k3_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_669,plain,(
    k3_xboole_0('#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_14])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_58,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_62,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_58])).

tff(c_179,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_194,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_179])).

tff(c_200,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_194])).

tff(c_1218,plain,(
    ! [C_70] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_5',C_70)) = k3_xboole_0('#skF_3',C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_512])).

tff(c_1254,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) = k3_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_1218])).

tff(c_1275,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1254])).

tff(c_197,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_179])).

tff(c_201,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_197])).

tff(c_310,plain,(
    ! [A_52,B_53,C_54] : k4_xboole_0(k3_xboole_0(A_52,B_53),C_54) = k3_xboole_0(A_52,k4_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_409,plain,(
    ! [A_56,B_57] : k3_xboole_0(A_56,k4_xboole_0(B_57,k3_xboole_0(A_56,B_57))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_310])).

tff(c_420,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_1'(A_56,k4_xboole_0(B_57,k3_xboole_0(A_56,B_57))),k1_xboole_0)
      | r1_xboole_0(A_56,k4_xboole_0(B_57,k3_xboole_0(A_56,B_57))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_4])).

tff(c_992,plain,(
    ! [A_65,B_66] : r1_xboole_0(A_65,k4_xboole_0(B_66,k3_xboole_0(A_65,B_66))) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_420])).

tff(c_1056,plain,(
    ! [B_66,A_65] : r1_xboole_0(k4_xboole_0(B_66,k3_xboole_0(A_65,B_66)),A_65) ),
    inference(resolution,[status(thm)],[c_992,c_2])).

tff(c_1282,plain,(
    r1_xboole_0(k4_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k1_xboole_0),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1275,c_1056])).

tff(c_1309,plain,(
    r1_xboole_0(k3_xboole_0('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1282])).

tff(c_1324,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1309,c_77])).

tff(c_1552,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1324,c_14])).

tff(c_1596,plain,(
    r1_xboole_0(k4_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_xboole_0),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1552,c_1056])).

tff(c_1626,plain,(
    r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1596])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( ~ r1_xboole_0(k3_xboole_0(A_22,B_23),B_23)
      | r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1644,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1626,c_24])).

tff(c_1651,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1644,c_2])).

tff(c_1656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1651])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.53  
% 3.36/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.42/1.53  
% 3.42/1.53  %Foreground sorts:
% 3.42/1.53  
% 3.42/1.53  
% 3.42/1.53  %Background operators:
% 3.42/1.53  
% 3.42/1.53  
% 3.42/1.53  %Foreground operators:
% 3.42/1.53  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.42/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.42/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.42/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.42/1.53  
% 3.42/1.55  tff(f_80, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.42/1.55  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.42/1.55  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.42/1.55  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.42/1.55  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.42/1.55  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.42/1.55  tff(f_57, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.42/1.55  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.42/1.55  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.42/1.55  tff(f_63, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.42/1.55  tff(f_71, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.42/1.55  tff(c_30, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.42/1.55  tff(c_16, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.42/1.55  tff(c_22, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.42/1.55  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.42/1.55  tff(c_72, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.42/1.55  tff(c_78, plain, (![A_37, B_38]: (~r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_72])).
% 3.42/1.55  tff(c_94, plain, (![A_21]: (k3_xboole_0(A_21, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_78])).
% 3.42/1.55  tff(c_42, plain, (![B_27, A_28]: (r1_xboole_0(B_27, A_28) | ~r1_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.55  tff(c_48, plain, (![A_21]: (r1_xboole_0(k1_xboole_0, A_21))), inference(resolution, [status(thm)], [c_22, c_42])).
% 3.42/1.55  tff(c_95, plain, (![A_39]: (k3_xboole_0(k1_xboole_0, A_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_78])).
% 3.42/1.55  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.42/1.55  tff(c_100, plain, (![A_39, C_7]: (~r1_xboole_0(k1_xboole_0, A_39) | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_95, c_6])).
% 3.42/1.55  tff(c_105, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_100])).
% 3.42/1.55  tff(c_512, plain, (![A_58, B_59, C_60]: (k3_xboole_0(k3_xboole_0(A_58, B_59), C_60)=k3_xboole_0(A_58, k3_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.42/1.55  tff(c_26, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.42/1.55  tff(c_47, plain, (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_26, c_42])).
% 3.42/1.55  tff(c_91, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_47, c_78])).
% 3.42/1.55  tff(c_538, plain, (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_512, c_91])).
% 3.42/1.55  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.42/1.55  tff(c_629, plain, (r2_hidden('#skF_1'('#skF_4', k3_xboole_0('#skF_5', '#skF_3')), k1_xboole_0) | r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_538, c_4])).
% 3.42/1.55  tff(c_641, plain, (r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_105, c_629])).
% 3.42/1.55  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.55  tff(c_652, plain, (r1_xboole_0(k3_xboole_0('#skF_5', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_641, c_2])).
% 3.42/1.55  tff(c_77, plain, (![A_34, B_35]: (~r1_xboole_0(A_34, B_35) | k3_xboole_0(A_34, B_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_72])).
% 3.42/1.55  tff(c_660, plain, (k3_xboole_0(k3_xboole_0('#skF_5', '#skF_3'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_652, c_77])).
% 3.42/1.55  tff(c_14, plain, (![A_12, B_13, C_14]: (k3_xboole_0(k3_xboole_0(A_12, B_13), C_14)=k3_xboole_0(A_12, k3_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.42/1.55  tff(c_669, plain, (k3_xboole_0('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_660, c_14])).
% 3.42/1.55  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.42/1.55  tff(c_58, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.42/1.55  tff(c_62, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_58])).
% 3.42/1.55  tff(c_179, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.42/1.55  tff(c_194, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_62, c_179])).
% 3.42/1.55  tff(c_200, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_194])).
% 3.42/1.55  tff(c_1218, plain, (![C_70]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_5', C_70))=k3_xboole_0('#skF_3', C_70))), inference(superposition, [status(thm), theory('equality')], [c_200, c_512])).
% 3.42/1.55  tff(c_1254, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_669, c_1218])).
% 3.42/1.55  tff(c_1275, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1254])).
% 3.42/1.55  tff(c_197, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_179])).
% 3.42/1.55  tff(c_201, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_197])).
% 3.42/1.55  tff(c_310, plain, (![A_52, B_53, C_54]: (k4_xboole_0(k3_xboole_0(A_52, B_53), C_54)=k3_xboole_0(A_52, k4_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.42/1.55  tff(c_409, plain, (![A_56, B_57]: (k3_xboole_0(A_56, k4_xboole_0(B_57, k3_xboole_0(A_56, B_57)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_201, c_310])).
% 3.42/1.55  tff(c_420, plain, (![A_56, B_57]: (r2_hidden('#skF_1'(A_56, k4_xboole_0(B_57, k3_xboole_0(A_56, B_57))), k1_xboole_0) | r1_xboole_0(A_56, k4_xboole_0(B_57, k3_xboole_0(A_56, B_57))))), inference(superposition, [status(thm), theory('equality')], [c_409, c_4])).
% 3.42/1.55  tff(c_992, plain, (![A_65, B_66]: (r1_xboole_0(A_65, k4_xboole_0(B_66, k3_xboole_0(A_65, B_66))))), inference(negUnitSimplification, [status(thm)], [c_105, c_420])).
% 3.42/1.55  tff(c_1056, plain, (![B_66, A_65]: (r1_xboole_0(k4_xboole_0(B_66, k3_xboole_0(A_65, B_66)), A_65))), inference(resolution, [status(thm)], [c_992, c_2])).
% 3.42/1.55  tff(c_1282, plain, (r1_xboole_0(k4_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k1_xboole_0), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1275, c_1056])).
% 3.42/1.55  tff(c_1309, plain, (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1282])).
% 3.42/1.55  tff(c_1324, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1309, c_77])).
% 3.42/1.55  tff(c_1552, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1324, c_14])).
% 3.42/1.55  tff(c_1596, plain, (r1_xboole_0(k4_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_xboole_0), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1552, c_1056])).
% 3.42/1.55  tff(c_1626, plain, (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1596])).
% 3.42/1.55  tff(c_24, plain, (![A_22, B_23]: (~r1_xboole_0(k3_xboole_0(A_22, B_23), B_23) | r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.42/1.55  tff(c_1644, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1626, c_24])).
% 3.42/1.55  tff(c_1651, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1644, c_2])).
% 3.42/1.55  tff(c_1656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1651])).
% 3.42/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.55  
% 3.42/1.55  Inference rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Ref     : 0
% 3.42/1.55  #Sup     : 407
% 3.42/1.55  #Fact    : 0
% 3.42/1.55  #Define  : 0
% 3.42/1.55  #Split   : 1
% 3.42/1.55  #Chain   : 0
% 3.42/1.55  #Close   : 0
% 3.42/1.55  
% 3.42/1.55  Ordering : KBO
% 3.42/1.55  
% 3.42/1.55  Simplification rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Subsume      : 43
% 3.42/1.55  #Demod        : 387
% 3.42/1.55  #Tautology    : 219
% 3.42/1.55  #SimpNegUnit  : 18
% 3.42/1.55  #BackRed      : 0
% 3.42/1.55  
% 3.42/1.55  #Partial instantiations: 0
% 3.42/1.55  #Strategies tried      : 1
% 3.42/1.55  
% 3.42/1.55  Timing (in seconds)
% 3.42/1.55  ----------------------
% 3.42/1.55  Preprocessing        : 0.29
% 3.42/1.55  Parsing              : 0.15
% 3.42/1.55  CNF conversion       : 0.02
% 3.42/1.55  Main loop            : 0.48
% 3.42/1.55  Inferencing          : 0.16
% 3.42/1.55  Reduction            : 0.20
% 3.42/1.55  Demodulation         : 0.16
% 3.42/1.55  BG Simplification    : 0.02
% 3.42/1.55  Subsumption          : 0.07
% 3.42/1.55  Abstraction          : 0.02
% 3.42/1.55  MUC search           : 0.00
% 3.42/1.55  Cooper               : 0.00
% 3.42/1.55  Total                : 0.80
% 3.42/1.55  Index Insertion      : 0.00
% 3.42/1.55  Index Deletion       : 0.00
% 3.42/1.55  Index Matching       : 0.00
% 3.42/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
