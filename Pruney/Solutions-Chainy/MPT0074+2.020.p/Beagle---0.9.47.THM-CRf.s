%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:29 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 135 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :   90 ( 250 expanded)
%              Number of equality atoms :   34 (  63 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_74,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_72,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

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

tff(f_76,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    ! [A_25,B_26] : r1_tarski(k4_xboole_0(A_25,B_26),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_45,plain,(
    ! [A_21] : r1_tarski(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_42])).

tff(c_1068,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_tarski('#skF_3'(A_78,B_79,C_80),B_79)
      | k3_xboole_0(B_79,C_80) = A_78
      | ~ r1_tarski(A_78,C_80)
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17] :
      ( ~ r1_tarski('#skF_3'(A_15,B_16,C_17),A_15)
      | k3_xboole_0(B_16,C_17) = A_15
      | ~ r1_tarski(A_15,C_17)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1072,plain,(
    ! [B_79,C_80] :
      ( k3_xboole_0(B_79,C_80) = B_79
      | ~ r1_tarski(B_79,C_80)
      | ~ r1_tarski(B_79,B_79) ) ),
    inference(resolution,[status(thm)],[c_1068,c_14])).

tff(c_1253,plain,(
    ! [B_83,C_84] :
      ( k3_xboole_0(B_83,C_84) = B_83
      | ~ r1_tarski(B_83,C_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_1072])).

tff(c_1272,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_1253])).

tff(c_32,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1273,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_1253])).

tff(c_28,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_47,plain,(
    ! [B_28,A_29] :
      ( r1_xboole_0(B_28,A_29)
      | ~ r1_xboole_0(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_47])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_115,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    ! [A_42,B_43] :
      ( ~ r1_xboole_0(A_42,B_43)
      | k3_xboole_0(A_42,B_43) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_115])).

tff(c_131,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_124])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_136,plain,(
    ! [C_7] :
      ( ~ r1_xboole_0('#skF_6','#skF_5')
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_6])).

tff(c_149,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_136])).

tff(c_57,plain,(
    ! [A_33,B_34] : k2_xboole_0(k3_xboole_0(A_33,B_34),k4_xboole_0(A_33,B_34)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k1_xboole_0 = A_10
      | k2_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_72,plain,(
    ! [B_34] : k3_xboole_0(k1_xboole_0,B_34) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_10])).

tff(c_132,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_124])).

tff(c_386,plain,(
    ! [A_56,B_57,C_58] : k3_xboole_0(k3_xboole_0(A_56,B_57),C_58) = k3_xboole_0(A_56,k3_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_423,plain,(
    ! [C_58] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_6',C_58)) = k3_xboole_0(k1_xboole_0,C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_386])).

tff(c_444,plain,(
    ! [C_59] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_6',C_59)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_423])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_455,plain,(
    ! [C_59] :
      ( r2_hidden('#skF_1'('#skF_5',k3_xboole_0('#skF_6',C_59)),k1_xboole_0)
      | r1_xboole_0('#skF_5',k3_xboole_0('#skF_6',C_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_4])).

tff(c_546,plain,(
    ! [C_61] : r1_xboole_0('#skF_5',k3_xboole_0('#skF_6',C_61)) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_455])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_594,plain,(
    ! [C_63] : r1_xboole_0(k3_xboole_0('#skF_6',C_63),'#skF_5') ),
    inference(resolution,[status(thm)],[c_546,c_2])).

tff(c_123,plain,(
    ! [A_39,B_40] :
      ( ~ r1_xboole_0(A_39,B_40)
      | k3_xboole_0(A_39,B_40) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_115])).

tff(c_683,plain,(
    ! [C_70] : k3_xboole_0(k3_xboole_0('#skF_6',C_70),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_594,c_123])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14] : k3_xboole_0(k3_xboole_0(A_12,B_13),C_14) = k3_xboole_0(A_12,k3_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_805,plain,(
    ! [C_72] : k3_xboole_0('#skF_6',k3_xboole_0(C_72,'#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_12])).

tff(c_827,plain,(
    ! [C_72] :
      ( r2_hidden('#skF_1'('#skF_6',k3_xboole_0(C_72,'#skF_5')),k1_xboole_0)
      | r1_xboole_0('#skF_6',k3_xboole_0(C_72,'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_4])).

tff(c_882,plain,(
    ! [C_73] : r1_xboole_0('#skF_6',k3_xboole_0(C_73,'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_827])).

tff(c_910,plain,(
    ! [C_74] : r1_xboole_0(k3_xboole_0(C_74,'#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_882,c_2])).

tff(c_931,plain,(
    ! [C_74] : k3_xboole_0(k3_xboole_0(C_74,'#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_910,c_123])).

tff(c_1466,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1273,c_931])).

tff(c_1499,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1272,c_1466])).

tff(c_1501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:07:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.45  
% 2.87/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.87/1.45  
% 2.87/1.45  %Foreground sorts:
% 2.87/1.45  
% 2.87/1.45  
% 2.87/1.45  %Background operators:
% 2.87/1.45  
% 2.87/1.45  
% 2.87/1.45  %Foreground operators:
% 2.87/1.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.87/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.45  
% 2.87/1.46  tff(f_85, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.87/1.46  tff(f_74, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.87/1.46  tff(f_72, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.87/1.46  tff(f_70, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_xboole_1)).
% 2.87/1.46  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.87/1.46  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.87/1.46  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.87/1.47  tff(f_76, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.87/1.47  tff(f_55, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.87/1.47  tff(f_57, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.87/1.47  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.87/1.47  tff(c_30, plain, (r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.87/1.47  tff(c_22, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.47  tff(c_42, plain, (![A_25, B_26]: (r1_tarski(k4_xboole_0(A_25, B_26), A_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.87/1.47  tff(c_45, plain, (![A_21]: (r1_tarski(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_22, c_42])).
% 2.87/1.47  tff(c_1068, plain, (![A_78, B_79, C_80]: (r1_tarski('#skF_3'(A_78, B_79, C_80), B_79) | k3_xboole_0(B_79, C_80)=A_78 | ~r1_tarski(A_78, C_80) | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.87/1.47  tff(c_14, plain, (![A_15, B_16, C_17]: (~r1_tarski('#skF_3'(A_15, B_16, C_17), A_15) | k3_xboole_0(B_16, C_17)=A_15 | ~r1_tarski(A_15, C_17) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.87/1.47  tff(c_1072, plain, (![B_79, C_80]: (k3_xboole_0(B_79, C_80)=B_79 | ~r1_tarski(B_79, C_80) | ~r1_tarski(B_79, B_79))), inference(resolution, [status(thm)], [c_1068, c_14])).
% 2.87/1.47  tff(c_1253, plain, (![B_83, C_84]: (k3_xboole_0(B_83, C_84)=B_83 | ~r1_tarski(B_83, C_84))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_1072])).
% 2.87/1.47  tff(c_1272, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_30, c_1253])).
% 2.87/1.47  tff(c_32, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.87/1.47  tff(c_1273, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_32, c_1253])).
% 2.87/1.47  tff(c_28, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.87/1.47  tff(c_47, plain, (![B_28, A_29]: (r1_xboole_0(B_28, A_29) | ~r1_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.87/1.47  tff(c_50, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_47])).
% 2.87/1.47  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.87/1.47  tff(c_115, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.47  tff(c_124, plain, (![A_42, B_43]: (~r1_xboole_0(A_42, B_43) | k3_xboole_0(A_42, B_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_115])).
% 2.87/1.47  tff(c_131, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_124])).
% 2.87/1.47  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.47  tff(c_136, plain, (![C_7]: (~r1_xboole_0('#skF_6', '#skF_5') | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_131, c_6])).
% 2.87/1.47  tff(c_149, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_136])).
% 2.87/1.47  tff(c_57, plain, (![A_33, B_34]: (k2_xboole_0(k3_xboole_0(A_33, B_34), k4_xboole_0(A_33, B_34))=A_33)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.87/1.47  tff(c_10, plain, (![A_10, B_11]: (k1_xboole_0=A_10 | k2_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.87/1.47  tff(c_72, plain, (![B_34]: (k3_xboole_0(k1_xboole_0, B_34)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_57, c_10])).
% 2.87/1.47  tff(c_132, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_124])).
% 2.87/1.47  tff(c_386, plain, (![A_56, B_57, C_58]: (k3_xboole_0(k3_xboole_0(A_56, B_57), C_58)=k3_xboole_0(A_56, k3_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.87/1.47  tff(c_423, plain, (![C_58]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_6', C_58))=k3_xboole_0(k1_xboole_0, C_58))), inference(superposition, [status(thm), theory('equality')], [c_132, c_386])).
% 2.87/1.47  tff(c_444, plain, (![C_59]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_6', C_59))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_423])).
% 2.87/1.47  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.47  tff(c_455, plain, (![C_59]: (r2_hidden('#skF_1'('#skF_5', k3_xboole_0('#skF_6', C_59)), k1_xboole_0) | r1_xboole_0('#skF_5', k3_xboole_0('#skF_6', C_59)))), inference(superposition, [status(thm), theory('equality')], [c_444, c_4])).
% 2.87/1.47  tff(c_546, plain, (![C_61]: (r1_xboole_0('#skF_5', k3_xboole_0('#skF_6', C_61)))), inference(negUnitSimplification, [status(thm)], [c_149, c_455])).
% 2.87/1.47  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.87/1.47  tff(c_594, plain, (![C_63]: (r1_xboole_0(k3_xboole_0('#skF_6', C_63), '#skF_5'))), inference(resolution, [status(thm)], [c_546, c_2])).
% 2.87/1.47  tff(c_123, plain, (![A_39, B_40]: (~r1_xboole_0(A_39, B_40) | k3_xboole_0(A_39, B_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_115])).
% 2.87/1.47  tff(c_683, plain, (![C_70]: (k3_xboole_0(k3_xboole_0('#skF_6', C_70), '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_594, c_123])).
% 2.87/1.47  tff(c_12, plain, (![A_12, B_13, C_14]: (k3_xboole_0(k3_xboole_0(A_12, B_13), C_14)=k3_xboole_0(A_12, k3_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.87/1.47  tff(c_805, plain, (![C_72]: (k3_xboole_0('#skF_6', k3_xboole_0(C_72, '#skF_5'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_683, c_12])).
% 2.87/1.47  tff(c_827, plain, (![C_72]: (r2_hidden('#skF_1'('#skF_6', k3_xboole_0(C_72, '#skF_5')), k1_xboole_0) | r1_xboole_0('#skF_6', k3_xboole_0(C_72, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_805, c_4])).
% 2.87/1.47  tff(c_882, plain, (![C_73]: (r1_xboole_0('#skF_6', k3_xboole_0(C_73, '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_149, c_827])).
% 2.87/1.47  tff(c_910, plain, (![C_74]: (r1_xboole_0(k3_xboole_0(C_74, '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_882, c_2])).
% 2.87/1.47  tff(c_931, plain, (![C_74]: (k3_xboole_0(k3_xboole_0(C_74, '#skF_5'), '#skF_6')=k1_xboole_0)), inference(resolution, [status(thm)], [c_910, c_123])).
% 2.87/1.47  tff(c_1466, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1273, c_931])).
% 2.87/1.47  tff(c_1499, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1272, c_1466])).
% 2.87/1.47  tff(c_1501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1499])).
% 2.87/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.47  
% 2.87/1.47  Inference rules
% 2.87/1.47  ----------------------
% 2.87/1.47  #Ref     : 0
% 2.87/1.47  #Sup     : 383
% 2.87/1.47  #Fact    : 0
% 2.87/1.47  #Define  : 0
% 2.87/1.47  #Split   : 1
% 2.87/1.47  #Chain   : 0
% 2.87/1.47  #Close   : 0
% 2.87/1.47  
% 2.87/1.47  Ordering : KBO
% 2.87/1.47  
% 2.87/1.47  Simplification rules
% 2.87/1.47  ----------------------
% 2.87/1.47  #Subsume      : 39
% 2.87/1.47  #Demod        : 176
% 2.87/1.47  #Tautology    : 240
% 2.87/1.47  #SimpNegUnit  : 17
% 2.87/1.47  #BackRed      : 5
% 2.87/1.47  
% 2.87/1.47  #Partial instantiations: 0
% 2.87/1.47  #Strategies tried      : 1
% 2.87/1.47  
% 2.87/1.47  Timing (in seconds)
% 2.87/1.47  ----------------------
% 2.87/1.47  Preprocessing        : 0.30
% 2.87/1.47  Parsing              : 0.16
% 2.87/1.47  CNF conversion       : 0.02
% 2.87/1.47  Main loop            : 0.40
% 2.87/1.47  Inferencing          : 0.15
% 2.87/1.47  Reduction            : 0.14
% 2.87/1.47  Demodulation         : 0.10
% 2.87/1.47  BG Simplification    : 0.02
% 2.87/1.47  Subsumption          : 0.06
% 2.87/1.47  Abstraction          : 0.02
% 2.87/1.47  MUC search           : 0.00
% 2.87/1.47  Cooper               : 0.00
% 2.87/1.47  Total                : 0.73
% 2.87/1.47  Index Insertion      : 0.00
% 2.87/1.47  Index Deletion       : 0.00
% 2.87/1.47  Index Matching       : 0.00
% 2.87/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
