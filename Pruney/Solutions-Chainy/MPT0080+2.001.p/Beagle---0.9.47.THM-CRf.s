%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:49 EST 2020

% Result     : Theorem 40.20s
% Output     : CNFRefutation 40.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 196 expanded)
%              Number of leaves         :   30 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 241 expanded)
%              Number of equality atoms :   42 ( 139 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_89,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_79,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_58,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [A_34] : r1_xboole_0(A_34,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_168,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = k1_xboole_0
      | ~ r1_xboole_0(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_187,plain,(
    ! [A_34] : k3_xboole_0(A_34,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_168])).

tff(c_359,plain,(
    ! [A_71,B_72] : k2_xboole_0(k3_xboole_0(A_71,B_72),k4_xboole_0(A_71,B_72)) = A_71 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_480,plain,(
    ! [A_83] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_83,k1_xboole_0)) = A_83 ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_359])).

tff(c_46,plain,(
    ! [A_25,B_26] : k2_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_524,plain,(
    ! [A_87] : k2_xboole_0(k1_xboole_0,A_87) = A_87 ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_46])).

tff(c_60,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_188,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_168])).

tff(c_389,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_7')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_359])).

tff(c_533,plain,(
    k4_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_389])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_576,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_524])).

tff(c_871,plain,(
    ! [A_94,B_95,C_96] : k4_xboole_0(k4_xboole_0(A_94,B_95),C_96) = k4_xboole_0(A_94,k2_xboole_0(B_95,C_96)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1549,plain,(
    ! [C_124] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_7',C_124)) = k4_xboole_0('#skF_5',C_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_871])).

tff(c_1613,plain,(
    ! [A_1] : k4_xboole_0('#skF_5',k2_xboole_0(A_1,'#skF_7')) = k4_xboole_0('#skF_5',A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1549])).

tff(c_66,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [A_35,B_36] : r1_tarski(A_35,k2_xboole_0(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_81,plain,(
    ! [A_42,B_41] : r1_tarski(A_42,k2_xboole_0(B_41,A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_56])).

tff(c_371,plain,(
    ! [A_71,B_72] : r1_tarski(k4_xboole_0(A_71,B_72),A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_81])).

tff(c_62,plain,(
    r1_tarski('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_4'(A_23),A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_718,plain,(
    ! [C_90,B_91,A_92] :
      ( r2_hidden(C_90,B_91)
      | ~ r2_hidden(C_90,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4784,plain,(
    ! [A_188,B_189] :
      ( r2_hidden('#skF_4'(A_188),B_189)
      | ~ r1_tarski(A_188,B_189)
      | k1_xboole_0 = A_188 ) ),
    inference(resolution,[status(thm)],[c_44,c_718])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_158245,plain,(
    ! [A_1172,B_1173,B_1174] :
      ( r2_hidden('#skF_4'(A_1172),B_1173)
      | ~ r1_tarski(B_1174,B_1173)
      | ~ r1_tarski(A_1172,B_1174)
      | k1_xboole_0 = A_1172 ) ),
    inference(resolution,[status(thm)],[c_4784,c_6])).

tff(c_159513,plain,(
    ! [A_1178] :
      ( r2_hidden('#skF_4'(A_1178),k2_xboole_0('#skF_6','#skF_7'))
      | ~ r1_tarski(A_1178,'#skF_5')
      | k1_xboole_0 = A_1178 ) ),
    inference(resolution,[status(thm)],[c_62,c_158245])).

tff(c_510,plain,(
    ! [D_84,B_85,A_86] :
      ( ~ r2_hidden(D_84,B_85)
      | ~ r2_hidden(D_84,k4_xboole_0(A_86,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_523,plain,(
    ! [A_86,B_85] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_86,B_85)),B_85)
      | k4_xboole_0(A_86,B_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_510])).

tff(c_162170,plain,(
    ! [A_1187] :
      ( ~ r1_tarski(k4_xboole_0(A_1187,k2_xboole_0('#skF_6','#skF_7')),'#skF_5')
      | k4_xboole_0(A_1187,k2_xboole_0('#skF_6','#skF_7')) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_159513,c_523])).

tff(c_162242,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_5','#skF_6'),'#skF_5')
    | k4_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1613,c_162170])).

tff(c_162310,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_371,c_162242])).

tff(c_932,plain,(
    ! [C_96] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_7',C_96)) = k4_xboole_0('#skF_5',C_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_871])).

tff(c_48,plain,(
    ! [A_27,B_28,C_29] : k4_xboole_0(k4_xboole_0(A_27,B_28),C_29) = k4_xboole_0(A_27,k2_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_946,plain,(
    ! [A_94,B_95,B_31] : k4_xboole_0(A_94,k2_xboole_0(B_95,k4_xboole_0(k4_xboole_0(A_94,B_95),B_31))) = k3_xboole_0(k4_xboole_0(A_94,B_95),B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_871])).

tff(c_17853,plain,(
    ! [A_392,B_393,B_394] : k4_xboole_0(A_392,k2_xboole_0(B_393,k4_xboole_0(A_392,k2_xboole_0(B_393,B_394)))) = k3_xboole_0(k4_xboole_0(A_392,B_393),B_394) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_946])).

tff(c_18139,plain,(
    ! [C_96] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_7',k4_xboole_0('#skF_5',C_96))) = k3_xboole_0(k4_xboole_0('#skF_5','#skF_7'),C_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_932,c_17853])).

tff(c_18244,plain,(
    ! [C_96] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_7',k4_xboole_0('#skF_5',C_96))) = k3_xboole_0('#skF_5',C_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_18139])).

tff(c_162359,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_7',k1_xboole_0)) = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_162310,c_18244])).

tff(c_162703,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_533,c_576,c_162359])).

tff(c_374,plain,(
    ! [A_71,B_72] : r1_tarski(k3_xboole_0(A_71,B_72),A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_56])).

tff(c_163022,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_162703,c_374])).

tff(c_163074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_163022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:15:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.20/29.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.20/29.49  
% 40.20/29.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.20/29.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1
% 40.20/29.49  
% 40.20/29.49  %Foreground sorts:
% 40.20/29.49  
% 40.20/29.49  
% 40.20/29.49  %Background operators:
% 40.20/29.49  
% 40.20/29.49  
% 40.20/29.49  %Foreground operators:
% 40.20/29.49  tff('#skF_4', type, '#skF_4': $i > $i).
% 40.20/29.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.20/29.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 40.20/29.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 40.20/29.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 40.20/29.49  tff('#skF_7', type, '#skF_7': $i).
% 40.20/29.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 40.20/29.49  tff('#skF_5', type, '#skF_5': $i).
% 40.20/29.49  tff('#skF_6', type, '#skF_6': $i).
% 40.20/29.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 40.20/29.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 40.20/29.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.20/29.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 40.20/29.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.20/29.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 40.20/29.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 40.20/29.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 40.20/29.49  
% 40.20/29.51  tff(f_98, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 40.20/29.51  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 40.20/29.51  tff(f_89, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 40.20/29.51  tff(f_50, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 40.20/29.51  tff(f_87, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 40.20/29.51  tff(f_81, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 40.20/29.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 40.20/29.51  tff(f_83, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 40.20/29.51  tff(f_91, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 40.20/29.51  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 40.20/29.51  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 40.20/29.51  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 40.20/29.51  tff(f_85, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 40.20/29.51  tff(c_58, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 40.20/29.51  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 40.20/29.51  tff(c_54, plain, (![A_34]: (r1_xboole_0(A_34, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_89])).
% 40.20/29.51  tff(c_168, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=k1_xboole_0 | ~r1_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_50])).
% 40.20/29.51  tff(c_187, plain, (![A_34]: (k3_xboole_0(A_34, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_168])).
% 40.20/29.51  tff(c_359, plain, (![A_71, B_72]: (k2_xboole_0(k3_xboole_0(A_71, B_72), k4_xboole_0(A_71, B_72))=A_71)), inference(cnfTransformation, [status(thm)], [f_87])).
% 40.20/29.51  tff(c_480, plain, (![A_83]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_83, k1_xboole_0))=A_83)), inference(superposition, [status(thm), theory('equality')], [c_187, c_359])).
% 40.20/29.51  tff(c_46, plain, (![A_25, B_26]: (k2_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 40.20/29.51  tff(c_524, plain, (![A_87]: (k2_xboole_0(k1_xboole_0, A_87)=A_87)), inference(superposition, [status(thm), theory('equality')], [c_480, c_46])).
% 40.20/29.51  tff(c_60, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 40.20/29.51  tff(c_188, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_168])).
% 40.20/29.51  tff(c_389, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_7'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_188, c_359])).
% 40.20/29.51  tff(c_533, plain, (k4_xboole_0('#skF_5', '#skF_7')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_524, c_389])).
% 40.20/29.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 40.20/29.51  tff(c_576, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_524])).
% 40.20/29.51  tff(c_871, plain, (![A_94, B_95, C_96]: (k4_xboole_0(k4_xboole_0(A_94, B_95), C_96)=k4_xboole_0(A_94, k2_xboole_0(B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 40.20/29.51  tff(c_1549, plain, (![C_124]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_7', C_124))=k4_xboole_0('#skF_5', C_124))), inference(superposition, [status(thm), theory('equality')], [c_533, c_871])).
% 40.20/29.51  tff(c_1613, plain, (![A_1]: (k4_xboole_0('#skF_5', k2_xboole_0(A_1, '#skF_7'))=k4_xboole_0('#skF_5', A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1549])).
% 40.20/29.51  tff(c_66, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 40.20/29.51  tff(c_56, plain, (![A_35, B_36]: (r1_tarski(A_35, k2_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 40.20/29.51  tff(c_81, plain, (![A_42, B_41]: (r1_tarski(A_42, k2_xboole_0(B_41, A_42)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_56])).
% 40.20/29.51  tff(c_371, plain, (![A_71, B_72]: (r1_tarski(k4_xboole_0(A_71, B_72), A_71))), inference(superposition, [status(thm), theory('equality')], [c_359, c_81])).
% 40.20/29.51  tff(c_62, plain, (r1_tarski('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 40.20/29.51  tff(c_44, plain, (![A_23]: (r2_hidden('#skF_4'(A_23), A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_79])).
% 40.20/29.51  tff(c_718, plain, (![C_90, B_91, A_92]: (r2_hidden(C_90, B_91) | ~r2_hidden(C_90, A_92) | ~r1_tarski(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_36])).
% 40.20/29.51  tff(c_4784, plain, (![A_188, B_189]: (r2_hidden('#skF_4'(A_188), B_189) | ~r1_tarski(A_188, B_189) | k1_xboole_0=A_188)), inference(resolution, [status(thm)], [c_44, c_718])).
% 40.20/29.51  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 40.20/29.51  tff(c_158245, plain, (![A_1172, B_1173, B_1174]: (r2_hidden('#skF_4'(A_1172), B_1173) | ~r1_tarski(B_1174, B_1173) | ~r1_tarski(A_1172, B_1174) | k1_xboole_0=A_1172)), inference(resolution, [status(thm)], [c_4784, c_6])).
% 40.20/29.51  tff(c_159513, plain, (![A_1178]: (r2_hidden('#skF_4'(A_1178), k2_xboole_0('#skF_6', '#skF_7')) | ~r1_tarski(A_1178, '#skF_5') | k1_xboole_0=A_1178)), inference(resolution, [status(thm)], [c_62, c_158245])).
% 40.20/29.51  tff(c_510, plain, (![D_84, B_85, A_86]: (~r2_hidden(D_84, B_85) | ~r2_hidden(D_84, k4_xboole_0(A_86, B_85)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 40.20/29.51  tff(c_523, plain, (![A_86, B_85]: (~r2_hidden('#skF_4'(k4_xboole_0(A_86, B_85)), B_85) | k4_xboole_0(A_86, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_510])).
% 40.20/29.51  tff(c_162170, plain, (![A_1187]: (~r1_tarski(k4_xboole_0(A_1187, k2_xboole_0('#skF_6', '#skF_7')), '#skF_5') | k4_xboole_0(A_1187, k2_xboole_0('#skF_6', '#skF_7'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_159513, c_523])).
% 40.20/29.51  tff(c_162242, plain, (~r1_tarski(k4_xboole_0('#skF_5', '#skF_6'), '#skF_5') | k4_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1613, c_162170])).
% 40.20/29.51  tff(c_162310, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1613, c_371, c_162242])).
% 40.20/29.51  tff(c_932, plain, (![C_96]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_7', C_96))=k4_xboole_0('#skF_5', C_96))), inference(superposition, [status(thm), theory('equality')], [c_533, c_871])).
% 40.20/29.51  tff(c_48, plain, (![A_27, B_28, C_29]: (k4_xboole_0(k4_xboole_0(A_27, B_28), C_29)=k4_xboole_0(A_27, k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 40.20/29.51  tff(c_50, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 40.20/29.51  tff(c_946, plain, (![A_94, B_95, B_31]: (k4_xboole_0(A_94, k2_xboole_0(B_95, k4_xboole_0(k4_xboole_0(A_94, B_95), B_31)))=k3_xboole_0(k4_xboole_0(A_94, B_95), B_31))), inference(superposition, [status(thm), theory('equality')], [c_50, c_871])).
% 40.20/29.51  tff(c_17853, plain, (![A_392, B_393, B_394]: (k4_xboole_0(A_392, k2_xboole_0(B_393, k4_xboole_0(A_392, k2_xboole_0(B_393, B_394))))=k3_xboole_0(k4_xboole_0(A_392, B_393), B_394))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_946])).
% 40.20/29.51  tff(c_18139, plain, (![C_96]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_7', k4_xboole_0('#skF_5', C_96)))=k3_xboole_0(k4_xboole_0('#skF_5', '#skF_7'), C_96))), inference(superposition, [status(thm), theory('equality')], [c_932, c_17853])).
% 40.20/29.51  tff(c_18244, plain, (![C_96]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_7', k4_xboole_0('#skF_5', C_96)))=k3_xboole_0('#skF_5', C_96))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_18139])).
% 40.20/29.51  tff(c_162359, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_7', k1_xboole_0))=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_162310, c_18244])).
% 40.20/29.51  tff(c_162703, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_533, c_576, c_162359])).
% 40.20/29.51  tff(c_374, plain, (![A_71, B_72]: (r1_tarski(k3_xboole_0(A_71, B_72), A_71))), inference(superposition, [status(thm), theory('equality')], [c_359, c_56])).
% 40.20/29.51  tff(c_163022, plain, (r1_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_162703, c_374])).
% 40.20/29.51  tff(c_163074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_163022])).
% 40.20/29.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.20/29.51  
% 40.20/29.51  Inference rules
% 40.20/29.51  ----------------------
% 40.20/29.51  #Ref     : 0
% 40.20/29.51  #Sup     : 41056
% 40.20/29.51  #Fact    : 10
% 40.20/29.51  #Define  : 0
% 40.20/29.51  #Split   : 12
% 40.20/29.51  #Chain   : 0
% 40.20/29.51  #Close   : 0
% 40.20/29.51  
% 40.20/29.51  Ordering : KBO
% 40.20/29.51  
% 40.20/29.51  Simplification rules
% 40.20/29.51  ----------------------
% 40.20/29.51  #Subsume      : 6694
% 40.20/29.51  #Demod        : 51571
% 40.20/29.51  #Tautology    : 23391
% 40.20/29.51  #SimpNegUnit  : 142
% 40.20/29.51  #BackRed      : 368
% 40.20/29.51  
% 40.20/29.51  #Partial instantiations: 0
% 40.20/29.51  #Strategies tried      : 1
% 40.20/29.51  
% 40.20/29.51  Timing (in seconds)
% 40.20/29.51  ----------------------
% 40.20/29.51  Preprocessing        : 0.30
% 40.20/29.51  Parsing              : 0.16
% 40.20/29.51  CNF conversion       : 0.02
% 40.20/29.51  Main loop            : 28.45
% 40.20/29.51  Inferencing          : 2.41
% 40.20/29.51  Reduction            : 18.62
% 40.33/29.51  Demodulation         : 17.02
% 40.33/29.51  BG Simplification    : 0.28
% 40.33/29.51  Subsumption          : 6.12
% 40.33/29.51  Abstraction          : 0.49
% 40.33/29.51  MUC search           : 0.00
% 40.33/29.51  Cooper               : 0.00
% 40.33/29.51  Total                : 28.79
% 40.33/29.51  Index Insertion      : 0.00
% 40.33/29.51  Index Deletion       : 0.00
% 40.33/29.51  Index Matching       : 0.00
% 40.33/29.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
