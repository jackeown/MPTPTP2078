%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:12 EST 2020

% Result     : Theorem 5.80s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 164 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 ( 190 expanded)
%              Number of equality atoms :   41 (  97 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_114,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [A_24] : k3_xboole_0(A_24,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_114])).

tff(c_20,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_212,plain,(
    ! [A_53,B_54] : k2_xboole_0(k3_xboole_0(A_53,B_54),k4_xboole_0(A_53,B_54)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_239,plain,(
    ! [A_18] : k2_xboole_0(k3_xboole_0(A_18,k1_xboole_0),A_18) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_212])).

tff(c_244,plain,(
    ! [A_55] : k2_xboole_0(k1_xboole_0,A_55) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_239])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_260,plain,(
    ! [A_55] : k2_xboole_0(A_55,k1_xboole_0) = A_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_2])).

tff(c_28,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_121,plain,(
    ! [A_25,B_26] : k3_xboole_0(k4_xboole_0(A_25,B_26),B_26) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_114])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_236,plain,(
    ! [A_5] : k2_xboole_0(A_5,k4_xboole_0(A_5,A_5)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_212])).

tff(c_52,plain,(
    ! [A_30,B_31] : r1_tarski(k4_xboole_0(A_30,B_31),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_18] : r1_tarski(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_52])).

tff(c_177,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(k2_xboole_0(A_48,B_50),C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_192,plain,(
    ! [A_51,B_52] : r1_tarski(A_51,k2_xboole_0(A_51,B_52)) ),
    inference(resolution,[status(thm)],[c_55,c_177])).

tff(c_452,plain,(
    ! [B_64,A_65] : r1_tarski(B_64,k2_xboole_0(A_65,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_192])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_769,plain,(
    ! [B_79,A_80] : k3_xboole_0(B_79,k2_xboole_0(A_80,B_79)) = B_79 ),
    inference(resolution,[status(thm)],[c_452,c_14])).

tff(c_802,plain,(
    ! [A_5] : k3_xboole_0(k4_xboole_0(A_5,A_5),A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_769])).

tff(c_833,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_802])).

tff(c_334,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_352,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_334])).

tff(c_848,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_352])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1461,plain,(
    ! [A_110,B_111] : k3_xboole_0(k4_xboole_0(A_110,B_111),A_110) = k4_xboole_0(A_110,B_111) ),
    inference(resolution,[status(thm)],[c_16,c_96])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1473,plain,(
    ! [A_110,B_111] : k5_xboole_0(k4_xboole_0(A_110,B_111),k4_xboole_0(A_110,B_111)) = k4_xboole_0(k4_xboole_0(A_110,B_111),A_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_1461,c_10])).

tff(c_1520,plain,(
    ! [A_112,B_113] : k4_xboole_0(k4_xboole_0(A_112,B_113),A_112) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_1473])).

tff(c_18,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1546,plain,(
    ! [A_112,B_113] : k2_xboole_0(A_112,k4_xboole_0(A_112,B_113)) = k2_xboole_0(A_112,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1520,c_18])).

tff(c_1588,plain,(
    ! [A_112,B_113] : k2_xboole_0(A_112,k4_xboole_0(A_112,B_113)) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_1546])).

tff(c_243,plain,(
    ! [A_18] : k2_xboole_0(k1_xboole_0,A_18) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_239])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_109,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_96])).

tff(c_349,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_334])).

tff(c_644,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_349])).

tff(c_1754,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_644])).

tff(c_1786,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k1_xboole_0) = k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1754,c_18])).

tff(c_1807,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_2,c_2,c_1786])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(k2_xboole_0(A_9,B_10),C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_481,plain,(
    ! [A_9,A_65,B_10] : r1_tarski(A_9,k2_xboole_0(A_65,k2_xboole_0(A_9,B_10))) ),
    inference(resolution,[status(thm)],[c_452,c_12])).

tff(c_6774,plain,(
    ! [A_230] : r1_tarski('#skF_1',k2_xboole_0(A_230,k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1807,c_481])).

tff(c_6791,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1588,c_6774])).

tff(c_6823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_6791])).

tff(c_6824,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_7307,plain,(
    ! [A_262,C_263,B_264] :
      ( r1_xboole_0(A_262,C_263)
      | ~ r1_xboole_0(B_264,C_263)
      | ~ r1_tarski(A_262,B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8589,plain,(
    ! [A_303,B_304,A_305] :
      ( r1_xboole_0(A_303,B_304)
      | ~ r1_tarski(A_303,k4_xboole_0(A_305,B_304)) ) ),
    inference(resolution,[status(thm)],[c_28,c_7307])).

tff(c_8633,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_8589])).

tff(c_8647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6824,c_8633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.80/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.16  
% 5.80/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.16  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.80/2.16  
% 5.80/2.16  %Foreground sorts:
% 5.80/2.16  
% 5.80/2.16  
% 5.80/2.16  %Background operators:
% 5.80/2.16  
% 5.80/2.16  
% 5.80/2.16  %Foreground operators:
% 5.80/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.80/2.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.80/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.80/2.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.80/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.80/2.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.80/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.80/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.80/2.16  tff('#skF_1', type, '#skF_1': $i).
% 5.80/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.80/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.80/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.80/2.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.80/2.16  
% 5.80/2.18  tff(f_68, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.80/2.18  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.80/2.18  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.80/2.18  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.80/2.18  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.80/2.18  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.80/2.18  tff(f_61, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.80/2.18  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.80/2.18  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.80/2.18  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.80/2.18  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.80/2.18  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.80/2.18  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.80/2.18  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 5.80/2.18  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.80/2.18  tff(c_62, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 5.80/2.18  tff(c_26, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.80/2.18  tff(c_114, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.80/2.18  tff(c_122, plain, (![A_24]: (k3_xboole_0(A_24, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_114])).
% 5.80/2.18  tff(c_20, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.80/2.18  tff(c_212, plain, (![A_53, B_54]: (k2_xboole_0(k3_xboole_0(A_53, B_54), k4_xboole_0(A_53, B_54))=A_53)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.80/2.18  tff(c_239, plain, (![A_18]: (k2_xboole_0(k3_xboole_0(A_18, k1_xboole_0), A_18)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_20, c_212])).
% 5.80/2.18  tff(c_244, plain, (![A_55]: (k2_xboole_0(k1_xboole_0, A_55)=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_239])).
% 5.80/2.18  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.80/2.18  tff(c_260, plain, (![A_55]: (k2_xboole_0(A_55, k1_xboole_0)=A_55)), inference(superposition, [status(thm), theory('equality')], [c_244, c_2])).
% 5.80/2.18  tff(c_28, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.80/2.18  tff(c_121, plain, (![A_25, B_26]: (k3_xboole_0(k4_xboole_0(A_25, B_26), B_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_114])).
% 5.80/2.18  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.80/2.18  tff(c_236, plain, (![A_5]: (k2_xboole_0(A_5, k4_xboole_0(A_5, A_5))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_8, c_212])).
% 5.80/2.18  tff(c_52, plain, (![A_30, B_31]: (r1_tarski(k4_xboole_0(A_30, B_31), A_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.80/2.18  tff(c_55, plain, (![A_18]: (r1_tarski(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_52])).
% 5.80/2.18  tff(c_177, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(k2_xboole_0(A_48, B_50), C_49))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.80/2.18  tff(c_192, plain, (![A_51, B_52]: (r1_tarski(A_51, k2_xboole_0(A_51, B_52)))), inference(resolution, [status(thm)], [c_55, c_177])).
% 5.80/2.18  tff(c_452, plain, (![B_64, A_65]: (r1_tarski(B_64, k2_xboole_0(A_65, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_192])).
% 5.80/2.18  tff(c_14, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.80/2.18  tff(c_769, plain, (![B_79, A_80]: (k3_xboole_0(B_79, k2_xboole_0(A_80, B_79))=B_79)), inference(resolution, [status(thm)], [c_452, c_14])).
% 5.80/2.18  tff(c_802, plain, (![A_5]: (k3_xboole_0(k4_xboole_0(A_5, A_5), A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_236, c_769])).
% 5.80/2.18  tff(c_833, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_802])).
% 5.80/2.18  tff(c_334, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.80/2.18  tff(c_352, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_334])).
% 5.80/2.18  tff(c_848, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_833, c_352])).
% 5.80/2.18  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.80/2.18  tff(c_96, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.80/2.18  tff(c_1461, plain, (![A_110, B_111]: (k3_xboole_0(k4_xboole_0(A_110, B_111), A_110)=k4_xboole_0(A_110, B_111))), inference(resolution, [status(thm)], [c_16, c_96])).
% 5.80/2.18  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.80/2.18  tff(c_1473, plain, (![A_110, B_111]: (k5_xboole_0(k4_xboole_0(A_110, B_111), k4_xboole_0(A_110, B_111))=k4_xboole_0(k4_xboole_0(A_110, B_111), A_110))), inference(superposition, [status(thm), theory('equality')], [c_1461, c_10])).
% 5.80/2.18  tff(c_1520, plain, (![A_112, B_113]: (k4_xboole_0(k4_xboole_0(A_112, B_113), A_112)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_848, c_1473])).
% 5.80/2.18  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.80/2.18  tff(c_1546, plain, (![A_112, B_113]: (k2_xboole_0(A_112, k4_xboole_0(A_112, B_113))=k2_xboole_0(A_112, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1520, c_18])).
% 5.80/2.18  tff(c_1588, plain, (![A_112, B_113]: (k2_xboole_0(A_112, k4_xboole_0(A_112, B_113))=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_260, c_1546])).
% 5.80/2.18  tff(c_243, plain, (![A_18]: (k2_xboole_0(k1_xboole_0, A_18)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_239])).
% 5.80/2.18  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.80/2.18  tff(c_109, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_96])).
% 5.80/2.18  tff(c_349, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_109, c_334])).
% 5.80/2.18  tff(c_644, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_352, c_349])).
% 5.80/2.18  tff(c_1754, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_833, c_644])).
% 5.80/2.18  tff(c_1786, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k1_xboole_0)=k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1754, c_18])).
% 5.80/2.18  tff(c_1807, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_2, c_2, c_1786])).
% 5.80/2.18  tff(c_12, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(k2_xboole_0(A_9, B_10), C_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.80/2.18  tff(c_481, plain, (![A_9, A_65, B_10]: (r1_tarski(A_9, k2_xboole_0(A_65, k2_xboole_0(A_9, B_10))))), inference(resolution, [status(thm)], [c_452, c_12])).
% 5.80/2.18  tff(c_6774, plain, (![A_230]: (r1_tarski('#skF_1', k2_xboole_0(A_230, k4_xboole_0('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1807, c_481])).
% 5.80/2.18  tff(c_6791, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1588, c_6774])).
% 5.80/2.18  tff(c_6823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_6791])).
% 5.80/2.18  tff(c_6824, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 5.80/2.18  tff(c_7307, plain, (![A_262, C_263, B_264]: (r1_xboole_0(A_262, C_263) | ~r1_xboole_0(B_264, C_263) | ~r1_tarski(A_262, B_264))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.80/2.18  tff(c_8589, plain, (![A_303, B_304, A_305]: (r1_xboole_0(A_303, B_304) | ~r1_tarski(A_303, k4_xboole_0(A_305, B_304)))), inference(resolution, [status(thm)], [c_28, c_7307])).
% 5.80/2.18  tff(c_8633, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_8589])).
% 5.80/2.18  tff(c_8647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6824, c_8633])).
% 5.80/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.18  
% 5.80/2.18  Inference rules
% 5.80/2.18  ----------------------
% 5.80/2.18  #Ref     : 0
% 5.80/2.18  #Sup     : 2117
% 5.80/2.18  #Fact    : 0
% 5.80/2.18  #Define  : 0
% 5.80/2.18  #Split   : 2
% 5.80/2.18  #Chain   : 0
% 5.80/2.18  #Close   : 0
% 5.80/2.18  
% 5.80/2.18  Ordering : KBO
% 5.80/2.18  
% 5.80/2.18  Simplification rules
% 5.80/2.18  ----------------------
% 5.80/2.18  #Subsume      : 73
% 5.80/2.18  #Demod        : 1662
% 5.80/2.18  #Tautology    : 1666
% 5.80/2.18  #SimpNegUnit  : 2
% 5.80/2.18  #BackRed      : 13
% 5.80/2.18  
% 5.80/2.18  #Partial instantiations: 0
% 5.80/2.18  #Strategies tried      : 1
% 5.80/2.18  
% 5.80/2.18  Timing (in seconds)
% 5.80/2.18  ----------------------
% 5.80/2.18  Preprocessing        : 0.29
% 5.80/2.18  Parsing              : 0.16
% 5.80/2.18  CNF conversion       : 0.02
% 5.80/2.18  Main loop            : 1.11
% 5.80/2.18  Inferencing          : 0.35
% 5.80/2.18  Reduction            : 0.49
% 5.80/2.18  Demodulation         : 0.39
% 5.80/2.18  BG Simplification    : 0.03
% 5.80/2.18  Subsumption          : 0.17
% 5.80/2.18  Abstraction          : 0.05
% 5.80/2.18  MUC search           : 0.00
% 5.80/2.18  Cooper               : 0.00
% 5.80/2.18  Total                : 1.44
% 5.80/2.18  Index Insertion      : 0.00
% 5.80/2.18  Index Deletion       : 0.00
% 5.80/2.18  Index Matching       : 0.00
% 5.80/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
