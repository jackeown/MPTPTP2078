%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:39 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   60 (  86 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 118 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_55,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(B,C)),k3_xboole_0(C,A)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(B,C)),k2_xboole_0(C,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_20,plain,(
    ! [A_21] : r1_tarski(k1_xboole_0,A_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_150,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_168,plain,(
    ! [A_21] : k2_xboole_0(k1_xboole_0,A_21) = A_21 ),
    inference(resolution,[status(thm)],[c_20,c_150])).

tff(c_18,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    ! [A_30,B_31] : r1_tarski(k3_xboole_0(A_30,B_31),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    ! [B_31] : k3_xboole_0(k1_xboole_0,B_31) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_22])).

tff(c_14,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k3_xboole_0(k3_xboole_0(A_3,B_4),C_5) = k3_xboole_0(A_3,k3_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19] : k3_xboole_0(k3_xboole_0(k2_xboole_0(A_17,B_18),k2_xboole_0(B_18,C_19)),k2_xboole_0(C_19,A_17)) = k2_xboole_0(k2_xboole_0(k3_xboole_0(A_17,B_18),k3_xboole_0(B_18,C_19)),k3_xboole_0(C_19,A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1464,plain,(
    ! [A_88,B_89,C_90] : k3_xboole_0(k3_xboole_0(k2_xboole_0(A_88,B_89),k2_xboole_0(B_89,C_90)),k2_xboole_0(C_90,A_88)) = k2_xboole_0(k3_xboole_0(A_88,B_89),k2_xboole_0(k3_xboole_0(B_89,C_90),k3_xboole_0(C_90,A_88))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16])).

tff(c_1614,plain,(
    ! [A_11,C_90] : k2_xboole_0(k3_xboole_0(A_11,k1_xboole_0),k2_xboole_0(k3_xboole_0(k1_xboole_0,C_90),k3_xboole_0(C_90,A_11))) = k3_xboole_0(k3_xboole_0(A_11,k2_xboole_0(k1_xboole_0,C_90)),k2_xboole_0(C_90,A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1464])).

tff(c_1663,plain,(
    ! [C_91,A_92] : k3_xboole_0(C_91,A_92) = k3_xboole_0(A_92,C_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_18,c_168,c_64,c_14,c_168,c_4,c_1614])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1927,plain,(
    ! [A_93,C_94] : r1_tarski(k3_xboole_0(A_93,C_94),C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_1663,c_6])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_201,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_215,plain,(
    ! [A_40] :
      ( r1_tarski(A_40,'#skF_4')
      | ~ r1_tarski(A_40,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_201])).

tff(c_2012,plain,(
    ! [A_93] : r1_tarski(k3_xboole_0(A_93,'#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1927,c_215])).

tff(c_85,plain,(
    ! [A_33,B_34] : k3_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,(
    ! [A_33] : r1_tarski(A_33,A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_6])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_378,plain,(
    ! [A_50] :
      ( r1_tarski(A_50,'#skF_2')
      | ~ r1_tarski(A_50,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_201])).

tff(c_12,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,C_14)
      | ~ r1_tarski(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1071,plain,(
    ! [A_76,A_77] :
      ( r1_tarski(A_76,'#skF_2')
      | ~ r1_tarski(A_76,A_77)
      | ~ r1_tarski(A_77,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_378,c_12])).

tff(c_1089,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k3_xboole_0(A_6,B_7),'#skF_2')
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_1071])).

tff(c_1148,plain,(
    ! [A_80,B_81,C_82] :
      ( r1_tarski(A_80,k3_xboole_0(B_81,C_82))
      | ~ r1_tarski(A_80,C_82)
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1199,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_4')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1148,c_26])).

tff(c_1374,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1199])).

tff(c_1377,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1089,c_1374])).

tff(c_1384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1377])).

tff(c_1385,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1199])).

tff(c_2030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_1385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:42:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.56  
% 3.58/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.56  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.58/1.56  
% 3.58/1.56  %Foreground sorts:
% 3.58/1.56  
% 3.58/1.56  
% 3.58/1.56  %Background operators:
% 3.58/1.56  
% 3.58/1.56  
% 3.58/1.56  %Foreground operators:
% 3.58/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.58/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.58/1.56  
% 3.58/1.57  tff(f_55, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.58/1.57  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.58/1.57  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.58/1.57  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.58/1.57  tff(f_59, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.58/1.57  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.58/1.57  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.58/1.57  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.58/1.57  tff(f_61, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.58/1.57  tff(f_51, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(B, C)), k3_xboole_0(C, A)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(B, C)), k2_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_xboole_1)).
% 3.58/1.57  tff(f_68, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 3.58/1.57  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.58/1.57  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.58/1.57  tff(c_20, plain, (![A_21]: (r1_tarski(k1_xboole_0, A_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.58/1.57  tff(c_150, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.58/1.57  tff(c_168, plain, (![A_21]: (k2_xboole_0(k1_xboole_0, A_21)=A_21)), inference(resolution, [status(thm)], [c_20, c_150])).
% 3.58/1.57  tff(c_18, plain, (![A_20]: (k3_xboole_0(A_20, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.58/1.57  tff(c_56, plain, (![A_30, B_31]: (r1_tarski(k3_xboole_0(A_30, B_31), A_30))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.58/1.57  tff(c_22, plain, (![A_22]: (k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.58/1.57  tff(c_64, plain, (![B_31]: (k3_xboole_0(k1_xboole_0, B_31)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_22])).
% 3.58/1.57  tff(c_14, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.58/1.57  tff(c_4, plain, (![A_3, B_4, C_5]: (k3_xboole_0(k3_xboole_0(A_3, B_4), C_5)=k3_xboole_0(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.57  tff(c_10, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.58/1.57  tff(c_24, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_xboole_0(A_23, B_24), C_25)=k2_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.58/1.57  tff(c_16, plain, (![A_17, B_18, C_19]: (k3_xboole_0(k3_xboole_0(k2_xboole_0(A_17, B_18), k2_xboole_0(B_18, C_19)), k2_xboole_0(C_19, A_17))=k2_xboole_0(k2_xboole_0(k3_xboole_0(A_17, B_18), k3_xboole_0(B_18, C_19)), k3_xboole_0(C_19, A_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.58/1.57  tff(c_1464, plain, (![A_88, B_89, C_90]: (k3_xboole_0(k3_xboole_0(k2_xboole_0(A_88, B_89), k2_xboole_0(B_89, C_90)), k2_xboole_0(C_90, A_88))=k2_xboole_0(k3_xboole_0(A_88, B_89), k2_xboole_0(k3_xboole_0(B_89, C_90), k3_xboole_0(C_90, A_88))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16])).
% 3.58/1.57  tff(c_1614, plain, (![A_11, C_90]: (k2_xboole_0(k3_xboole_0(A_11, k1_xboole_0), k2_xboole_0(k3_xboole_0(k1_xboole_0, C_90), k3_xboole_0(C_90, A_11)))=k3_xboole_0(k3_xboole_0(A_11, k2_xboole_0(k1_xboole_0, C_90)), k2_xboole_0(C_90, A_11)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1464])).
% 3.58/1.57  tff(c_1663, plain, (![C_91, A_92]: (k3_xboole_0(C_91, A_92)=k3_xboole_0(A_92, C_91))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_18, c_168, c_64, c_14, c_168, c_4, c_1614])).
% 3.58/1.57  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.58/1.57  tff(c_1927, plain, (![A_93, C_94]: (r1_tarski(k3_xboole_0(A_93, C_94), C_94))), inference(superposition, [status(thm), theory('equality')], [c_1663, c_6])).
% 3.58/1.57  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.58/1.57  tff(c_201, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.58/1.57  tff(c_215, plain, (![A_40]: (r1_tarski(A_40, '#skF_4') | ~r1_tarski(A_40, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_201])).
% 3.58/1.57  tff(c_2012, plain, (![A_93]: (r1_tarski(k3_xboole_0(A_93, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_1927, c_215])).
% 3.58/1.57  tff(c_85, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k2_xboole_0(A_33, B_34))=A_33)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.58/1.57  tff(c_95, plain, (![A_33]: (r1_tarski(A_33, A_33))), inference(superposition, [status(thm), theory('equality')], [c_85, c_6])).
% 3.58/1.57  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.58/1.57  tff(c_378, plain, (![A_50]: (r1_tarski(A_50, '#skF_2') | ~r1_tarski(A_50, '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_201])).
% 3.58/1.57  tff(c_12, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, C_14) | ~r1_tarski(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.58/1.57  tff(c_1071, plain, (![A_76, A_77]: (r1_tarski(A_76, '#skF_2') | ~r1_tarski(A_76, A_77) | ~r1_tarski(A_77, '#skF_1'))), inference(resolution, [status(thm)], [c_378, c_12])).
% 3.58/1.57  tff(c_1089, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), '#skF_2') | ~r1_tarski(A_6, '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1071])).
% 3.58/1.57  tff(c_1148, plain, (![A_80, B_81, C_82]: (r1_tarski(A_80, k3_xboole_0(B_81, C_82)) | ~r1_tarski(A_80, C_82) | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.58/1.57  tff(c_26, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.58/1.57  tff(c_1199, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_4') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_1148, c_26])).
% 3.58/1.57  tff(c_1374, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1199])).
% 3.58/1.57  tff(c_1377, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1089, c_1374])).
% 3.58/1.57  tff(c_1384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_1377])).
% 3.58/1.57  tff(c_1385, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_1199])).
% 3.58/1.57  tff(c_2030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2012, c_1385])).
% 3.58/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.57  
% 3.58/1.57  Inference rules
% 3.58/1.57  ----------------------
% 3.58/1.57  #Ref     : 0
% 3.58/1.57  #Sup     : 497
% 3.58/1.57  #Fact    : 0
% 3.58/1.57  #Define  : 0
% 3.58/1.57  #Split   : 2
% 3.58/1.57  #Chain   : 0
% 3.58/1.58  #Close   : 0
% 3.58/1.58  
% 3.58/1.58  Ordering : KBO
% 3.58/1.58  
% 3.58/1.58  Simplification rules
% 3.58/1.58  ----------------------
% 3.58/1.58  #Subsume      : 23
% 3.58/1.58  #Demod        : 435
% 3.58/1.58  #Tautology    : 300
% 3.58/1.58  #SimpNegUnit  : 0
% 3.58/1.58  #BackRed      : 4
% 3.58/1.58  
% 3.58/1.58  #Partial instantiations: 0
% 3.58/1.58  #Strategies tried      : 1
% 3.58/1.58  
% 3.58/1.58  Timing (in seconds)
% 3.58/1.58  ----------------------
% 3.58/1.58  Preprocessing        : 0.29
% 3.58/1.58  Parsing              : 0.16
% 3.58/1.58  CNF conversion       : 0.02
% 3.58/1.58  Main loop            : 0.52
% 3.58/1.58  Inferencing          : 0.17
% 3.58/1.58  Reduction            : 0.21
% 3.58/1.58  Demodulation         : 0.17
% 3.58/1.58  BG Simplification    : 0.02
% 3.58/1.58  Subsumption          : 0.08
% 3.58/1.58  Abstraction          : 0.03
% 3.58/1.58  MUC search           : 0.00
% 3.58/1.58  Cooper               : 0.00
% 3.58/1.58  Total                : 0.84
% 3.58/1.58  Index Insertion      : 0.00
% 3.58/1.58  Index Deletion       : 0.00
% 3.58/1.58  Index Matching       : 0.00
% 3.58/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
