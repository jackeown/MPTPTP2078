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
% DateTime   : Thu Dec  3 09:45:30 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 118 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   69 ( 132 expanded)
%              Number of equality atoms :   40 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k4_xboole_0(A,B),C)
        & r1_tarski(k4_xboole_0(B,A),C) )
     => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [B_28,A_29] : k5_xboole_0(B_28,A_29) = k5_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    ! [A_29] : k5_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_12])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_426,plain,(
    ! [A_44,B_45,C_46] : k5_xboole_0(k5_xboole_0(A_44,B_45),C_46) = k5_xboole_0(A_44,k5_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_507,plain,(
    ! [A_16,C_46] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_46)) = k5_xboole_0(k1_xboole_0,C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_426])).

tff(c_1229,plain,(
    ! [A_66,C_67] : k5_xboole_0(A_66,k5_xboole_0(A_66,C_67)) = C_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_507])).

tff(c_1290,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k5_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1229])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_151,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_162,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_151])).

tff(c_230,plain,(
    ! [A_40,B_41] : k5_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_243,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_230])).

tff(c_253,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_243])).

tff(c_22,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_258,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_22])).

tff(c_264,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_258])).

tff(c_289,plain,(
    ! [A_42,B_43] : k5_xboole_0(k5_xboole_0(A_42,B_43),k2_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_310,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_289])).

tff(c_340,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_310])).

tff(c_1349,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_340])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_191,plain,(
    ! [A_35,B_36,C_37] :
      ( r1_tarski(A_35,B_36)
      | ~ r1_tarski(A_35,k3_xboole_0(B_36,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_202,plain,(
    ! [B_36,C_37,B_11] : r1_tarski(k4_xboole_0(k3_xboole_0(B_36,C_37),B_11),B_36) ),
    inference(resolution,[status(thm)],[c_10,c_191])).

tff(c_1495,plain,(
    ! [B_11] : r1_tarski(k4_xboole_0('#skF_3',B_11),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_202])).

tff(c_751,plain,(
    ! [A_51,C_52] : k5_xboole_0(A_51,k5_xboole_0(A_51,C_52)) = C_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_507])).

tff(c_812,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k5_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_751])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_163,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_151])).

tff(c_246,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_230])).

tff(c_254,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_246])).

tff(c_273,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_22])).

tff(c_279,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_273])).

tff(c_18,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k2_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_345,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_1'),'#skF_2') = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_18])).

tff(c_348,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_345])).

tff(c_1033,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_348])).

tff(c_1129,plain,(
    ! [B_11] : r1_tarski(k4_xboole_0('#skF_1',B_11),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_202])).

tff(c_614,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(k5_xboole_0(A_47,B_48),C_49)
      | ~ r1_tarski(k4_xboole_0(B_48,A_47),C_49)
      | ~ r1_tarski(k4_xboole_0(A_47,B_48),C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_657,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_614,c_24])).

tff(c_695,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_1206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_695])).

tff(c_1207,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_1507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:40:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.48  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.22/1.48  
% 3.22/1.48  %Foreground sorts:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Background operators:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Foreground operators:
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.22/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.22/1.48  
% 3.22/1.50  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.22/1.50  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.22/1.50  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.22/1.50  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.22/1.50  tff(f_62, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 3.22/1.50  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.22/1.50  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.22/1.50  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.22/1.50  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.22/1.50  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.22/1.50  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.22/1.50  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_xboole_1)).
% 3.22/1.50  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.50  tff(c_56, plain, (![B_28, A_29]: (k5_xboole_0(B_28, A_29)=k5_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.50  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.50  tff(c_72, plain, (![A_29]: (k5_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_56, c_12])).
% 3.22/1.50  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.22/1.50  tff(c_426, plain, (![A_44, B_45, C_46]: (k5_xboole_0(k5_xboole_0(A_44, B_45), C_46)=k5_xboole_0(A_44, k5_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.22/1.50  tff(c_507, plain, (![A_16, C_46]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_46))=k5_xboole_0(k1_xboole_0, C_46))), inference(superposition, [status(thm), theory('equality')], [c_16, c_426])).
% 3.22/1.50  tff(c_1229, plain, (![A_66, C_67]: (k5_xboole_0(A_66, k5_xboole_0(A_66, C_67))=C_67)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_507])).
% 3.22/1.50  tff(c_1290, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k5_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1229])).
% 3.22/1.50  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.22/1.50  tff(c_151, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.50  tff(c_162, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_26, c_151])).
% 3.22/1.50  tff(c_230, plain, (![A_40, B_41]: (k5_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.50  tff(c_243, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_162, c_230])).
% 3.22/1.50  tff(c_253, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_243])).
% 3.22/1.50  tff(c_22, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.22/1.50  tff(c_258, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_253, c_22])).
% 3.22/1.50  tff(c_264, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_258])).
% 3.22/1.50  tff(c_289, plain, (![A_42, B_43]: (k5_xboole_0(k5_xboole_0(A_42, B_43), k2_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.50  tff(c_310, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_264, c_289])).
% 3.22/1.50  tff(c_340, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_310])).
% 3.22/1.50  tff(c_1349, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1290, c_340])).
% 3.22/1.50  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.50  tff(c_191, plain, (![A_35, B_36, C_37]: (r1_tarski(A_35, B_36) | ~r1_tarski(A_35, k3_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.50  tff(c_202, plain, (![B_36, C_37, B_11]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_36, C_37), B_11), B_36))), inference(resolution, [status(thm)], [c_10, c_191])).
% 3.22/1.50  tff(c_1495, plain, (![B_11]: (r1_tarski(k4_xboole_0('#skF_3', B_11), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1349, c_202])).
% 3.22/1.50  tff(c_751, plain, (![A_51, C_52]: (k5_xboole_0(A_51, k5_xboole_0(A_51, C_52))=C_52)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_507])).
% 3.22/1.50  tff(c_812, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k5_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_751])).
% 3.22/1.50  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.22/1.50  tff(c_163, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_28, c_151])).
% 3.22/1.50  tff(c_246, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_163, c_230])).
% 3.22/1.50  tff(c_254, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_246])).
% 3.22/1.50  tff(c_273, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_254, c_22])).
% 3.22/1.50  tff(c_279, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_273])).
% 3.22/1.50  tff(c_18, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k2_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.50  tff(c_345, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_1'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_279, c_18])).
% 3.22/1.50  tff(c_348, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_345])).
% 3.22/1.50  tff(c_1033, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_812, c_348])).
% 3.22/1.50  tff(c_1129, plain, (![B_11]: (r1_tarski(k4_xboole_0('#skF_1', B_11), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1033, c_202])).
% 3.22/1.50  tff(c_614, plain, (![A_47, B_48, C_49]: (r1_tarski(k5_xboole_0(A_47, B_48), C_49) | ~r1_tarski(k4_xboole_0(B_48, A_47), C_49) | ~r1_tarski(k4_xboole_0(A_47, B_48), C_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.22/1.50  tff(c_24, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.22/1.50  tff(c_657, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_614, c_24])).
% 3.22/1.50  tff(c_695, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_657])).
% 3.22/1.50  tff(c_1206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1129, c_695])).
% 3.22/1.50  tff(c_1207, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_657])).
% 3.22/1.50  tff(c_1507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1207])).
% 3.22/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  Inference rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Ref     : 0
% 3.22/1.50  #Sup     : 410
% 3.22/1.50  #Fact    : 0
% 3.22/1.50  #Define  : 0
% 3.22/1.50  #Split   : 1
% 3.22/1.50  #Chain   : 0
% 3.22/1.50  #Close   : 0
% 3.22/1.50  
% 3.22/1.50  Ordering : KBO
% 3.22/1.50  
% 3.22/1.50  Simplification rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Subsume      : 4
% 3.22/1.50  #Demod        : 196
% 3.22/1.50  #Tautology    : 233
% 3.22/1.50  #SimpNegUnit  : 0
% 3.22/1.50  #BackRed      : 7
% 3.22/1.50  
% 3.22/1.50  #Partial instantiations: 0
% 3.22/1.50  #Strategies tried      : 1
% 3.22/1.50  
% 3.22/1.50  Timing (in seconds)
% 3.22/1.50  ----------------------
% 3.22/1.50  Preprocessing        : 0.27
% 3.22/1.50  Parsing              : 0.15
% 3.22/1.50  CNF conversion       : 0.02
% 3.22/1.50  Main loop            : 0.47
% 3.22/1.50  Inferencing          : 0.15
% 3.22/1.50  Reduction            : 0.19
% 3.22/1.50  Demodulation         : 0.15
% 3.22/1.50  BG Simplification    : 0.02
% 3.22/1.50  Subsumption          : 0.06
% 3.22/1.50  Abstraction          : 0.02
% 3.22/1.50  MUC search           : 0.00
% 3.22/1.50  Cooper               : 0.00
% 3.22/1.50  Total                : 0.77
% 3.22/1.50  Index Insertion      : 0.00
% 3.22/1.50  Index Deletion       : 0.00
% 3.22/1.50  Index Matching       : 0.00
% 3.22/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
