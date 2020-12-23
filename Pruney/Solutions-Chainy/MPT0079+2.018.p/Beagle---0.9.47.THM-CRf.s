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
% DateTime   : Thu Dec  3 09:43:45 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 250 expanded)
%              Number of leaves         :   21 (  94 expanded)
%              Depth                    :   14
%              Number of atoms          :   74 ( 302 expanded)
%              Number of equality atoms :   67 ( 240 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_20,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_148,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_148])).

tff(c_22,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_107,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_114,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_107])).

tff(c_294,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_315,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_294])).

tff(c_328,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_315])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_341,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_18])).

tff(c_344,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_341])).

tff(c_372,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_344])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_191,plain,(
    ! [A_29,B_30] : k4_xboole_0(k2_xboole_0(A_29,B_30),B_30) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_201,plain,(
    ! [A_29] : k4_xboole_0(A_29,k1_xboole_0) = k2_xboole_0(A_29,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_10])).

tff(c_220,plain,(
    ! [A_29] : k2_xboole_0(A_29,k1_xboole_0) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_201])).

tff(c_585,plain,(
    ! [A_39,B_40] : k4_xboole_0(k2_xboole_0(A_39,B_40),A_39) = k4_xboole_0(B_40,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_611,plain,(
    ! [A_29] : k4_xboole_0(k1_xboole_0,A_29) = k4_xboole_0(A_29,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_585])).

tff(c_636,plain,(
    ! [A_29] : k4_xboole_0(k1_xboole_0,A_29) = k3_xboole_0(A_29,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_611])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_115,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_107])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_4])).

tff(c_312,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_294])).

tff(c_327,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_312])).

tff(c_406,plain,(
    ! [A_35,B_36,C_37] : k4_xboole_0(k4_xboole_0(A_35,B_36),C_37) = k4_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2481,plain,(
    ! [A_73,B_74,C_75] : k4_xboole_0(A_73,k2_xboole_0(k4_xboole_0(A_73,B_74),C_75)) = k4_xboole_0(k3_xboole_0(A_73,B_74),C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_406])).

tff(c_2626,plain,(
    ! [C_75] : k4_xboole_0(k3_xboole_0('#skF_3','#skF_1'),C_75) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_3',C_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_2481])).

tff(c_2730,plain,(
    ! [C_77] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_3',C_77)) = k3_xboole_0(C_77,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_123,c_4,c_2626])).

tff(c_2764,plain,(
    ! [B_2] : k4_xboole_0('#skF_3',k2_xboole_0(B_2,'#skF_3')) = k3_xboole_0(B_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2730])).

tff(c_26,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_1021,plain,(
    ! [C_47] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_1',C_47)) = k4_xboole_0('#skF_3',C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_406])).

tff(c_1048,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_1021])).

tff(c_4455,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k3_xboole_0('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2764,c_1048])).

tff(c_4456,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_4455])).

tff(c_4566,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4456,c_18])).

tff(c_4573,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4566])).

tff(c_698,plain,(
    ! [B_42,A_43] : k4_xboole_0(B_42,k3_xboole_0(A_43,B_42)) = k4_xboole_0(B_42,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_294])).

tff(c_764,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_698])).

tff(c_790,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_764])).

tff(c_309,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_294])).

tff(c_326,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_309])).

tff(c_357,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_18])).

tff(c_360,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_357])).

tff(c_549,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_163])).

tff(c_811,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_18])).

tff(c_814,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_4,c_811])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_819,plain,(
    ! [C_12] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_2',C_12)) = k4_xboole_0(k1_xboole_0,C_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_14])).

tff(c_2165,plain,(
    ! [C_65] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_2',C_65)) = k3_xboole_0(C_65,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_819])).

tff(c_7269,plain,(
    ! [B_114] : k4_xboole_0('#skF_2',k2_xboole_0(B_114,'#skF_2')) = k3_xboole_0(B_114,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2165])).

tff(c_7357,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_7269])).

tff(c_7378,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_7357])).

tff(c_423,plain,(
    ! [A_35,B_36,C_37] : k4_xboole_0(k4_xboole_0(A_35,B_36),k4_xboole_0(A_35,k2_xboole_0(B_36,C_37))) = k3_xboole_0(k4_xboole_0(A_35,B_36),C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_18])).

tff(c_7388,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_4'),k1_xboole_0) = k3_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7378,c_423])).

tff(c_7423,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4573,c_790,c_790,c_4,c_10,c_7388])).

tff(c_7425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_7423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:02:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.74/2.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.66  
% 7.74/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.66  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.74/2.66  
% 7.74/2.66  %Foreground sorts:
% 7.74/2.66  
% 7.74/2.66  
% 7.74/2.66  %Background operators:
% 7.74/2.66  
% 7.74/2.66  
% 7.74/2.66  %Foreground operators:
% 7.74/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.74/2.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.74/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.74/2.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.74/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.74/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.74/2.66  tff('#skF_1', type, '#skF_1': $i).
% 7.74/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.74/2.66  tff('#skF_4', type, '#skF_4': $i).
% 7.74/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.74/2.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.74/2.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.74/2.66  
% 7.74/2.68  tff(f_52, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 7.74/2.68  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.74/2.68  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.74/2.68  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.74/2.68  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.74/2.68  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.74/2.68  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 7.74/2.68  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.74/2.68  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.74/2.68  tff(c_20, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.74/2.68  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.74/2.68  tff(c_148, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.74/2.68  tff(c_163, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_148])).
% 7.74/2.68  tff(c_22, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.74/2.68  tff(c_107, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.74/2.68  tff(c_114, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_107])).
% 7.74/2.68  tff(c_294, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.74/2.68  tff(c_315, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_114, c_294])).
% 7.74/2.68  tff(c_328, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_315])).
% 7.74/2.68  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.74/2.68  tff(c_341, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_328, c_18])).
% 7.74/2.68  tff(c_344, plain, (k4_xboole_0('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_341])).
% 7.74/2.68  tff(c_372, plain, (k3_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_163, c_344])).
% 7.74/2.68  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.74/2.68  tff(c_191, plain, (![A_29, B_30]: (k4_xboole_0(k2_xboole_0(A_29, B_30), B_30)=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.74/2.68  tff(c_201, plain, (![A_29]: (k4_xboole_0(A_29, k1_xboole_0)=k2_xboole_0(A_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_191, c_10])).
% 7.74/2.68  tff(c_220, plain, (![A_29]: (k2_xboole_0(A_29, k1_xboole_0)=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_201])).
% 7.74/2.68  tff(c_585, plain, (![A_39, B_40]: (k4_xboole_0(k2_xboole_0(A_39, B_40), A_39)=k4_xboole_0(B_40, A_39))), inference(superposition, [status(thm), theory('equality')], [c_2, c_191])).
% 7.74/2.68  tff(c_611, plain, (![A_29]: (k4_xboole_0(k1_xboole_0, A_29)=k4_xboole_0(A_29, A_29))), inference(superposition, [status(thm), theory('equality')], [c_220, c_585])).
% 7.74/2.68  tff(c_636, plain, (![A_29]: (k4_xboole_0(k1_xboole_0, A_29)=k3_xboole_0(A_29, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_611])).
% 7.74/2.68  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.74/2.68  tff(c_115, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_107])).
% 7.74/2.68  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.74/2.68  tff(c_123, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_115, c_4])).
% 7.74/2.68  tff(c_312, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_115, c_294])).
% 7.74/2.68  tff(c_327, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_312])).
% 7.74/2.68  tff(c_406, plain, (![A_35, B_36, C_37]: (k4_xboole_0(k4_xboole_0(A_35, B_36), C_37)=k4_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.74/2.68  tff(c_2481, plain, (![A_73, B_74, C_75]: (k4_xboole_0(A_73, k2_xboole_0(k4_xboole_0(A_73, B_74), C_75))=k4_xboole_0(k3_xboole_0(A_73, B_74), C_75))), inference(superposition, [status(thm), theory('equality')], [c_18, c_406])).
% 7.74/2.68  tff(c_2626, plain, (![C_75]: (k4_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), C_75)=k4_xboole_0('#skF_3', k2_xboole_0('#skF_3', C_75)))), inference(superposition, [status(thm), theory('equality')], [c_327, c_2481])).
% 7.74/2.68  tff(c_2730, plain, (![C_77]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_3', C_77))=k3_xboole_0(C_77, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_636, c_123, c_4, c_2626])).
% 7.74/2.68  tff(c_2764, plain, (![B_2]: (k4_xboole_0('#skF_3', k2_xboole_0(B_2, '#skF_3'))=k3_xboole_0(B_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2730])).
% 7.74/2.68  tff(c_26, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.74/2.68  tff(c_27, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 7.74/2.68  tff(c_1021, plain, (![C_47]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_1', C_47))=k4_xboole_0('#skF_3', C_47))), inference(superposition, [status(thm), theory('equality')], [c_327, c_406])).
% 7.74/2.68  tff(c_1048, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27, c_1021])).
% 7.74/2.68  tff(c_4455, plain, (k4_xboole_0('#skF_3', '#skF_2')=k3_xboole_0('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2764, c_1048])).
% 7.74/2.68  tff(c_4456, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_372, c_4455])).
% 7.74/2.68  tff(c_4566, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4456, c_18])).
% 7.74/2.68  tff(c_4573, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4566])).
% 7.74/2.68  tff(c_698, plain, (![B_42, A_43]: (k4_xboole_0(B_42, k3_xboole_0(A_43, B_42))=k4_xboole_0(B_42, A_43))), inference(superposition, [status(thm), theory('equality')], [c_4, c_294])).
% 7.74/2.68  tff(c_764, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_114, c_698])).
% 7.74/2.68  tff(c_790, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_764])).
% 7.74/2.68  tff(c_309, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_123, c_294])).
% 7.74/2.68  tff(c_326, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_309])).
% 7.74/2.68  tff(c_357, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_326, c_18])).
% 7.74/2.68  tff(c_360, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_123, c_357])).
% 7.74/2.68  tff(c_549, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_360, c_163])).
% 7.74/2.68  tff(c_811, plain, (k4_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_790, c_18])).
% 7.74/2.68  tff(c_814, plain, (k4_xboole_0('#skF_2', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_4, c_811])).
% 7.74/2.68  tff(c_14, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.74/2.68  tff(c_819, plain, (![C_12]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_2', C_12))=k4_xboole_0(k1_xboole_0, C_12))), inference(superposition, [status(thm), theory('equality')], [c_814, c_14])).
% 7.74/2.68  tff(c_2165, plain, (![C_65]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_2', C_65))=k3_xboole_0(C_65, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_636, c_819])).
% 7.74/2.68  tff(c_7269, plain, (![B_114]: (k4_xboole_0('#skF_2', k2_xboole_0(B_114, '#skF_2'))=k3_xboole_0(B_114, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2165])).
% 7.74/2.68  tff(c_7357, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_27, c_7269])).
% 7.74/2.68  tff(c_7378, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_549, c_7357])).
% 7.74/2.68  tff(c_423, plain, (![A_35, B_36, C_37]: (k4_xboole_0(k4_xboole_0(A_35, B_36), k4_xboole_0(A_35, k2_xboole_0(B_36, C_37)))=k3_xboole_0(k4_xboole_0(A_35, B_36), C_37))), inference(superposition, [status(thm), theory('equality')], [c_406, c_18])).
% 7.74/2.68  tff(c_7388, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), k1_xboole_0)=k3_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7378, c_423])).
% 7.74/2.68  tff(c_7423, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4573, c_790, c_790, c_4, c_10, c_7388])).
% 7.74/2.68  tff(c_7425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_7423])).
% 7.74/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.68  
% 7.74/2.68  Inference rules
% 7.74/2.68  ----------------------
% 7.74/2.68  #Ref     : 0
% 7.74/2.68  #Sup     : 1821
% 7.74/2.68  #Fact    : 0
% 7.74/2.68  #Define  : 0
% 7.74/2.68  #Split   : 0
% 7.74/2.68  #Chain   : 0
% 7.74/2.68  #Close   : 0
% 7.74/2.68  
% 7.74/2.68  Ordering : KBO
% 7.74/2.68  
% 7.74/2.68  Simplification rules
% 7.74/2.68  ----------------------
% 7.74/2.68  #Subsume      : 64
% 7.74/2.68  #Demod        : 2811
% 7.74/2.68  #Tautology    : 1022
% 7.74/2.68  #SimpNegUnit  : 1
% 7.74/2.68  #BackRed      : 5
% 7.74/2.68  
% 7.74/2.68  #Partial instantiations: 0
% 7.74/2.68  #Strategies tried      : 1
% 7.74/2.68  
% 7.74/2.68  Timing (in seconds)
% 7.74/2.68  ----------------------
% 7.74/2.68  Preprocessing        : 0.29
% 7.74/2.68  Parsing              : 0.16
% 7.74/2.68  CNF conversion       : 0.02
% 7.74/2.68  Main loop            : 1.63
% 7.74/2.68  Inferencing          : 0.38
% 7.74/2.68  Reduction            : 0.91
% 7.74/2.68  Demodulation         : 0.80
% 7.74/2.68  BG Simplification    : 0.05
% 7.74/2.68  Subsumption          : 0.22
% 7.74/2.68  Abstraction          : 0.07
% 7.74/2.68  MUC search           : 0.00
% 7.74/2.68  Cooper               : 0.00
% 7.74/2.68  Total                : 1.95
% 7.74/2.68  Index Insertion      : 0.00
% 7.74/2.68  Index Deletion       : 0.00
% 7.74/2.68  Index Matching       : 0.00
% 7.74/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
