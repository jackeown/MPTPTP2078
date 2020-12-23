%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:42 EST 2020

% Result     : Theorem 13.01s
% Output     : CNFRefutation 13.01s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 231 expanded)
%              Number of leaves         :   25 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          :   90 ( 273 expanded)
%              Number of equality atoms :   56 ( 190 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_136,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_136])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_277,plain,(
    ! [A_46,B_47] : k2_xboole_0(k3_xboole_0(A_46,B_47),k4_xboole_0(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_922,plain,(
    ! [B_69,A_70] : k2_xboole_0(k3_xboole_0(B_69,A_70),k4_xboole_0(A_70,B_69)) = A_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_277])).

tff(c_996,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_4')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_922])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_208,plain,(
    ! [A_42,B_43] : k4_xboole_0(k2_xboole_0(A_42,B_43),B_43) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_215,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_xboole_0) = k2_xboole_0(A_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_14])).

tff(c_236,plain,(
    ! [A_44] : k2_xboole_0(A_44,k1_xboole_0) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_215])).

tff(c_264,plain,(
    ! [A_1] : k2_xboole_0(k1_xboole_0,A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_236])).

tff(c_1361,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_996,c_264])).

tff(c_32,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_33,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_51,plain,(
    ! [B_27,A_28] : k2_xboole_0(B_27,A_28) = k2_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(B_30,A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_24])).

tff(c_99,plain,(
    r1_tarski('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_90])).

tff(c_565,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_tarski(k4_xboole_0(A_53,B_54),C_55)
      | ~ r1_tarski(A_53,k2_xboole_0(B_54,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4365,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_xboole_0(k4_xboole_0(A_136,B_137),C_138) = C_138
      | ~ r1_tarski(A_136,k2_xboole_0(B_137,C_138)) ) ),
    inference(resolution,[status(thm)],[c_565,c_12])).

tff(c_4480,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_99,c_4365])).

tff(c_4534,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1361,c_4480])).

tff(c_310,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_277])).

tff(c_165,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1249,plain,(
    ! [A_74,B_75] : k2_xboole_0(A_74,k2_xboole_0(A_74,B_75)) = k2_xboole_0(A_74,B_75) ),
    inference(resolution,[status(thm)],[c_24,c_165])).

tff(c_1283,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = k2_xboole_0(k3_xboole_0(B_4,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_1249])).

tff(c_1607,plain,(
    ! [A_82,B_83] : k2_xboole_0(A_82,k3_xboole_0(B_83,A_82)) = A_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_2,c_1283])).

tff(c_1624,plain,(
    ! [B_83] : k3_xboole_0(B_83,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1607,c_264])).

tff(c_457,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_481,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_457])).

tff(c_1718,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_481])).

tff(c_221,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_208])).

tff(c_4556,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4534,c_221])).

tff(c_4580,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_4556])).

tff(c_22,plain,(
    ! [A_20,B_21] : k2_xboole_0(k3_xboole_0(A_20,B_21),k4_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4634,plain,(
    k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),k1_xboole_0) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4580,c_22])).

tff(c_4649,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_2,c_4,c_4634])).

tff(c_4808,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4649,c_22])).

tff(c_66,plain,(
    ! [A_28,B_27] : r1_tarski(A_28,k2_xboole_0(B_27,A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_24])).

tff(c_10291,plain,(
    ! [A_182,B_183] : k2_xboole_0(A_182,k2_xboole_0(B_183,A_182)) = k2_xboole_0(B_183,A_182) ),
    inference(resolution,[status(thm)],[c_66,c_165])).

tff(c_30422,plain,(
    ! [B_405,A_406] : k2_xboole_0(B_405,k2_xboole_0(B_405,A_406)) = k2_xboole_0(A_406,B_405) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10291])).

tff(c_30740,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_2'),'#skF_2') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4808,c_30422])).

tff(c_30894,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_2'),'#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_2,c_30740])).

tff(c_194,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,k2_xboole_0(C_40,B_41))
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_200,plain,(
    ! [A_39,B_2,A_1] :
      ( r1_tarski(A_39,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_39,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_194])).

tff(c_4516,plain,(
    ! [A_39,B_2,A_1] :
      ( k2_xboole_0(k4_xboole_0(A_39,B_2),A_1) = A_1
      | ~ r1_tarski(A_39,B_2) ) ),
    inference(resolution,[status(thm)],[c_200,c_4365])).

tff(c_30933,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30894,c_4516])).

tff(c_31050,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_30933])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_144,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_136])).

tff(c_304,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_1')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_277])).

tff(c_396,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_304])).

tff(c_40898,plain,(
    ! [C_456] :
      ( r1_tarski('#skF_3',C_456)
      | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_1',C_456)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_565])).

tff(c_40976,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_40898])).

tff(c_40990,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_40976])).

tff(c_40992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31050,c_40990])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:19:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.01/5.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.01/5.87  
% 13.01/5.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.01/5.87  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.01/5.87  
% 13.01/5.87  %Foreground sorts:
% 13.01/5.87  
% 13.01/5.87  
% 13.01/5.87  %Background operators:
% 13.01/5.87  
% 13.01/5.87  
% 13.01/5.87  %Foreground operators:
% 13.01/5.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.01/5.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.01/5.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.01/5.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.01/5.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.01/5.87  tff('#skF_2', type, '#skF_2': $i).
% 13.01/5.87  tff('#skF_3', type, '#skF_3': $i).
% 13.01/5.87  tff('#skF_1', type, '#skF_1': $i).
% 13.01/5.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.01/5.87  tff('#skF_4', type, '#skF_4': $i).
% 13.01/5.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.01/5.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.01/5.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.01/5.87  
% 13.01/5.89  tff(f_64, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 13.01/5.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.01/5.89  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 13.01/5.89  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.01/5.89  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 13.01/5.89  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.01/5.89  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 13.01/5.89  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.01/5.89  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 13.01/5.89  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.01/5.89  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.01/5.89  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 13.01/5.89  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.01/5.89  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.01/5.89  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.01/5.89  tff(c_136, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.01/5.89  tff(c_143, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_136])).
% 13.01/5.89  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.01/5.89  tff(c_277, plain, (![A_46, B_47]: (k2_xboole_0(k3_xboole_0(A_46, B_47), k4_xboole_0(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.01/5.89  tff(c_922, plain, (![B_69, A_70]: (k2_xboole_0(k3_xboole_0(B_69, A_70), k4_xboole_0(A_70, B_69))=A_70)), inference(superposition, [status(thm), theory('equality')], [c_4, c_277])).
% 13.01/5.89  tff(c_996, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_4'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_143, c_922])).
% 13.01/5.89  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.01/5.89  tff(c_208, plain, (![A_42, B_43]: (k4_xboole_0(k2_xboole_0(A_42, B_43), B_43)=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.01/5.89  tff(c_215, plain, (![A_42]: (k4_xboole_0(A_42, k1_xboole_0)=k2_xboole_0(A_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_208, c_14])).
% 13.01/5.89  tff(c_236, plain, (![A_44]: (k2_xboole_0(A_44, k1_xboole_0)=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_215])).
% 13.01/5.89  tff(c_264, plain, (![A_1]: (k2_xboole_0(k1_xboole_0, A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_236])).
% 13.01/5.89  tff(c_1361, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_996, c_264])).
% 13.01/5.89  tff(c_32, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.01/5.89  tff(c_33, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 13.01/5.89  tff(c_51, plain, (![B_27, A_28]: (k2_xboole_0(B_27, A_28)=k2_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.01/5.89  tff(c_24, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.01/5.89  tff(c_90, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(B_30, A_29)))), inference(superposition, [status(thm), theory('equality')], [c_51, c_24])).
% 13.01/5.89  tff(c_99, plain, (r1_tarski('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_33, c_90])).
% 13.01/5.89  tff(c_565, plain, (![A_53, B_54, C_55]: (r1_tarski(k4_xboole_0(A_53, B_54), C_55) | ~r1_tarski(A_53, k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.01/5.89  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.01/5.89  tff(c_4365, plain, (![A_136, B_137, C_138]: (k2_xboole_0(k4_xboole_0(A_136, B_137), C_138)=C_138 | ~r1_tarski(A_136, k2_xboole_0(B_137, C_138)))), inference(resolution, [status(thm)], [c_565, c_12])).
% 13.01/5.89  tff(c_4480, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_99, c_4365])).
% 13.01/5.89  tff(c_4534, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1361, c_4480])).
% 13.01/5.89  tff(c_310, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_277])).
% 13.01/5.89  tff(c_165, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.01/5.89  tff(c_1249, plain, (![A_74, B_75]: (k2_xboole_0(A_74, k2_xboole_0(A_74, B_75))=k2_xboole_0(A_74, B_75))), inference(resolution, [status(thm)], [c_24, c_165])).
% 13.01/5.89  tff(c_1283, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=k2_xboole_0(k3_xboole_0(B_4, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_310, c_1249])).
% 13.01/5.89  tff(c_1607, plain, (![A_82, B_83]: (k2_xboole_0(A_82, k3_xboole_0(B_83, A_82))=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_310, c_2, c_1283])).
% 13.01/5.89  tff(c_1624, plain, (![B_83]: (k3_xboole_0(B_83, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1607, c_264])).
% 13.01/5.89  tff(c_457, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.01/5.89  tff(c_481, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_457])).
% 13.01/5.89  tff(c_1718, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1624, c_481])).
% 13.01/5.89  tff(c_221, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_208])).
% 13.01/5.89  tff(c_4556, plain, (k4_xboole_0('#skF_2', '#skF_3')=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4534, c_221])).
% 13.01/5.89  tff(c_4580, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_4556])).
% 13.01/5.89  tff(c_22, plain, (![A_20, B_21]: (k2_xboole_0(k3_xboole_0(A_20, B_21), k4_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.01/5.89  tff(c_4634, plain, (k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), k1_xboole_0)='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_4580, c_22])).
% 13.01/5.89  tff(c_4649, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_264, c_2, c_4, c_4634])).
% 13.01/5.89  tff(c_4808, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4649, c_22])).
% 13.01/5.89  tff(c_66, plain, (![A_28, B_27]: (r1_tarski(A_28, k2_xboole_0(B_27, A_28)))), inference(superposition, [status(thm), theory('equality')], [c_51, c_24])).
% 13.01/5.89  tff(c_10291, plain, (![A_182, B_183]: (k2_xboole_0(A_182, k2_xboole_0(B_183, A_182))=k2_xboole_0(B_183, A_182))), inference(resolution, [status(thm)], [c_66, c_165])).
% 13.01/5.89  tff(c_30422, plain, (![B_405, A_406]: (k2_xboole_0(B_405, k2_xboole_0(B_405, A_406))=k2_xboole_0(A_406, B_405))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10291])).
% 13.01/5.89  tff(c_30740, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_2'), '#skF_2')=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4808, c_30422])).
% 13.01/5.89  tff(c_30894, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_2'), '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_2, c_30740])).
% 13.01/5.89  tff(c_194, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, k2_xboole_0(C_40, B_41)) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.01/5.89  tff(c_200, plain, (![A_39, B_2, A_1]: (r1_tarski(A_39, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_39, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_194])).
% 13.01/5.89  tff(c_4516, plain, (![A_39, B_2, A_1]: (k2_xboole_0(k4_xboole_0(A_39, B_2), A_1)=A_1 | ~r1_tarski(A_39, B_2))), inference(resolution, [status(thm)], [c_200, c_4365])).
% 13.01/5.89  tff(c_30933, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30894, c_4516])).
% 13.01/5.89  tff(c_31050, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_30933])).
% 13.01/5.89  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.01/5.89  tff(c_144, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_136])).
% 13.01/5.89  tff(c_304, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_1'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_144, c_277])).
% 13.01/5.89  tff(c_396, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_264, c_304])).
% 13.01/5.89  tff(c_40898, plain, (![C_456]: (r1_tarski('#skF_3', C_456) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_1', C_456)))), inference(superposition, [status(thm), theory('equality')], [c_396, c_565])).
% 13.01/5.89  tff(c_40976, plain, (r1_tarski('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_33, c_40898])).
% 13.01/5.89  tff(c_40990, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_40976])).
% 13.01/5.89  tff(c_40992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31050, c_40990])).
% 13.01/5.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.01/5.89  
% 13.01/5.89  Inference rules
% 13.01/5.89  ----------------------
% 13.01/5.89  #Ref     : 0
% 13.01/5.89  #Sup     : 10157
% 13.01/5.89  #Fact    : 0
% 13.01/5.89  #Define  : 0
% 13.01/5.89  #Split   : 7
% 13.01/5.89  #Chain   : 0
% 13.01/5.89  #Close   : 0
% 13.01/5.89  
% 13.01/5.89  Ordering : KBO
% 13.01/5.89  
% 13.01/5.89  Simplification rules
% 13.01/5.89  ----------------------
% 13.01/5.89  #Subsume      : 527
% 13.01/5.89  #Demod        : 10832
% 13.01/5.89  #Tautology    : 7215
% 13.01/5.89  #SimpNegUnit  : 10
% 13.01/5.89  #BackRed      : 15
% 13.01/5.89  
% 13.01/5.89  #Partial instantiations: 0
% 13.01/5.89  #Strategies tried      : 1
% 13.01/5.89  
% 13.01/5.89  Timing (in seconds)
% 13.01/5.89  ----------------------
% 13.01/5.89  Preprocessing        : 0.30
% 13.01/5.89  Parsing              : 0.16
% 13.01/5.89  CNF conversion       : 0.02
% 13.01/5.89  Main loop            : 4.83
% 13.01/5.89  Inferencing          : 0.76
% 13.01/5.89  Reduction            : 2.80
% 13.01/5.89  Demodulation         : 2.46
% 13.01/5.89  BG Simplification    : 0.08
% 13.01/5.89  Subsumption          : 0.95
% 13.01/5.89  Abstraction          : 0.12
% 13.01/5.89  MUC search           : 0.00
% 13.01/5.89  Cooper               : 0.00
% 13.01/5.89  Total                : 5.16
% 13.01/5.89  Index Insertion      : 0.00
% 13.01/5.89  Index Deletion       : 0.00
% 13.01/5.89  Index Matching       : 0.00
% 13.01/5.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
