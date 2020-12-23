%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:26 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 133 expanded)
%              Number of leaves         :   18 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 147 expanded)
%              Number of equality atoms :   56 ( 110 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_319,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(A_36,B_37)
      | k3_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_39,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_331,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_319,c_39])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_349,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_370,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_349])).

tff(c_373,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_370])).

tff(c_41,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41,c_39])).

tff(c_262,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_283,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_262])).

tff(c_287,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_283])).

tff(c_18,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_95,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k4_xboole_0(A_22,B_23),k3_xboole_0(A_22,C_24)) = k4_xboole_0(A_22,k4_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_110,plain,(
    ! [A_3,B_23] : k4_xboole_0(A_3,k4_xboole_0(B_23,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_3,B_23),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_95])).

tff(c_227,plain,(
    ! [A_29,B_30] : k2_xboole_0(k4_xboole_0(A_29,B_30),k1_xboole_0) = k4_xboole_0(A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_110])).

tff(c_73,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_73])).

tff(c_94,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_91])).

tff(c_22,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_46,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_46])).

tff(c_184,plain,(
    ! [B_28] : k4_xboole_0('#skF_3',k4_xboole_0(B_28,'#skF_4')) = k2_xboole_0(k4_xboole_0('#skF_3',B_28),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_95])).

tff(c_207,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_184])).

tff(c_215,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_207])).

tff(c_233,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_215])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_233])).

tff(c_252,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_280,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_262])).

tff(c_310,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_280])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_310])).

tff(c_312,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_367,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_349])).

tff(c_418,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_367])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_418])).

tff(c_421,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_16,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_424,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_16])).

tff(c_447,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k4_xboole_0(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_462,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_447])).

tff(c_465,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_462])).

tff(c_590,plain,(
    ! [A_57,B_58,C_59] : k2_xboole_0(k4_xboole_0(A_57,B_58),k3_xboole_0(A_57,C_59)) = k4_xboole_0(A_57,k4_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_623,plain,(
    ! [A_3,B_58] : k4_xboole_0(A_3,k4_xboole_0(B_58,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_3,B_58),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_590])).

tff(c_631,plain,(
    ! [A_60,B_61] : k2_xboole_0(k4_xboole_0(A_60,B_61),k1_xboole_0) = k4_xboole_0(A_60,B_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_623])).

tff(c_649,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_631])).

tff(c_655,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_649])).

tff(c_420,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_426,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_438,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_420,c_426])).

tff(c_617,plain,(
    ! [B_58] : k4_xboole_0('#skF_3',k4_xboole_0(B_58,'#skF_4')) = k2_xboole_0(k4_xboole_0('#skF_3',B_58),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_590])).

tff(c_779,plain,(
    ! [B_67] : k4_xboole_0('#skF_3',k4_xboole_0(B_67,'#skF_4')) = k4_xboole_0('#skF_3',B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_617])).

tff(c_810,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_779])).

tff(c_822,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_810])).

tff(c_824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_424,c_822])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:21:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.33  
% 2.46/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.34  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.46/1.34  
% 2.46/1.34  %Foreground sorts:
% 2.46/1.34  
% 2.46/1.34  
% 2.46/1.34  %Background operators:
% 2.46/1.34  
% 2.46/1.34  
% 2.46/1.34  %Foreground operators:
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.46/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.46/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.46/1.34  
% 2.46/1.35  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.46/1.35  tff(f_44, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.46/1.35  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.46/1.35  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.46/1.35  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.46/1.35  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.46/1.35  tff(c_319, plain, (![A_36, B_37]: (r1_xboole_0(A_36, B_37) | k3_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.35  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.46/1.35  tff(c_39, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_20])).
% 2.46/1.35  tff(c_331, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_319, c_39])).
% 2.46/1.35  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.35  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.46/1.35  tff(c_349, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.35  tff(c_370, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_349])).
% 2.46/1.35  tff(c_373, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_370])).
% 2.46/1.35  tff(c_41, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.35  tff(c_45, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_41, c_39])).
% 2.46/1.35  tff(c_262, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.35  tff(c_283, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_262])).
% 2.46/1.35  tff(c_287, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_283])).
% 2.46/1.35  tff(c_18, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.46/1.35  tff(c_59, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_18])).
% 2.46/1.35  tff(c_95, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k4_xboole_0(A_22, B_23), k3_xboole_0(A_22, C_24))=k4_xboole_0(A_22, k4_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.46/1.35  tff(c_110, plain, (![A_3, B_23]: (k4_xboole_0(A_3, k4_xboole_0(B_23, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_3, B_23), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_95])).
% 2.46/1.35  tff(c_227, plain, (![A_29, B_30]: (k2_xboole_0(k4_xboole_0(A_29, B_30), k1_xboole_0)=k4_xboole_0(A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_110])).
% 2.46/1.35  tff(c_73, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.35  tff(c_91, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_73])).
% 2.46/1.35  tff(c_94, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_91])).
% 2.46/1.35  tff(c_22, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.46/1.35  tff(c_40, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_22])).
% 2.46/1.35  tff(c_46, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.35  tff(c_54, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_46])).
% 2.46/1.35  tff(c_184, plain, (![B_28]: (k4_xboole_0('#skF_3', k4_xboole_0(B_28, '#skF_4'))=k2_xboole_0(k4_xboole_0('#skF_3', B_28), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_95])).
% 2.46/1.35  tff(c_207, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_94, c_184])).
% 2.46/1.35  tff(c_215, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_207])).
% 2.46/1.35  tff(c_233, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_227, c_215])).
% 2.46/1.35  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_233])).
% 2.46/1.35  tff(c_252, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_18])).
% 2.46/1.35  tff(c_280, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_252, c_262])).
% 2.46/1.35  tff(c_310, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_287, c_280])).
% 2.46/1.35  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_310])).
% 2.46/1.35  tff(c_312, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_22])).
% 2.46/1.35  tff(c_367, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_312, c_349])).
% 2.46/1.35  tff(c_418, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_373, c_367])).
% 2.46/1.35  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_331, c_418])).
% 2.46/1.35  tff(c_421, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_20])).
% 2.46/1.35  tff(c_16, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.46/1.35  tff(c_424, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_421, c_16])).
% 2.46/1.35  tff(c_447, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k4_xboole_0(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.35  tff(c_462, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_447])).
% 2.46/1.35  tff(c_465, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_462])).
% 2.46/1.35  tff(c_590, plain, (![A_57, B_58, C_59]: (k2_xboole_0(k4_xboole_0(A_57, B_58), k3_xboole_0(A_57, C_59))=k4_xboole_0(A_57, k4_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.46/1.35  tff(c_623, plain, (![A_3, B_58]: (k4_xboole_0(A_3, k4_xboole_0(B_58, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_3, B_58), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_590])).
% 2.46/1.35  tff(c_631, plain, (![A_60, B_61]: (k2_xboole_0(k4_xboole_0(A_60, B_61), k1_xboole_0)=k4_xboole_0(A_60, B_61))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_623])).
% 2.46/1.35  tff(c_649, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_631])).
% 2.46/1.35  tff(c_655, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_649])).
% 2.46/1.35  tff(c_420, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_20])).
% 2.46/1.35  tff(c_426, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.35  tff(c_438, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_420, c_426])).
% 2.46/1.35  tff(c_617, plain, (![B_58]: (k4_xboole_0('#skF_3', k4_xboole_0(B_58, '#skF_4'))=k2_xboole_0(k4_xboole_0('#skF_3', B_58), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_438, c_590])).
% 2.46/1.35  tff(c_779, plain, (![B_67]: (k4_xboole_0('#skF_3', k4_xboole_0(B_67, '#skF_4'))=k4_xboole_0('#skF_3', B_67))), inference(demodulation, [status(thm), theory('equality')], [c_655, c_617])).
% 2.46/1.35  tff(c_810, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_465, c_779])).
% 2.46/1.35  tff(c_822, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_810])).
% 2.46/1.35  tff(c_824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_424, c_822])).
% 2.46/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.35  
% 2.46/1.35  Inference rules
% 2.46/1.35  ----------------------
% 2.46/1.35  #Ref     : 0
% 2.46/1.35  #Sup     : 202
% 2.46/1.35  #Fact    : 0
% 2.46/1.35  #Define  : 0
% 2.46/1.35  #Split   : 3
% 2.46/1.35  #Chain   : 0
% 2.46/1.35  #Close   : 0
% 2.46/1.35  
% 2.46/1.35  Ordering : KBO
% 2.46/1.35  
% 2.46/1.35  Simplification rules
% 2.46/1.35  ----------------------
% 2.46/1.35  #Subsume      : 3
% 2.46/1.35  #Demod        : 76
% 2.46/1.35  #Tautology    : 128
% 2.46/1.35  #SimpNegUnit  : 4
% 2.46/1.35  #BackRed      : 2
% 2.46/1.35  
% 2.46/1.35  #Partial instantiations: 0
% 2.46/1.35  #Strategies tried      : 1
% 2.46/1.35  
% 2.46/1.35  Timing (in seconds)
% 2.46/1.35  ----------------------
% 2.46/1.35  Preprocessing        : 0.26
% 2.46/1.35  Parsing              : 0.15
% 2.46/1.35  CNF conversion       : 0.02
% 2.46/1.35  Main loop            : 0.31
% 2.46/1.35  Inferencing          : 0.13
% 2.46/1.35  Reduction            : 0.09
% 2.46/1.35  Demodulation         : 0.07
% 2.46/1.35  BG Simplification    : 0.02
% 2.46/1.35  Subsumption          : 0.04
% 2.46/1.35  Abstraction          : 0.02
% 2.46/1.35  MUC search           : 0.00
% 2.46/1.35  Cooper               : 0.00
% 2.46/1.36  Total                : 0.60
% 2.46/1.36  Index Insertion      : 0.00
% 2.46/1.36  Index Deletion       : 0.00
% 2.46/1.36  Index Matching       : 0.00
% 2.46/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
