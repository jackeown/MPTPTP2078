%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:27 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 136 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 153 expanded)
%              Number of equality atoms :   56 ( 112 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_609,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_37,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_617,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_609,c_37])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_624,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_642,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_624])).

tff(c_645,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_642])).

tff(c_525,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(A_34,B_35)
      | k3_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_533,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_525,c_37])).

tff(c_534,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_555,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_534])).

tff(c_559,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_555])).

tff(c_16,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_20,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_39,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_39])).

tff(c_58,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_58])).

tff(c_77,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_73])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = k3_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_10])).

tff(c_144,plain,(
    ! [A_22] : k3_xboole_0(A_22,A_22) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_82])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k3_xboole_0(A_7,B_8),C_9) = k3_xboole_0(A_7,k4_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_150,plain,(
    ! [A_22,C_9] : k3_xboole_0(A_22,k4_xboole_0(A_22,C_9)) = k4_xboole_0(A_22,C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_12])).

tff(c_67,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_58])).

tff(c_437,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_67])).

tff(c_493,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_437])).

tff(c_512,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_493])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_512])).

tff(c_515,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_552,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_534])).

tff(c_601,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_552])).

tff(c_602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_601])).

tff(c_603,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_639,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_624])).

tff(c_732,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_639])).

tff(c_733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_617,c_732])).

tff(c_735,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_14,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_736,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_760,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_775,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_760])).

tff(c_820,plain,(
    ! [A_60] : k4_xboole_0(A_60,A_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_775])).

tff(c_829,plain,(
    ! [A_60] : k4_xboole_0(A_60,k1_xboole_0) = k3_xboole_0(A_60,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_10])).

tff(c_849,plain,(
    ! [A_61] : k3_xboole_0(A_61,A_61) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_829])).

tff(c_1260,plain,(
    ! [A_72,C_73] : k3_xboole_0(A_72,k4_xboole_0(A_72,C_73)) = k4_xboole_0(A_72,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_12])).

tff(c_734,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_738,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_746,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_734,c_738])).

tff(c_961,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,k4_xboole_0(A_66,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_760])).

tff(c_998,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_961])).

tff(c_1013,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_998])).

tff(c_1273,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1260,c_1013])).

tff(c_1326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_736,c_1273])).

tff(c_1327,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_1330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_1327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.42  
% 2.60/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.42  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.60/1.42  
% 2.60/1.42  %Foreground sorts:
% 2.60/1.42  
% 2.60/1.42  
% 2.60/1.42  %Background operators:
% 2.60/1.42  
% 2.60/1.42  
% 2.60/1.42  %Foreground operators:
% 2.60/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.60/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.42  
% 2.60/1.44  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.60/1.44  tff(f_42, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.60/1.44  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.60/1.44  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.60/1.44  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.60/1.44  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.60/1.44  tff(c_609, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.44  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.60/1.44  tff(c_37, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_18])).
% 2.60/1.44  tff(c_617, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_609, c_37])).
% 2.60/1.44  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.44  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.44  tff(c_624, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.44  tff(c_642, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_624])).
% 2.60/1.44  tff(c_645, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_642])).
% 2.60/1.44  tff(c_525, plain, (![A_34, B_35]: (r1_xboole_0(A_34, B_35) | k3_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.44  tff(c_533, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_525, c_37])).
% 2.60/1.44  tff(c_534, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.44  tff(c_555, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_534])).
% 2.60/1.44  tff(c_559, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_555])).
% 2.60/1.44  tff(c_16, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.60/1.44  tff(c_48, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_16])).
% 2.60/1.44  tff(c_20, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.60/1.44  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_20])).
% 2.60/1.44  tff(c_39, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.44  tff(c_43, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_39])).
% 2.60/1.44  tff(c_58, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.44  tff(c_73, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_58])).
% 2.60/1.44  tff(c_77, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_73])).
% 2.60/1.44  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.44  tff(c_82, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=k3_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_77, c_10])).
% 2.60/1.44  tff(c_144, plain, (![A_22]: (k3_xboole_0(A_22, A_22)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_82])).
% 2.60/1.44  tff(c_12, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k3_xboole_0(A_7, B_8), C_9)=k3_xboole_0(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.60/1.44  tff(c_150, plain, (![A_22, C_9]: (k3_xboole_0(A_22, k4_xboole_0(A_22, C_9))=k4_xboole_0(A_22, C_9))), inference(superposition, [status(thm), theory('equality')], [c_144, c_12])).
% 2.60/1.44  tff(c_67, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k3_xboole_0(A_5, k4_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_58])).
% 2.60/1.44  tff(c_437, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_67])).
% 2.60/1.44  tff(c_493, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_43, c_437])).
% 2.60/1.44  tff(c_512, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_493])).
% 2.60/1.44  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_512])).
% 2.60/1.44  tff(c_515, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 2.60/1.44  tff(c_552, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_515, c_534])).
% 2.60/1.44  tff(c_601, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_559, c_552])).
% 2.60/1.44  tff(c_602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_533, c_601])).
% 2.60/1.44  tff(c_603, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 2.60/1.44  tff(c_639, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_603, c_624])).
% 2.60/1.44  tff(c_732, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_645, c_639])).
% 2.60/1.44  tff(c_733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_617, c_732])).
% 2.60/1.44  tff(c_735, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_18])).
% 2.60/1.44  tff(c_14, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.60/1.44  tff(c_736, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_14])).
% 2.60/1.44  tff(c_760, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.44  tff(c_775, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_760])).
% 2.60/1.44  tff(c_820, plain, (![A_60]: (k4_xboole_0(A_60, A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_775])).
% 2.60/1.44  tff(c_829, plain, (![A_60]: (k4_xboole_0(A_60, k1_xboole_0)=k3_xboole_0(A_60, A_60))), inference(superposition, [status(thm), theory('equality')], [c_820, c_10])).
% 2.60/1.44  tff(c_849, plain, (![A_61]: (k3_xboole_0(A_61, A_61)=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_829])).
% 2.60/1.44  tff(c_1260, plain, (![A_72, C_73]: (k3_xboole_0(A_72, k4_xboole_0(A_72, C_73))=k4_xboole_0(A_72, C_73))), inference(superposition, [status(thm), theory('equality')], [c_849, c_12])).
% 2.60/1.44  tff(c_734, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_18])).
% 2.60/1.44  tff(c_738, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.44  tff(c_746, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_734, c_738])).
% 2.60/1.44  tff(c_961, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k3_xboole_0(A_66, k4_xboole_0(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_760])).
% 2.60/1.44  tff(c_998, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_746, c_961])).
% 2.60/1.44  tff(c_1013, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_998])).
% 2.60/1.44  tff(c_1273, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1260, c_1013])).
% 2.60/1.44  tff(c_1326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_736, c_1273])).
% 2.60/1.44  tff(c_1327, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_14])).
% 2.60/1.44  tff(c_1330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_735, c_1327])).
% 2.60/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.44  
% 2.60/1.44  Inference rules
% 2.60/1.44  ----------------------
% 2.60/1.44  #Ref     : 0
% 2.60/1.44  #Sup     : 322
% 2.60/1.44  #Fact    : 0
% 2.60/1.44  #Define  : 0
% 2.60/1.44  #Split   : 4
% 2.60/1.44  #Chain   : 0
% 2.60/1.44  #Close   : 0
% 2.60/1.44  
% 2.60/1.44  Ordering : KBO
% 2.60/1.44  
% 2.60/1.44  Simplification rules
% 2.60/1.44  ----------------------
% 2.60/1.44  #Subsume      : 3
% 2.60/1.44  #Demod        : 221
% 2.60/1.44  #Tautology    : 208
% 2.60/1.44  #SimpNegUnit  : 4
% 2.60/1.44  #BackRed      : 1
% 2.60/1.44  
% 2.60/1.44  #Partial instantiations: 0
% 2.60/1.44  #Strategies tried      : 1
% 2.60/1.44  
% 2.60/1.44  Timing (in seconds)
% 2.60/1.44  ----------------------
% 2.60/1.44  Preprocessing        : 0.28
% 2.60/1.44  Parsing              : 0.15
% 2.60/1.44  CNF conversion       : 0.02
% 2.60/1.44  Main loop            : 0.39
% 2.60/1.44  Inferencing          : 0.15
% 2.60/1.44  Reduction            : 0.14
% 2.60/1.44  Demodulation         : 0.11
% 2.60/1.44  BG Simplification    : 0.02
% 2.60/1.44  Subsumption          : 0.05
% 2.60/1.44  Abstraction          : 0.03
% 2.60/1.44  MUC search           : 0.00
% 2.60/1.44  Cooper               : 0.00
% 2.60/1.44  Total                : 0.70
% 2.60/1.44  Index Insertion      : 0.00
% 2.60/1.44  Index Deletion       : 0.00
% 2.60/1.45  Index Matching       : 0.00
% 2.60/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
