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
% DateTime   : Thu Dec  3 09:43:37 EST 2020

% Result     : Theorem 17.14s
% Output     : CNFRefutation 17.25s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 431 expanded)
%              Number of leaves         :   25 ( 149 expanded)
%              Depth                    :   11
%              Number of atoms          :  183 ( 757 expanded)
%              Number of equality atoms :   60 ( 217 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_189,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(A_38,B_39)
      | k3_xboole_0(A_38,B_39) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_201,plain,(
    ! [B_40,A_41] :
      ( r1_xboole_0(B_40,A_41)
      | k3_xboole_0(A_41,B_40) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_189,c_8])).

tff(c_28,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_166,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_211,plain,(
    k3_xboole_0('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_201,c_166])).

tff(c_72,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_87,plain,(
    ! [A_31,B_30] : r1_tarski(A_31,k2_xboole_0(B_30,A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_213,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_219,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_213,c_4])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_39,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_292,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_298,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_292,c_4])).

tff(c_320,plain,(
    ! [A_46,B_47] : k2_xboole_0(k3_xboole_0(A_46,B_47),k4_xboole_0(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_341,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_6')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_320])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_31] : k2_xboole_0(k1_xboole_0,A_31) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_10])).

tff(c_410,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_94])).

tff(c_561,plain,(
    ! [A_60,B_61,C_62] : k4_xboole_0(k4_xboole_0(A_60,B_61),C_62) = k4_xboole_0(A_60,k2_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3333,plain,(
    ! [A_135,B_136,C_137] : k4_xboole_0(k4_xboole_0(A_135,B_136),k4_xboole_0(A_135,k2_xboole_0(B_136,C_137))) = k3_xboole_0(k4_xboole_0(A_135,B_136),C_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_18])).

tff(c_3428,plain,(
    ! [C_137] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_137))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_6'),C_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_3333])).

tff(c_3479,plain,(
    ! [C_137] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_137)) = k3_xboole_0('#skF_4',C_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_410,c_3428])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_37,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_34])).

tff(c_422,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_449,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_422])).

tff(c_16910,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3479,c_449])).

tff(c_16913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_16910])).

tff(c_16914,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_16948,plain,(
    r1_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_16914,c_8])).

tff(c_22,plain,(
    ! [A_17,C_19,B_18] :
      ( r1_xboole_0(A_17,C_19)
      | ~ r1_xboole_0(B_18,C_19)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_17740,plain,(
    ! [A_370] :
      ( r1_xboole_0(A_370,'#skF_1')
      | ~ r1_tarski(A_370,k2_xboole_0('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_16948,c_22])).

tff(c_17767,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_17740])).

tff(c_17776,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_17767,c_4])).

tff(c_17783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_17776])).

tff(c_17784,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_17804,plain,(
    r1_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_17784,c_8])).

tff(c_17942,plain,(
    ! [A_377,C_378,B_379] :
      ( r1_xboole_0(A_377,C_378)
      | ~ r1_xboole_0(B_379,C_378)
      | ~ r1_tarski(A_377,B_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_19144,plain,(
    ! [A_414] :
      ( r1_xboole_0(A_414,'#skF_1')
      | ~ r1_tarski(A_414,k2_xboole_0('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_17804,c_17942])).

tff(c_19171,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_19144])).

tff(c_19181,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_19171,c_4])).

tff(c_19188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_19181])).

tff(c_19189,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_19205,plain,(
    r1_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_19189,c_8])).

tff(c_19352,plain,(
    ! [A_425,C_426,B_427] :
      ( r1_xboole_0(A_425,C_426)
      | ~ r1_xboole_0(B_427,C_426)
      | ~ r1_tarski(A_425,B_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20186,plain,(
    ! [A_454] :
      ( r1_xboole_0(A_454,'#skF_1')
      | ~ r1_tarski(A_454,k2_xboole_0('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_19205,c_19352])).

tff(c_20213,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_20186])).

tff(c_20222,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20213,c_4])).

tff(c_20229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_20222])).

tff(c_20231,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_20276,plain,(
    ! [A_459,B_460] :
      ( r1_xboole_0(A_459,B_460)
      | k3_xboole_0(A_459,B_460) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20292,plain,(
    ! [B_461,A_462] :
      ( r1_xboole_0(B_461,A_462)
      | k3_xboole_0(A_462,B_461) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20276,c_8])).

tff(c_20230,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_20239,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20230])).

tff(c_20302,plain,(
    k3_xboole_0('#skF_3','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20292,c_20239])).

tff(c_20304,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_20310,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20304,c_4])).

tff(c_20387,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_20394,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20387,c_4])).

tff(c_20420,plain,(
    ! [A_467,B_468] : k2_xboole_0(k3_xboole_0(A_467,B_468),k4_xboole_0(A_467,B_468)) = A_467 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20438,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_6')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_20394,c_20420])).

tff(c_20563,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_20438,c_94])).

tff(c_20703,plain,(
    ! [A_482,B_483,C_484] : k4_xboole_0(k4_xboole_0(A_482,B_483),C_484) = k4_xboole_0(A_482,k2_xboole_0(B_483,C_484)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22913,plain,(
    ! [A_541,B_542,C_543] : k4_xboole_0(k4_xboole_0(A_541,B_542),k4_xboole_0(A_541,k2_xboole_0(B_542,C_543))) = k3_xboole_0(k4_xboole_0(A_541,B_542),C_543) ),
    inference(superposition,[status(thm),theory(equality)],[c_20703,c_18])).

tff(c_23017,plain,(
    ! [C_543] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_543))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_6'),C_543) ),
    inference(superposition,[status(thm),theory(equality)],[c_20563,c_22913])).

tff(c_23073,plain,(
    ! [C_543] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_543)) = k3_xboole_0('#skF_4',C_543) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20563,c_23017])).

tff(c_20388,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_20419,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_20388])).

tff(c_46319,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23073,c_20419])).

tff(c_46322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20310,c_46319])).

tff(c_46323,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_46346,plain,(
    r1_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_46323,c_8])).

tff(c_46603,plain,(
    ! [A_852,C_853,B_854] :
      ( r1_xboole_0(A_852,C_853)
      | ~ r1_xboole_0(B_854,C_853)
      | ~ r1_tarski(A_852,B_854) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48784,plain,(
    ! [A_910] :
      ( r1_xboole_0(A_910,'#skF_1')
      | ~ r1_tarski(A_910,k2_xboole_0('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_46346,c_46603])).

tff(c_48816,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_48784])).

tff(c_48832,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48816,c_4])).

tff(c_48839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20302,c_48832])).

tff(c_48840,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_48856,plain,(
    r1_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_48840,c_8])).

tff(c_49008,plain,(
    ! [A_917,C_918,B_919] :
      ( r1_xboole_0(A_917,C_918)
      | ~ r1_xboole_0(B_919,C_918)
      | ~ r1_tarski(A_917,B_919) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_51329,plain,(
    ! [A_980] :
      ( r1_xboole_0(A_980,'#skF_1')
      | ~ r1_tarski(A_980,k2_xboole_0('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48856,c_49008])).

tff(c_51362,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_51329])).

tff(c_51367,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51362,c_4])).

tff(c_51374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20302,c_51367])).

tff(c_51375,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_51391,plain,(
    r1_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_51375,c_8])).

tff(c_51539,plain,(
    ! [A_989,C_990,B_991] :
      ( r1_xboole_0(A_989,C_990)
      | ~ r1_xboole_0(B_991,C_990)
      | ~ r1_tarski(A_989,B_991) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52672,plain,(
    ! [A_1032] :
      ( r1_xboole_0(A_1032,'#skF_1')
      | ~ r1_tarski(A_1032,k2_xboole_0('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_51391,c_51539])).

tff(c_52705,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_52672])).

tff(c_52710,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52705,c_4])).

tff(c_52717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20302,c_52710])).

tff(c_52719,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20230])).

tff(c_36,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_82492,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20231,c_52719,c_40])).

tff(c_52718,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_20230])).

tff(c_52734,plain,(
    ! [A_1033,B_1034] :
      ( k3_xboole_0(A_1033,B_1034) = k1_xboole_0
      | ~ r1_xboole_0(A_1033,B_1034) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52756,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52718,c_52734])).

tff(c_32,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52769,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20231,c_52719,c_32])).

tff(c_52775,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52769,c_4])).

tff(c_52846,plain,(
    ! [A_1041,B_1042] : k2_xboole_0(k3_xboole_0(A_1041,B_1042),k4_xboole_0(A_1041,B_1042)) = A_1041 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52876,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_5')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_52775,c_52846])).

tff(c_53023,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_52876,c_94])).

tff(c_53175,plain,(
    ! [A_1058,B_1059,C_1060] : k4_xboole_0(k4_xboole_0(A_1058,B_1059),C_1060) = k4_xboole_0(A_1058,k2_xboole_0(B_1059,C_1060)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54995,plain,(
    ! [A_1110,B_1111,C_1112] : k4_xboole_0(k4_xboole_0(A_1110,B_1111),k4_xboole_0(A_1110,k2_xboole_0(B_1111,C_1112))) = k3_xboole_0(k4_xboole_0(A_1110,B_1111),C_1112) ),
    inference(superposition,[status(thm),theory(equality)],[c_53175,c_18])).

tff(c_73664,plain,(
    ! [A_1384,B_1385,A_1386] : k4_xboole_0(k4_xboole_0(A_1384,B_1385),k4_xboole_0(A_1384,k2_xboole_0(A_1386,B_1385))) = k3_xboole_0(k4_xboole_0(A_1384,B_1385),A_1386) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_54995])).

tff(c_73918,plain,(
    ! [A_1386] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0(A_1386,'#skF_5'))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_5'),A_1386) ),
    inference(superposition,[status(thm),theory(equality)],[c_53023,c_73664])).

tff(c_74008,plain,(
    ! [A_1386] : k3_xboole_0('#skF_4',k2_xboole_0(A_1386,'#skF_5')) = k3_xboole_0('#skF_4',A_1386) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_53023,c_73918])).

tff(c_53133,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_53141,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_53133])).

tff(c_82475,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74008,c_53141])).

tff(c_82478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52756,c_82475])).

tff(c_82480,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_82501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82492,c_82480])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.14/9.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.14/9.68  
% 17.14/9.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.14/9.68  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 17.14/9.68  
% 17.14/9.68  %Foreground sorts:
% 17.14/9.68  
% 17.14/9.68  
% 17.14/9.68  %Background operators:
% 17.14/9.68  
% 17.14/9.68  
% 17.14/9.68  %Foreground operators:
% 17.14/9.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.14/9.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.14/9.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.14/9.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.14/9.68  tff('#skF_5', type, '#skF_5': $i).
% 17.14/9.68  tff('#skF_6', type, '#skF_6': $i).
% 17.14/9.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.14/9.68  tff('#skF_2', type, '#skF_2': $i).
% 17.14/9.68  tff('#skF_3', type, '#skF_3': $i).
% 17.14/9.68  tff('#skF_1', type, '#skF_1': $i).
% 17.14/9.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.14/9.68  tff('#skF_4', type, '#skF_4': $i).
% 17.14/9.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.14/9.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.14/9.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.14/9.68  
% 17.25/9.70  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 17.25/9.70  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 17.25/9.70  tff(f_72, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 17.25/9.70  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 17.25/9.70  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 17.25/9.70  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 17.25/9.70  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 17.25/9.70  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 17.25/9.70  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 17.25/9.70  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 17.25/9.70  tff(c_189, plain, (![A_38, B_39]: (r1_xboole_0(A_38, B_39) | k3_xboole_0(A_38, B_39)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.25/9.70  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.25/9.70  tff(c_201, plain, (![B_40, A_41]: (r1_xboole_0(B_40, A_41) | k3_xboole_0(A_41, B_40)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_189, c_8])).
% 17.25/9.70  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.25/9.70  tff(c_166, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 17.25/9.70  tff(c_211, plain, (k3_xboole_0('#skF_2', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_201, c_166])).
% 17.25/9.70  tff(c_72, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.25/9.70  tff(c_24, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.25/9.70  tff(c_87, plain, (![A_31, B_30]: (r1_tarski(A_31, k2_xboole_0(B_30, A_31)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_24])).
% 17.25/9.70  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.25/9.70  tff(c_30, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.25/9.70  tff(c_38, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 17.25/9.70  tff(c_213, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_38])).
% 17.25/9.70  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.25/9.70  tff(c_219, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_213, c_4])).
% 17.25/9.70  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.25/9.70  tff(c_26, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.25/9.70  tff(c_39, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 17.25/9.70  tff(c_292, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_39])).
% 17.25/9.70  tff(c_298, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_292, c_4])).
% 17.25/9.70  tff(c_320, plain, (![A_46, B_47]: (k2_xboole_0(k3_xboole_0(A_46, B_47), k4_xboole_0(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.25/9.70  tff(c_341, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_6'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_298, c_320])).
% 17.25/9.70  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.25/9.70  tff(c_94, plain, (![A_31]: (k2_xboole_0(k1_xboole_0, A_31)=A_31)), inference(superposition, [status(thm), theory('equality')], [c_72, c_10])).
% 17.25/9.70  tff(c_410, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_341, c_94])).
% 17.25/9.70  tff(c_561, plain, (![A_60, B_61, C_62]: (k4_xboole_0(k4_xboole_0(A_60, B_61), C_62)=k4_xboole_0(A_60, k2_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.25/9.70  tff(c_3333, plain, (![A_135, B_136, C_137]: (k4_xboole_0(k4_xboole_0(A_135, B_136), k4_xboole_0(A_135, k2_xboole_0(B_136, C_137)))=k3_xboole_0(k4_xboole_0(A_135, B_136), C_137))), inference(superposition, [status(thm), theory('equality')], [c_561, c_18])).
% 17.25/9.70  tff(c_3428, plain, (![C_137]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_137)))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), C_137))), inference(superposition, [status(thm), theory('equality')], [c_410, c_3333])).
% 17.25/9.70  tff(c_3479, plain, (![C_137]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_137))=k3_xboole_0('#skF_4', C_137))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_410, c_3428])).
% 17.25/9.70  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.25/9.70  tff(c_34, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.25/9.70  tff(c_37, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_34])).
% 17.25/9.70  tff(c_422, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_37])).
% 17.25/9.70  tff(c_449, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_422])).
% 17.25/9.70  tff(c_16910, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3479, c_449])).
% 17.25/9.70  tff(c_16913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_219, c_16910])).
% 17.25/9.70  tff(c_16914, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_37])).
% 17.25/9.70  tff(c_16948, plain, (r1_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_16914, c_8])).
% 17.25/9.70  tff(c_22, plain, (![A_17, C_19, B_18]: (r1_xboole_0(A_17, C_19) | ~r1_xboole_0(B_18, C_19) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.25/9.70  tff(c_17740, plain, (![A_370]: (r1_xboole_0(A_370, '#skF_1') | ~r1_tarski(A_370, k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_16948, c_22])).
% 17.25/9.70  tff(c_17767, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_87, c_17740])).
% 17.25/9.70  tff(c_17776, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_17767, c_4])).
% 17.25/9.70  tff(c_17783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_17776])).
% 17.25/9.70  tff(c_17784, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_39])).
% 17.25/9.70  tff(c_17804, plain, (r1_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_17784, c_8])).
% 17.25/9.70  tff(c_17942, plain, (![A_377, C_378, B_379]: (r1_xboole_0(A_377, C_378) | ~r1_xboole_0(B_379, C_378) | ~r1_tarski(A_377, B_379))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.25/9.70  tff(c_19144, plain, (![A_414]: (r1_xboole_0(A_414, '#skF_1') | ~r1_tarski(A_414, k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_17804, c_17942])).
% 17.25/9.70  tff(c_19171, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_87, c_19144])).
% 17.25/9.70  tff(c_19181, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_19171, c_4])).
% 17.25/9.70  tff(c_19188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_19181])).
% 17.25/9.70  tff(c_19189, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 17.25/9.70  tff(c_19205, plain, (r1_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_19189, c_8])).
% 17.25/9.70  tff(c_19352, plain, (![A_425, C_426, B_427]: (r1_xboole_0(A_425, C_426) | ~r1_xboole_0(B_427, C_426) | ~r1_tarski(A_425, B_427))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.25/9.70  tff(c_20186, plain, (![A_454]: (r1_xboole_0(A_454, '#skF_1') | ~r1_tarski(A_454, k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_19205, c_19352])).
% 17.25/9.70  tff(c_20213, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_87, c_20186])).
% 17.25/9.70  tff(c_20222, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_20213, c_4])).
% 17.25/9.70  tff(c_20229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_20222])).
% 17.25/9.70  tff(c_20231, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 17.25/9.70  tff(c_20276, plain, (![A_459, B_460]: (r1_xboole_0(A_459, B_460) | k3_xboole_0(A_459, B_460)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.25/9.70  tff(c_20292, plain, (![B_461, A_462]: (r1_xboole_0(B_461, A_462) | k3_xboole_0(A_462, B_461)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20276, c_8])).
% 17.25/9.70  tff(c_20230, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_28])).
% 17.25/9.70  tff(c_20239, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_20230])).
% 17.25/9.70  tff(c_20302, plain, (k3_xboole_0('#skF_3', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_20292, c_20239])).
% 17.25/9.70  tff(c_20304, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_38])).
% 17.25/9.70  tff(c_20310, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_20304, c_4])).
% 17.25/9.70  tff(c_20387, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_39])).
% 17.25/9.70  tff(c_20394, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_20387, c_4])).
% 17.25/9.70  tff(c_20420, plain, (![A_467, B_468]: (k2_xboole_0(k3_xboole_0(A_467, B_468), k4_xboole_0(A_467, B_468))=A_467)), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.25/9.70  tff(c_20438, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_6'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_20394, c_20420])).
% 17.25/9.70  tff(c_20563, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_20438, c_94])).
% 17.25/9.70  tff(c_20703, plain, (![A_482, B_483, C_484]: (k4_xboole_0(k4_xboole_0(A_482, B_483), C_484)=k4_xboole_0(A_482, k2_xboole_0(B_483, C_484)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.25/9.70  tff(c_22913, plain, (![A_541, B_542, C_543]: (k4_xboole_0(k4_xboole_0(A_541, B_542), k4_xboole_0(A_541, k2_xboole_0(B_542, C_543)))=k3_xboole_0(k4_xboole_0(A_541, B_542), C_543))), inference(superposition, [status(thm), theory('equality')], [c_20703, c_18])).
% 17.25/9.70  tff(c_23017, plain, (![C_543]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_543)))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), C_543))), inference(superposition, [status(thm), theory('equality')], [c_20563, c_22913])).
% 17.25/9.70  tff(c_23073, plain, (![C_543]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_543))=k3_xboole_0('#skF_4', C_543))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20563, c_23017])).
% 17.25/9.70  tff(c_20388, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_37])).
% 17.25/9.70  tff(c_20419, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_20388])).
% 17.25/9.70  tff(c_46319, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_23073, c_20419])).
% 17.25/9.70  tff(c_46322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20310, c_46319])).
% 17.25/9.70  tff(c_46323, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_37])).
% 17.25/9.70  tff(c_46346, plain, (r1_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_46323, c_8])).
% 17.25/9.70  tff(c_46603, plain, (![A_852, C_853, B_854]: (r1_xboole_0(A_852, C_853) | ~r1_xboole_0(B_854, C_853) | ~r1_tarski(A_852, B_854))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.25/9.70  tff(c_48784, plain, (![A_910]: (r1_xboole_0(A_910, '#skF_1') | ~r1_tarski(A_910, k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_46346, c_46603])).
% 17.25/9.70  tff(c_48816, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_48784])).
% 17.25/9.70  tff(c_48832, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_48816, c_4])).
% 17.25/9.70  tff(c_48839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20302, c_48832])).
% 17.25/9.70  tff(c_48840, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_39])).
% 17.25/9.70  tff(c_48856, plain, (r1_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_48840, c_8])).
% 17.25/9.70  tff(c_49008, plain, (![A_917, C_918, B_919]: (r1_xboole_0(A_917, C_918) | ~r1_xboole_0(B_919, C_918) | ~r1_tarski(A_917, B_919))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.25/9.70  tff(c_51329, plain, (![A_980]: (r1_xboole_0(A_980, '#skF_1') | ~r1_tarski(A_980, k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_48856, c_49008])).
% 17.25/9.70  tff(c_51362, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_51329])).
% 17.25/9.70  tff(c_51367, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_51362, c_4])).
% 17.25/9.70  tff(c_51374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20302, c_51367])).
% 17.25/9.70  tff(c_51375, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 17.25/9.70  tff(c_51391, plain, (r1_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_51375, c_8])).
% 17.25/9.70  tff(c_51539, plain, (![A_989, C_990, B_991]: (r1_xboole_0(A_989, C_990) | ~r1_xboole_0(B_991, C_990) | ~r1_tarski(A_989, B_991))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.25/9.70  tff(c_52672, plain, (![A_1032]: (r1_xboole_0(A_1032, '#skF_1') | ~r1_tarski(A_1032, k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_51391, c_51539])).
% 17.25/9.70  tff(c_52705, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_52672])).
% 17.25/9.70  tff(c_52710, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_52705, c_4])).
% 17.25/9.70  tff(c_52717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20302, c_52710])).
% 17.25/9.70  tff(c_52719, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_20230])).
% 17.25/9.70  tff(c_36, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.25/9.70  tff(c_40, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 17.25/9.70  tff(c_82492, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_20231, c_52719, c_40])).
% 17.25/9.70  tff(c_52718, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_20230])).
% 17.25/9.70  tff(c_52734, plain, (![A_1033, B_1034]: (k3_xboole_0(A_1033, B_1034)=k1_xboole_0 | ~r1_xboole_0(A_1033, B_1034))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.25/9.70  tff(c_52756, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_52718, c_52734])).
% 17.25/9.70  tff(c_32, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.25/9.70  tff(c_52769, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20231, c_52719, c_32])).
% 17.25/9.70  tff(c_52775, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_52769, c_4])).
% 17.25/9.70  tff(c_52846, plain, (![A_1041, B_1042]: (k2_xboole_0(k3_xboole_0(A_1041, B_1042), k4_xboole_0(A_1041, B_1042))=A_1041)), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.25/9.70  tff(c_52876, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_5'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_52775, c_52846])).
% 17.25/9.70  tff(c_53023, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_52876, c_94])).
% 17.25/9.70  tff(c_53175, plain, (![A_1058, B_1059, C_1060]: (k4_xboole_0(k4_xboole_0(A_1058, B_1059), C_1060)=k4_xboole_0(A_1058, k2_xboole_0(B_1059, C_1060)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.25/9.70  tff(c_54995, plain, (![A_1110, B_1111, C_1112]: (k4_xboole_0(k4_xboole_0(A_1110, B_1111), k4_xboole_0(A_1110, k2_xboole_0(B_1111, C_1112)))=k3_xboole_0(k4_xboole_0(A_1110, B_1111), C_1112))), inference(superposition, [status(thm), theory('equality')], [c_53175, c_18])).
% 17.25/9.70  tff(c_73664, plain, (![A_1384, B_1385, A_1386]: (k4_xboole_0(k4_xboole_0(A_1384, B_1385), k4_xboole_0(A_1384, k2_xboole_0(A_1386, B_1385)))=k3_xboole_0(k4_xboole_0(A_1384, B_1385), A_1386))), inference(superposition, [status(thm), theory('equality')], [c_2, c_54995])).
% 17.25/9.70  tff(c_73918, plain, (![A_1386]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0(A_1386, '#skF_5')))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), A_1386))), inference(superposition, [status(thm), theory('equality')], [c_53023, c_73664])).
% 17.25/9.70  tff(c_74008, plain, (![A_1386]: (k3_xboole_0('#skF_4', k2_xboole_0(A_1386, '#skF_5'))=k3_xboole_0('#skF_4', A_1386))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_53023, c_73918])).
% 17.25/9.70  tff(c_53133, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_37])).
% 17.25/9.70  tff(c_53141, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_53133])).
% 17.25/9.71  tff(c_82475, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74008, c_53141])).
% 17.25/9.71  tff(c_82478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52756, c_82475])).
% 17.25/9.71  tff(c_82480, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_37])).
% 17.25/9.71  tff(c_82501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82492, c_82480])).
% 17.25/9.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.25/9.71  
% 17.25/9.71  Inference rules
% 17.25/9.71  ----------------------
% 17.25/9.71  #Ref     : 0
% 17.25/9.71  #Sup     : 20971
% 17.25/9.71  #Fact    : 0
% 17.25/9.71  #Define  : 0
% 17.25/9.71  #Split   : 23
% 17.25/9.71  #Chain   : 0
% 17.25/9.71  #Close   : 0
% 17.25/9.71  
% 17.25/9.71  Ordering : KBO
% 17.25/9.71  
% 17.25/9.71  Simplification rules
% 17.25/9.71  ----------------------
% 17.25/9.71  #Subsume      : 961
% 17.25/9.71  #Demod        : 21341
% 17.25/9.71  #Tautology    : 13350
% 17.25/9.71  #SimpNegUnit  : 7
% 17.25/9.71  #BackRed      : 114
% 17.25/9.71  
% 17.25/9.71  #Partial instantiations: 0
% 17.25/9.71  #Strategies tried      : 1
% 17.25/9.71  
% 17.25/9.71  Timing (in seconds)
% 17.25/9.71  ----------------------
% 17.25/9.71  Preprocessing        : 0.29
% 17.25/9.71  Parsing              : 0.16
% 17.25/9.71  CNF conversion       : 0.02
% 17.25/9.71  Main loop            : 8.64
% 17.25/9.71  Inferencing          : 1.59
% 17.25/9.71  Reduction            : 4.84
% 17.25/9.71  Demodulation         : 4.18
% 17.25/9.71  BG Simplification    : 0.18
% 17.25/9.71  Subsumption          : 1.56
% 17.25/9.71  Abstraction          : 0.26
% 17.25/9.71  MUC search           : 0.00
% 17.25/9.71  Cooper               : 0.00
% 17.25/9.71  Total                : 8.97
% 17.25/9.71  Index Insertion      : 0.00
% 17.25/9.71  Index Deletion       : 0.00
% 17.25/9.71  Index Matching       : 0.00
% 17.25/9.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
