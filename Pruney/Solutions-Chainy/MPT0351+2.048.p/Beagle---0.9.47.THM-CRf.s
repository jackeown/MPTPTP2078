%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:43 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 173 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 248 expanded)
%              Number of equality atoms :   48 ( 114 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_10,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_27,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_24])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k3_subset_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( k4_subset_1(A_22,B_23,k3_subset_1(A_22,B_23)) = k2_subset_1(A_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_283,plain,(
    ! [A_45,B_46] :
      ( k4_subset_1(A_45,B_46,k3_subset_1(A_45,B_46)) = A_45
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_289,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_283])).

tff(c_466,plain,(
    ! [A_56,B_57,C_58] :
      ( m1_subset_1(k4_subset_1(A_56,B_57,C_58),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_485,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_466])).

tff(c_495,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_485])).

tff(c_813,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_495])).

tff(c_816,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_813])).

tff(c_820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_816])).

tff(c_821,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_495])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_119,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k3_subset_1(A_35,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_123,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_119])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_4])).

tff(c_136,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_6])).

tff(c_111,plain,(
    ! [A_33,B_34] :
      ( k3_subset_1(A_33,k3_subset_1(A_33,B_34)) = B_34
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_114,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_111])).

tff(c_176,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k3_subset_1(A_37,B_38),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k3_subset_1(A_10,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_559,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,k3_subset_1(A_63,B_64)) = k3_subset_1(A_63,k3_subset_1(A_63,B_64))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_176,c_12])).

tff(c_565,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_559])).

tff(c_569,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_114,c_565])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_98,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_107,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_98])).

tff(c_372,plain,(
    ! [A_51,B_52] : k2_xboole_0(k4_xboole_0(A_51,B_52),k3_xboole_0(A_51,B_52)) = k2_xboole_0(A_51,k4_xboole_0(A_51,B_52)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_378,plain,(
    ! [A_51,B_52] : k2_xboole_0(k3_xboole_0(A_51,B_52),k4_xboole_0(A_51,B_52)) = k2_xboole_0(A_51,k4_xboole_0(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_2])).

tff(c_407,plain,(
    ! [A_51,B_52] : k2_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_378])).

tff(c_110,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_417,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_110])).

tff(c_581,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_417])).

tff(c_599,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_2,c_123,c_581])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k3_subset_1(A_17,k3_subset_1(A_17,B_18)) = B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_843,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_1')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_821,c_18])).

tff(c_335,plain,(
    ! [A_47,B_48,C_49] :
      ( k4_subset_1(A_47,B_48,C_49) = k2_xboole_0(B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_904,plain,(
    ! [A_69,B_70,B_71] :
      ( k4_subset_1(A_69,B_70,k3_subset_1(A_69,B_71)) = k2_xboole_0(B_70,k3_subset_1(A_69,B_71))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_69)) ) ),
    inference(resolution,[status(thm)],[c_14,c_335])).

tff(c_956,plain,(
    ! [B_72] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_72)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_904])).

tff(c_1395,plain,(
    ! [B_83] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',k3_subset_1('#skF_1',B_83))) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',k3_subset_1('#skF_1',B_83)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_956])).

tff(c_1427,plain,
    ( k2_xboole_0('#skF_2',k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_1'))) = k4_subset_1('#skF_1','#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_1395])).

tff(c_1454,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_599,c_2,c_843,c_1427])).

tff(c_1456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_1454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.57  
% 3.26/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.58  %$ m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.26/1.58  
% 3.26/1.58  %Foreground sorts:
% 3.26/1.58  
% 3.26/1.58  
% 3.26/1.58  %Background operators:
% 3.26/1.58  
% 3.26/1.58  
% 3.26/1.58  %Foreground operators:
% 3.26/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.26/1.58  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.26/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.58  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.26/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.58  
% 3.26/1.59  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.26/1.59  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 3.26/1.59  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.26/1.59  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 3.26/1.59  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 3.26/1.59  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.26/1.59  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.26/1.59  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.26/1.59  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.26/1.59  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.26/1.59  tff(f_33, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.26/1.59  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.26/1.59  tff(c_10, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.59  tff(c_24, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.26/1.59  tff(c_27, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_24])).
% 3.26/1.59  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.26/1.59  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(k3_subset_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.59  tff(c_22, plain, (![A_22, B_23]: (k4_subset_1(A_22, B_23, k3_subset_1(A_22, B_23))=k2_subset_1(A_22) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.26/1.59  tff(c_283, plain, (![A_45, B_46]: (k4_subset_1(A_45, B_46, k3_subset_1(A_45, B_46))=A_45 | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 3.26/1.59  tff(c_289, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_26, c_283])).
% 3.26/1.59  tff(c_466, plain, (![A_56, B_57, C_58]: (m1_subset_1(k4_subset_1(A_56, B_57, C_58), k1_zfmisc_1(A_56)) | ~m1_subset_1(C_58, k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.26/1.59  tff(c_485, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_289, c_466])).
% 3.26/1.59  tff(c_495, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_485])).
% 3.26/1.59  tff(c_813, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_495])).
% 3.26/1.59  tff(c_816, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_813])).
% 3.26/1.59  tff(c_820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_816])).
% 3.26/1.59  tff(c_821, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_495])).
% 3.26/1.59  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.59  tff(c_119, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k3_subset_1(A_35, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.59  tff(c_123, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_119])).
% 3.26/1.59  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.59  tff(c_127, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_123, c_4])).
% 3.26/1.59  tff(c_136, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_127])).
% 3.26/1.59  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.59  tff(c_130, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_123, c_6])).
% 3.26/1.59  tff(c_111, plain, (![A_33, B_34]: (k3_subset_1(A_33, k3_subset_1(A_33, B_34))=B_34 | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.26/1.59  tff(c_114, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_111])).
% 3.26/1.59  tff(c_176, plain, (![A_37, B_38]: (m1_subset_1(k3_subset_1(A_37, B_38), k1_zfmisc_1(A_37)) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.59  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k3_subset_1(A_10, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.59  tff(c_559, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k3_subset_1(A_63, B_64))=k3_subset_1(A_63, k3_subset_1(A_63, B_64)) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(resolution, [status(thm)], [c_176, c_12])).
% 3.26/1.59  tff(c_565, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_559])).
% 3.26/1.59  tff(c_569, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_114, c_565])).
% 3.26/1.59  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.59  tff(c_98, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.59  tff(c_107, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=k2_xboole_0(k4_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_98])).
% 3.26/1.59  tff(c_372, plain, (![A_51, B_52]: (k2_xboole_0(k4_xboole_0(A_51, B_52), k3_xboole_0(A_51, B_52))=k2_xboole_0(A_51, k4_xboole_0(A_51, B_52)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_107])).
% 3.26/1.59  tff(c_378, plain, (![A_51, B_52]: (k2_xboole_0(k3_xboole_0(A_51, B_52), k4_xboole_0(A_51, B_52))=k2_xboole_0(A_51, k4_xboole_0(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_372, c_2])).
% 3.26/1.59  tff(c_407, plain, (![A_51, B_52]: (k2_xboole_0(A_51, k4_xboole_0(A_51, B_52))=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_378])).
% 3.26/1.59  tff(c_110, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=k2_xboole_0(A_5, k4_xboole_0(A_5, B_6)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_107])).
% 3.26/1.59  tff(c_417, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_407, c_110])).
% 3.26/1.59  tff(c_581, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_569, c_417])).
% 3.26/1.59  tff(c_599, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_2, c_123, c_581])).
% 3.26/1.59  tff(c_18, plain, (![A_17, B_18]: (k3_subset_1(A_17, k3_subset_1(A_17, B_18))=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.26/1.59  tff(c_843, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_1'))='#skF_1'), inference(resolution, [status(thm)], [c_821, c_18])).
% 3.26/1.59  tff(c_335, plain, (![A_47, B_48, C_49]: (k4_subset_1(A_47, B_48, C_49)=k2_xboole_0(B_48, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.26/1.59  tff(c_904, plain, (![A_69, B_70, B_71]: (k4_subset_1(A_69, B_70, k3_subset_1(A_69, B_71))=k2_xboole_0(B_70, k3_subset_1(A_69, B_71)) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)) | ~m1_subset_1(B_71, k1_zfmisc_1(A_69)))), inference(resolution, [status(thm)], [c_14, c_335])).
% 3.26/1.59  tff(c_956, plain, (![B_72]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_72))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_904])).
% 3.26/1.59  tff(c_1395, plain, (![B_83]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', k3_subset_1('#skF_1', B_83)))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', k3_subset_1('#skF_1', B_83))) | ~m1_subset_1(B_83, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_956])).
% 3.26/1.59  tff(c_1427, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_1')))=k4_subset_1('#skF_1', '#skF_2', '#skF_1') | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_843, c_1395])).
% 3.26/1.59  tff(c_1454, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_821, c_599, c_2, c_843, c_1427])).
% 3.26/1.59  tff(c_1456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27, c_1454])).
% 3.26/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.59  
% 3.26/1.59  Inference rules
% 3.26/1.59  ----------------------
% 3.26/1.59  #Ref     : 0
% 3.26/1.59  #Sup     : 382
% 3.26/1.59  #Fact    : 0
% 3.26/1.59  #Define  : 0
% 3.26/1.59  #Split   : 1
% 3.26/1.59  #Chain   : 0
% 3.26/1.59  #Close   : 0
% 3.26/1.59  
% 3.26/1.59  Ordering : KBO
% 3.26/1.59  
% 3.26/1.59  Simplification rules
% 3.26/1.59  ----------------------
% 3.26/1.59  #Subsume      : 4
% 3.26/1.59  #Demod        : 356
% 3.26/1.59  #Tautology    : 261
% 3.26/1.59  #SimpNegUnit  : 1
% 3.26/1.59  #BackRed      : 15
% 3.26/1.59  
% 3.26/1.59  #Partial instantiations: 0
% 3.26/1.59  #Strategies tried      : 1
% 3.26/1.59  
% 3.26/1.59  Timing (in seconds)
% 3.26/1.59  ----------------------
% 3.26/1.59  Preprocessing        : 0.29
% 3.26/1.59  Parsing              : 0.16
% 3.26/1.59  CNF conversion       : 0.02
% 3.26/1.59  Main loop            : 0.48
% 3.26/1.59  Inferencing          : 0.16
% 3.26/1.59  Reduction            : 0.19
% 3.26/1.59  Demodulation         : 0.15
% 3.26/1.59  BG Simplification    : 0.02
% 3.26/1.59  Subsumption          : 0.08
% 3.26/1.59  Abstraction          : 0.03
% 3.26/1.59  MUC search           : 0.00
% 3.26/1.59  Cooper               : 0.00
% 3.26/1.59  Total                : 0.81
% 3.26/1.59  Index Insertion      : 0.00
% 3.26/1.59  Index Deletion       : 0.00
% 3.26/1.59  Index Matching       : 0.00
% 3.26/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
