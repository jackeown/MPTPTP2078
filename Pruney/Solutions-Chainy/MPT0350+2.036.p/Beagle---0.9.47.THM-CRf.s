%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:30 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 127 expanded)
%              Number of leaves         :   32 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :   80 ( 142 expanded)
%              Number of equality atoms :   53 (  90 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_16,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_37,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_192,plain,(
    ! [A_46,B_47] :
      ( k3_subset_1(A_46,k3_subset_1(A_46,B_47)) = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_199,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_192])).

tff(c_587,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k3_subset_1(A_61,B_62),k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k3_subset_1(A_16,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3472,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(A_115,k3_subset_1(A_115,B_116)) = k3_subset_1(A_115,k3_subset_1(A_115,B_116))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(resolution,[status(thm)],[c_587,c_18])).

tff(c_3476,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_3472])).

tff(c_3483,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_3476])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_14] : k1_subset_1(A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_26] : k3_subset_1(A_26,k1_subset_1(A_26)) = k2_subset_1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    ! [A_26] : k3_subset_1(A_26,k1_subset_1(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_28])).

tff(c_38,plain,(
    ! [A_26] : k3_subset_1(A_26,k1_xboole_0) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_30,plain,(
    ! [A_27] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_196,plain,(
    ! [A_27] : k3_subset_1(A_27,k3_subset_1(A_27,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_192])).

tff(c_201,plain,(
    ! [A_27] : k3_subset_1(A_27,A_27) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_196])).

tff(c_20,plain,(
    ! [A_18] : m1_subset_1(k2_subset_1(A_18),k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35,plain,(
    ! [A_18] : m1_subset_1(A_18,k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_135,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = k3_subset_1(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_subset_1(A_18,A_18) ),
    inference(resolution,[status(thm)],[c_35,c_135])).

tff(c_221,plain,(
    ! [A_49] : k4_xboole_0(A_49,A_49) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_148])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_233,plain,(
    ! [A_49] : k5_xboole_0(A_49,k1_xboole_0) = k2_xboole_0(A_49,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_10])).

tff(c_243,plain,(
    ! [A_49] : k5_xboole_0(A_49,k1_xboole_0) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_233])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_203,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_148])).

tff(c_360,plain,(
    ! [A_53,B_54,C_55] : k4_xboole_0(k4_xboole_0(A_53,B_54),C_55) = k4_xboole_0(A_53,k2_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_396,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k2_xboole_0(B_54,k4_xboole_0(A_53,B_54))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_360])).

tff(c_410,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k2_xboole_0(B_54,A_53)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_396])).

tff(c_1544,plain,(
    ! [C_88,A_89,B_90] : k5_xboole_0(C_88,k4_xboole_0(A_89,k2_xboole_0(B_90,C_88))) = k2_xboole_0(C_88,k4_xboole_0(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_10])).

tff(c_1591,plain,(
    ! [A_53,B_54] : k2_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k5_xboole_0(A_53,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_1544])).

tff(c_1639,plain,(
    ! [A_53,B_54] : k2_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_1591])).

tff(c_3497,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3483,c_1639])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_145,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_135])).

tff(c_282,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_6])).

tff(c_288,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_282])).

tff(c_3524,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3497,c_288])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k3_subset_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_897,plain,(
    ! [A_69,B_70,C_71] :
      ( k4_subset_1(A_69,B_70,C_71) = k2_xboole_0(B_70,C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(A_69))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4993,plain,(
    ! [A_127,B_128,B_129] :
      ( k4_subset_1(A_127,B_128,k3_subset_1(A_127,B_129)) = k2_xboole_0(B_128,k3_subset_1(A_127,B_129))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_127))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_127)) ) ),
    inference(resolution,[status(thm)],[c_22,c_897])).

tff(c_5010,plain,(
    ! [B_130] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_130)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_130))
      | ~ m1_subset_1(B_130,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_34,c_4993])).

tff(c_5017,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_5010])).

tff(c_5028,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3524,c_5017])).

tff(c_5030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_5028])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.57/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/1.89  
% 4.57/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/1.90  %$ m1_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.57/1.90  
% 4.57/1.90  %Foreground sorts:
% 4.57/1.90  
% 4.57/1.90  
% 4.57/1.90  %Background operators:
% 4.57/1.90  
% 4.57/1.90  
% 4.57/1.90  %Foreground operators:
% 4.57/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.57/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.57/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.57/1.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.57/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.57/1.90  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.57/1.90  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.57/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.57/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.57/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.57/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.57/1.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.57/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.57/1.90  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.57/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.57/1.90  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.57/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.57/1.90  
% 4.57/1.91  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.57/1.91  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 4.57/1.91  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.57/1.91  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.57/1.91  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.57/1.91  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.57/1.91  tff(f_39, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 4.57/1.91  tff(f_63, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 4.57/1.91  tff(f_65, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.57/1.91  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.57/1.91  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.57/1.91  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.57/1.91  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.57/1.91  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.57/1.91  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.57/1.91  tff(c_16, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.57/1.91  tff(c_32, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.57/1.91  tff(c_37, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32])).
% 4.57/1.91  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.57/1.91  tff(c_192, plain, (![A_46, B_47]: (k3_subset_1(A_46, k3_subset_1(A_46, B_47))=B_47 | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.57/1.91  tff(c_199, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_34, c_192])).
% 4.57/1.91  tff(c_587, plain, (![A_61, B_62]: (m1_subset_1(k3_subset_1(A_61, B_62), k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.57/1.91  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k3_subset_1(A_16, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.57/1.91  tff(c_3472, plain, (![A_115, B_116]: (k4_xboole_0(A_115, k3_subset_1(A_115, B_116))=k3_subset_1(A_115, k3_subset_1(A_115, B_116)) | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(resolution, [status(thm)], [c_587, c_18])).
% 4.57/1.91  tff(c_3476, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_3472])).
% 4.57/1.91  tff(c_3483, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_199, c_3476])).
% 4.57/1.91  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.57/1.91  tff(c_14, plain, (![A_14]: (k1_subset_1(A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.57/1.91  tff(c_28, plain, (![A_26]: (k3_subset_1(A_26, k1_subset_1(A_26))=k2_subset_1(A_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.57/1.91  tff(c_36, plain, (![A_26]: (k3_subset_1(A_26, k1_subset_1(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_28])).
% 4.57/1.91  tff(c_38, plain, (![A_26]: (k3_subset_1(A_26, k1_xboole_0)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 4.57/1.91  tff(c_30, plain, (![A_27]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.57/1.91  tff(c_196, plain, (![A_27]: (k3_subset_1(A_27, k3_subset_1(A_27, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_192])).
% 4.57/1.91  tff(c_201, plain, (![A_27]: (k3_subset_1(A_27, A_27)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_196])).
% 4.57/1.91  tff(c_20, plain, (![A_18]: (m1_subset_1(k2_subset_1(A_18), k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.57/1.91  tff(c_35, plain, (![A_18]: (m1_subset_1(A_18, k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 4.57/1.91  tff(c_135, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=k3_subset_1(A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.57/1.91  tff(c_148, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_subset_1(A_18, A_18))), inference(resolution, [status(thm)], [c_35, c_135])).
% 4.57/1.91  tff(c_221, plain, (![A_49]: (k4_xboole_0(A_49, A_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_201, c_148])).
% 4.57/1.91  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.57/1.91  tff(c_233, plain, (![A_49]: (k5_xboole_0(A_49, k1_xboole_0)=k2_xboole_0(A_49, A_49))), inference(superposition, [status(thm), theory('equality')], [c_221, c_10])).
% 4.57/1.91  tff(c_243, plain, (![A_49]: (k5_xboole_0(A_49, k1_xboole_0)=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_233])).
% 4.57/1.91  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.57/1.91  tff(c_203, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_201, c_148])).
% 4.57/1.91  tff(c_360, plain, (![A_53, B_54, C_55]: (k4_xboole_0(k4_xboole_0(A_53, B_54), C_55)=k4_xboole_0(A_53, k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.57/1.91  tff(c_396, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k2_xboole_0(B_54, k4_xboole_0(A_53, B_54)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_203, c_360])).
% 4.57/1.91  tff(c_410, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k2_xboole_0(B_54, A_53))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_396])).
% 4.57/1.91  tff(c_1544, plain, (![C_88, A_89, B_90]: (k5_xboole_0(C_88, k4_xboole_0(A_89, k2_xboole_0(B_90, C_88)))=k2_xboole_0(C_88, k4_xboole_0(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_360, c_10])).
% 4.57/1.91  tff(c_1591, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k5_xboole_0(A_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_410, c_1544])).
% 4.57/1.91  tff(c_1639, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k4_xboole_0(A_53, B_54))=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_243, c_1591])).
% 4.57/1.91  tff(c_3497, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3483, c_1639])).
% 4.57/1.91  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.57/1.91  tff(c_145, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_135])).
% 4.57/1.91  tff(c_282, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_145, c_6])).
% 4.57/1.91  tff(c_288, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_282])).
% 4.57/1.91  tff(c_3524, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3497, c_288])).
% 4.57/1.91  tff(c_22, plain, (![A_19, B_20]: (m1_subset_1(k3_subset_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.57/1.91  tff(c_897, plain, (![A_69, B_70, C_71]: (k4_subset_1(A_69, B_70, C_71)=k2_xboole_0(B_70, C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(A_69)) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.57/1.91  tff(c_4993, plain, (![A_127, B_128, B_129]: (k4_subset_1(A_127, B_128, k3_subset_1(A_127, B_129))=k2_xboole_0(B_128, k3_subset_1(A_127, B_129)) | ~m1_subset_1(B_128, k1_zfmisc_1(A_127)) | ~m1_subset_1(B_129, k1_zfmisc_1(A_127)))), inference(resolution, [status(thm)], [c_22, c_897])).
% 4.57/1.91  tff(c_5010, plain, (![B_130]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_130))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_130)) | ~m1_subset_1(B_130, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_4993])).
% 4.57/1.91  tff(c_5017, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_5010])).
% 4.57/1.91  tff(c_5028, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3524, c_5017])).
% 4.57/1.91  tff(c_5030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_5028])).
% 4.57/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/1.91  
% 4.57/1.91  Inference rules
% 4.57/1.91  ----------------------
% 4.57/1.91  #Ref     : 0
% 4.57/1.91  #Sup     : 1256
% 4.57/1.91  #Fact    : 0
% 4.57/1.91  #Define  : 0
% 4.57/1.91  #Split   : 0
% 4.57/1.91  #Chain   : 0
% 4.57/1.91  #Close   : 0
% 4.57/1.91  
% 4.57/1.91  Ordering : KBO
% 4.57/1.91  
% 4.57/1.91  Simplification rules
% 4.57/1.91  ----------------------
% 4.57/1.91  #Subsume      : 3
% 4.57/1.91  #Demod        : 1346
% 4.57/1.91  #Tautology    : 902
% 4.57/1.91  #SimpNegUnit  : 1
% 4.57/1.91  #BackRed      : 6
% 4.57/1.91  
% 4.57/1.91  #Partial instantiations: 0
% 4.57/1.91  #Strategies tried      : 1
% 4.57/1.91  
% 4.57/1.91  Timing (in seconds)
% 4.57/1.91  ----------------------
% 4.57/1.91  Preprocessing        : 0.29
% 4.57/1.91  Parsing              : 0.16
% 4.57/1.91  CNF conversion       : 0.02
% 4.57/1.91  Main loop            : 0.86
% 4.57/1.91  Inferencing          : 0.24
% 4.57/1.91  Reduction            : 0.43
% 4.57/1.91  Demodulation         : 0.36
% 4.57/1.92  BG Simplification    : 0.03
% 4.57/1.92  Subsumption          : 0.11
% 4.57/1.92  Abstraction          : 0.04
% 4.57/1.92  MUC search           : 0.00
% 4.57/1.92  Cooper               : 0.00
% 4.57/1.92  Total                : 1.19
% 4.57/1.92  Index Insertion      : 0.00
% 4.57/1.92  Index Deletion       : 0.00
% 4.57/1.92  Index Matching       : 0.00
% 4.57/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
