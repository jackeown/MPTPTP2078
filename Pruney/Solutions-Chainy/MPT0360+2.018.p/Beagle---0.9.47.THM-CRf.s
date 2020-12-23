%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:20 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.96s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 164 expanded)
%              Number of leaves         :   39 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  117 ( 220 expanded)
%              Number of equality atoms :   53 ( 110 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_64,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_68,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_100,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_80,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k5_xboole_0(B,C))
    <=> ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_103,plain,(
    ! [B_42,A_43] : k5_xboole_0(B_42,A_43) = k5_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_119,plain,(
    ! [A_43] : k5_xboole_0(k1_xboole_0,A_43) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_30])).

tff(c_34,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_586,plain,(
    ! [A_97,B_98,C_99] : k5_xboole_0(k5_xboole_0(A_97,B_98),C_99) = k5_xboole_0(A_97,k5_xboole_0(B_98,C_99)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_656,plain,(
    ! [A_22,C_99] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_99)) = k5_xboole_0(k1_xboole_0,C_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_586])).

tff(c_669,plain,(
    ! [A_22,C_99] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_99)) = C_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_656])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_215,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(A_51,B_52) = B_52
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_227,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62,c_215])).

tff(c_1072,plain,(
    ! [A_108,B_109] : k5_xboole_0(k5_xboole_0(A_108,B_109),k2_xboole_0(A_108,B_109)) = k3_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1154,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),'#skF_4') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_1072])).

tff(c_1186,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_2,c_2,c_1154])).

tff(c_60,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_485,plain,(
    ! [A_91,B_92] :
      ( k4_xboole_0(A_91,B_92) = k3_subset_1(A_91,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_494,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_485])).

tff(c_677,plain,(
    ! [A_100,C_101] : k5_xboole_0(A_100,k5_xboole_0(A_100,C_101)) = C_101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_656])).

tff(c_726,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_677])).

tff(c_56,plain,(
    ! [A_36] : ~ v1_xboole_0(k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_273,plain,(
    ! [B_66,A_67] :
      ( r2_hidden(B_66,A_67)
      | ~ m1_subset_1(B_66,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_44,plain,(
    ! [A_31] : k3_tarski(k1_zfmisc_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_246,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,k3_tarski(B_57))
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_255,plain,(
    ! [A_56,A_31] :
      ( r1_tarski(A_56,A_31)
      | ~ r2_hidden(A_56,k1_zfmisc_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_246])).

tff(c_280,plain,(
    ! [B_66,A_31] :
      ( r1_tarski(B_66,A_31)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_31))
      | v1_xboole_0(k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_273,c_255])).

tff(c_285,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(B_68,A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_280])).

tff(c_294,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_285])).

tff(c_12,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_tarski(A_14,'#skF_1'(A_14,B_15,C_16))
      | k2_xboole_0(A_14,C_16) = B_15
      | ~ r1_tarski(C_16,B_15)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1656,plain,(
    ! [B_134,A_135,C_136] :
      ( ~ r1_tarski(B_134,'#skF_1'(A_135,B_134,C_136))
      | k2_xboole_0(A_135,C_136) = B_134
      | ~ r1_tarski(C_136,B_134)
      | ~ r1_tarski(A_135,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1664,plain,(
    ! [B_15,C_16] :
      ( k2_xboole_0(B_15,C_16) = B_15
      | ~ r1_tarski(C_16,B_15)
      | ~ r1_tarski(B_15,B_15) ) ),
    inference(resolution,[status(thm)],[c_28,c_1656])).

tff(c_1676,plain,(
    ! [B_137,C_138] :
      ( k2_xboole_0(B_137,C_138) = B_137
      | ~ r1_tarski(C_138,B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1664])).

tff(c_1732,plain,(
    k2_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_294,c_1676])).

tff(c_36,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k2_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1833,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_4'),'#skF_2') = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_36])).

tff(c_1840,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_2,c_2,c_1833])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1852,plain,(
    k5_xboole_0('#skF_2','#skF_4') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1840,c_14])).

tff(c_1857,plain,(
    k5_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_1852])).

tff(c_2324,plain,(
    k5_xboole_0('#skF_4','#skF_2') = k3_subset_1('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1857])).

tff(c_748,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k5_xboole_0(B_103,A_102)) = B_103 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_677])).

tff(c_787,plain,(
    ! [A_22,C_99] : k5_xboole_0(k5_xboole_0(A_22,C_99),C_99) = A_22 ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_748])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_298,plain,(
    k2_xboole_0('#skF_4','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_294,c_22])).

tff(c_1148,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_2'),'#skF_2') = k3_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_1072])).

tff(c_1184,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_1148])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_xboole_0(A_9,k3_xboole_0(B_10,C_11))
      | ~ r1_tarski(A_9,k5_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1327,plain,(
    ! [A_9] :
      ( r1_xboole_0(A_9,'#skF_4')
      | ~ r1_tarski(A_9,k5_xboole_0('#skF_4','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1184,c_18])).

tff(c_3942,plain,(
    ! [A_166] :
      ( r1_xboole_0(A_166,'#skF_4')
      | ~ r1_tarski(A_166,k3_subset_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2324,c_1327])).

tff(c_3959,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3942])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3968,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3959,c_4])).

tff(c_3970,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_3968])).

tff(c_3972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3970])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:04:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.96/1.94  
% 4.96/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.96/1.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.96/1.94  
% 4.96/1.94  %Foreground sorts:
% 4.96/1.94  
% 4.96/1.94  
% 4.96/1.94  %Background operators:
% 4.96/1.94  
% 4.96/1.94  
% 4.96/1.94  %Foreground operators:
% 4.96/1.94  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.96/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.96/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.96/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.96/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.96/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.96/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.96/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.96/1.94  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.96/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.96/1.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.96/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.96/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.96/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.96/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.96/1.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.96/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.96/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.96/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.96/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.96/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.96/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.96/1.94  
% 4.96/1.96  tff(f_109, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 4.96/1.96  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.96/1.96  tff(f_64, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.96/1.96  tff(f_68, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.96/1.96  tff(f_66, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.96/1.96  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.96/1.96  tff(f_70, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.96/1.96  tff(f_97, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.96/1.96  tff(f_100, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.96/1.96  tff(f_93, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.96/1.96  tff(f_80, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 4.96/1.96  tff(f_76, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 4.96/1.96  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.96/1.96  tff(f_62, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 4.96/1.96  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.96/1.96  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 4.96/1.96  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.96/1.96  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.96/1.96  tff(c_103, plain, (![B_42, A_43]: (k5_xboole_0(B_42, A_43)=k5_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.96/1.96  tff(c_30, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.96/1.96  tff(c_119, plain, (![A_43]: (k5_xboole_0(k1_xboole_0, A_43)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_103, c_30])).
% 4.96/1.96  tff(c_34, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.96/1.96  tff(c_586, plain, (![A_97, B_98, C_99]: (k5_xboole_0(k5_xboole_0(A_97, B_98), C_99)=k5_xboole_0(A_97, k5_xboole_0(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.96/1.96  tff(c_656, plain, (![A_22, C_99]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_99))=k5_xboole_0(k1_xboole_0, C_99))), inference(superposition, [status(thm), theory('equality')], [c_34, c_586])).
% 4.96/1.96  tff(c_669, plain, (![A_22, C_99]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_99))=C_99)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_656])).
% 4.96/1.96  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.96/1.96  tff(c_62, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.96/1.96  tff(c_215, plain, (![A_51, B_52]: (k2_xboole_0(A_51, B_52)=B_52 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.96/1.96  tff(c_227, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_62, c_215])).
% 4.96/1.96  tff(c_1072, plain, (![A_108, B_109]: (k5_xboole_0(k5_xboole_0(A_108, B_109), k2_xboole_0(A_108, B_109))=k3_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.96/1.96  tff(c_1154, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), '#skF_4')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_227, c_1072])).
% 4.96/1.96  tff(c_1186, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_669, c_2, c_2, c_1154])).
% 4.96/1.96  tff(c_60, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.96/1.96  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.96/1.96  tff(c_485, plain, (![A_91, B_92]: (k4_xboole_0(A_91, B_92)=k3_subset_1(A_91, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.96/1.96  tff(c_494, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_485])).
% 4.96/1.96  tff(c_677, plain, (![A_100, C_101]: (k5_xboole_0(A_100, k5_xboole_0(A_100, C_101))=C_101)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_656])).
% 4.96/1.96  tff(c_726, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_677])).
% 4.96/1.96  tff(c_56, plain, (![A_36]: (~v1_xboole_0(k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.96/1.96  tff(c_273, plain, (![B_66, A_67]: (r2_hidden(B_66, A_67) | ~m1_subset_1(B_66, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.96/1.96  tff(c_44, plain, (![A_31]: (k3_tarski(k1_zfmisc_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.96/1.96  tff(c_246, plain, (![A_56, B_57]: (r1_tarski(A_56, k3_tarski(B_57)) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.96/1.96  tff(c_255, plain, (![A_56, A_31]: (r1_tarski(A_56, A_31) | ~r2_hidden(A_56, k1_zfmisc_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_246])).
% 4.96/1.96  tff(c_280, plain, (![B_66, A_31]: (r1_tarski(B_66, A_31) | ~m1_subset_1(B_66, k1_zfmisc_1(A_31)) | v1_xboole_0(k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_273, c_255])).
% 4.96/1.96  tff(c_285, plain, (![B_68, A_69]: (r1_tarski(B_68, A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)))), inference(negUnitSimplification, [status(thm)], [c_56, c_280])).
% 4.96/1.96  tff(c_294, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_285])).
% 4.96/1.96  tff(c_12, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.96/1.96  tff(c_28, plain, (![A_14, B_15, C_16]: (r1_tarski(A_14, '#skF_1'(A_14, B_15, C_16)) | k2_xboole_0(A_14, C_16)=B_15 | ~r1_tarski(C_16, B_15) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.96/1.96  tff(c_1656, plain, (![B_134, A_135, C_136]: (~r1_tarski(B_134, '#skF_1'(A_135, B_134, C_136)) | k2_xboole_0(A_135, C_136)=B_134 | ~r1_tarski(C_136, B_134) | ~r1_tarski(A_135, B_134))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.96/1.96  tff(c_1664, plain, (![B_15, C_16]: (k2_xboole_0(B_15, C_16)=B_15 | ~r1_tarski(C_16, B_15) | ~r1_tarski(B_15, B_15))), inference(resolution, [status(thm)], [c_28, c_1656])).
% 4.96/1.96  tff(c_1676, plain, (![B_137, C_138]: (k2_xboole_0(B_137, C_138)=B_137 | ~r1_tarski(C_138, B_137))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1664])).
% 4.96/1.96  tff(c_1732, plain, (k2_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_294, c_1676])).
% 4.96/1.96  tff(c_36, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k2_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.96/1.96  tff(c_1833, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_4'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1732, c_36])).
% 4.96/1.96  tff(c_1840, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_726, c_2, c_2, c_1833])).
% 4.96/1.96  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.96/1.96  tff(c_1852, plain, (k5_xboole_0('#skF_2', '#skF_4')=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1840, c_14])).
% 4.96/1.96  tff(c_1857, plain, (k5_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_494, c_1852])).
% 4.96/1.96  tff(c_2324, plain, (k5_xboole_0('#skF_4', '#skF_2')=k3_subset_1('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2, c_1857])).
% 4.96/1.96  tff(c_748, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k5_xboole_0(B_103, A_102))=B_103)), inference(superposition, [status(thm), theory('equality')], [c_2, c_677])).
% 4.96/1.96  tff(c_787, plain, (![A_22, C_99]: (k5_xboole_0(k5_xboole_0(A_22, C_99), C_99)=A_22)), inference(superposition, [status(thm), theory('equality')], [c_669, c_748])).
% 4.96/1.96  tff(c_22, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.96/1.96  tff(c_298, plain, (k2_xboole_0('#skF_4', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_294, c_22])).
% 4.96/1.96  tff(c_1148, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_2'), '#skF_2')=k3_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_298, c_1072])).
% 4.96/1.96  tff(c_1184, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_787, c_1148])).
% 4.96/1.96  tff(c_18, plain, (![A_9, B_10, C_11]: (r1_xboole_0(A_9, k3_xboole_0(B_10, C_11)) | ~r1_tarski(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.96/1.96  tff(c_1327, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_4') | ~r1_tarski(A_9, k5_xboole_0('#skF_4', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1184, c_18])).
% 4.96/1.96  tff(c_3942, plain, (![A_166]: (r1_xboole_0(A_166, '#skF_4') | ~r1_tarski(A_166, k3_subset_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2324, c_1327])).
% 4.96/1.96  tff(c_3959, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_3942])).
% 4.96/1.96  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.96/1.96  tff(c_3968, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_3959, c_4])).
% 4.96/1.96  tff(c_3970, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1186, c_3968])).
% 4.96/1.96  tff(c_3972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_3970])).
% 4.96/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.96/1.96  
% 4.96/1.96  Inference rules
% 4.96/1.96  ----------------------
% 4.96/1.96  #Ref     : 0
% 4.96/1.96  #Sup     : 1024
% 4.96/1.96  #Fact    : 0
% 4.96/1.96  #Define  : 0
% 4.96/1.96  #Split   : 6
% 4.96/1.96  #Chain   : 0
% 4.96/1.96  #Close   : 0
% 4.96/1.96  
% 4.96/1.96  Ordering : KBO
% 4.96/1.96  
% 4.96/1.96  Simplification rules
% 4.96/1.96  ----------------------
% 4.96/1.96  #Subsume      : 20
% 4.96/1.96  #Demod        : 795
% 4.96/1.96  #Tautology    : 559
% 4.96/1.96  #SimpNegUnit  : 3
% 4.96/1.96  #BackRed      : 8
% 4.96/1.96  
% 4.96/1.96  #Partial instantiations: 0
% 4.96/1.96  #Strategies tried      : 1
% 4.96/1.96  
% 4.96/1.96  Timing (in seconds)
% 4.96/1.96  ----------------------
% 4.96/1.96  Preprocessing        : 0.33
% 4.96/1.96  Parsing              : 0.18
% 4.96/1.96  CNF conversion       : 0.02
% 4.96/1.96  Main loop            : 0.82
% 4.96/1.96  Inferencing          : 0.25
% 4.96/1.96  Reduction            : 0.34
% 4.96/1.96  Demodulation         : 0.27
% 4.96/1.96  BG Simplification    : 0.03
% 4.96/1.96  Subsumption          : 0.13
% 4.96/1.96  Abstraction          : 0.03
% 4.96/1.96  MUC search           : 0.00
% 4.96/1.96  Cooper               : 0.00
% 4.96/1.96  Total                : 1.19
% 4.96/1.96  Index Insertion      : 0.00
% 4.96/1.96  Index Deletion       : 0.00
% 4.96/1.96  Index Matching       : 0.00
% 4.96/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
