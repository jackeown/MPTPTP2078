%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:45 EST 2020

% Result     : Theorem 10.05s
% Output     : CNFRefutation 10.05s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 309 expanded)
%              Number of leaves         :   28 ( 117 expanded)
%              Depth                    :   13
%              Number of atoms          :   82 ( 372 expanded)
%              Number of equality atoms :   68 ( 287 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_32,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_19,B_20] : k4_xboole_0(k2_xboole_0(A_19,B_20),B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_530,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r1_xboole_0(A_53,B_54)
      | ~ r2_hidden(C_55,k3_xboole_0(A_53,B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_651,plain,(
    ! [A_62,B_63] :
      ( ~ r1_xboole_0(A_62,B_63)
      | k3_xboole_0(A_62,B_63) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_530])).

tff(c_659,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_651])).

tff(c_701,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_659])).

tff(c_26,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_727,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_26])).

tff(c_730,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_727])).

tff(c_34,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_658,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_651])).

tff(c_666,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k4_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_26])).

tff(c_683,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_666])).

tff(c_14,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_39,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_184,plain,(
    k2_xboole_0('#skF_6','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_2])).

tff(c_197,plain,(
    ! [B_38,A_39] : k3_xboole_0(B_38,A_39) = k3_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_213,plain,(
    ! [A_39] : k3_xboole_0(k1_xboole_0,A_39) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_16])).

tff(c_388,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_406,plain,(
    ! [A_39] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_388])).

tff(c_421,plain,(
    ! [A_39] : k4_xboole_0(k1_xboole_0,A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_406])).

tff(c_288,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_303,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_288])).

tff(c_306,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_303])).

tff(c_844,plain,(
    ! [A_68,B_69,C_70] : k4_xboole_0(k4_xboole_0(A_68,B_69),C_70) = k4_xboole_0(A_68,k2_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_903,plain,(
    ! [A_18,C_70] : k4_xboole_0(A_18,k2_xboole_0(A_18,C_70)) = k4_xboole_0(k1_xboole_0,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_844])).

tff(c_1019,plain,(
    ! [A_73,C_74] : k4_xboole_0(A_73,k2_xboole_0(A_73,C_74)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_903])).

tff(c_1061,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_1019])).

tff(c_18,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_19452,plain,(
    ! [C_238,A_239,B_240] : k2_xboole_0(C_238,k4_xboole_0(A_239,k2_xboole_0(B_240,C_238))) = k2_xboole_0(C_238,k4_xboole_0(A_239,B_240)) ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_18])).

tff(c_19805,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_6','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1061,c_19452])).

tff(c_19960,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_14,c_19805])).

tff(c_861,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k2_xboole_0(B_69,k4_xboole_0(A_68,B_69))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_306])).

tff(c_925,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k2_xboole_0(B_69,A_68)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_861])).

tff(c_20118,plain,(
    ! [A_241] : k2_xboole_0('#skF_6',k4_xboole_0(A_241,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_6',k4_xboole_0(A_241,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_19452])).

tff(c_20315,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_925,c_20118])).

tff(c_20379,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19960,c_2,c_730,c_14,c_20315])).

tff(c_28,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1040,plain,(
    ! [A_73,C_74] : k3_xboole_0(A_73,k2_xboole_0(A_73,C_74)) = k4_xboole_0(A_73,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_28])).

tff(c_1085,plain,(
    ! [A_73,C_74] : k3_xboole_0(A_73,k2_xboole_0(A_73,C_74)) = A_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1040])).

tff(c_476,plain,(
    ! [A_51,B_52] : k4_xboole_0(k2_xboole_0(A_51,B_52),B_52) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2001,plain,(
    ! [B_93,A_94] : k4_xboole_0(k2_xboole_0(B_93,A_94),B_93) = k4_xboole_0(A_94,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_476])).

tff(c_2017,plain,(
    ! [B_93,A_94] : k4_xboole_0(k2_xboole_0(B_93,A_94),k4_xboole_0(A_94,B_93)) = k3_xboole_0(k2_xboole_0(B_93,A_94),B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_2001,c_28])).

tff(c_6603,plain,(
    ! [B_140,A_141] : k4_xboole_0(k2_xboole_0(B_140,A_141),k4_xboole_0(A_141,B_140)) = B_140 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_4,c_2017])).

tff(c_6786,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k4_xboole_0('#skF_6','#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_6603])).

tff(c_20401,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k4_xboole_0('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20379,c_6786])).

tff(c_20434,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_730,c_20401])).

tff(c_20416,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20379,c_658])).

tff(c_412,plain,(
    ! [B_4,A_3] : k4_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_388])).

tff(c_21001,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20416,c_412])).

tff(c_21050,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20434,c_20,c_21001])).

tff(c_21052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_21050])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:22:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.05/4.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.05/4.04  
% 10.05/4.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.05/4.05  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 10.05/4.05  
% 10.05/4.05  %Foreground sorts:
% 10.05/4.05  
% 10.05/4.05  
% 10.05/4.05  %Background operators:
% 10.05/4.05  
% 10.05/4.05  
% 10.05/4.05  %Foreground operators:
% 10.05/4.05  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.05/4.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.05/4.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.05/4.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.05/4.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.05/4.05  tff('#skF_5', type, '#skF_5': $i).
% 10.05/4.05  tff('#skF_6', type, '#skF_6': $i).
% 10.05/4.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.05/4.05  tff('#skF_3', type, '#skF_3': $i).
% 10.05/4.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.05/4.05  tff('#skF_4', type, '#skF_4': $i).
% 10.05/4.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.05/4.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.05/4.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.05/4.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.05/4.05  
% 10.05/4.06  tff(f_80, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 10.05/4.06  tff(f_63, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 10.05/4.06  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.05/4.06  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.05/4.06  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 10.05/4.06  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.05/4.06  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 10.05/4.06  tff(f_55, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.05/4.06  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.05/4.06  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.05/4.06  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.05/4.06  tff(f_65, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.05/4.06  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.05/4.06  tff(c_32, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.05/4.06  tff(c_22, plain, (![A_19, B_20]: (k4_xboole_0(k2_xboole_0(A_19, B_20), B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.05/4.06  tff(c_20, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.05/4.06  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.05/4.06  tff(c_36, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.05/4.06  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.05/4.06  tff(c_530, plain, (![A_53, B_54, C_55]: (~r1_xboole_0(A_53, B_54) | ~r2_hidden(C_55, k3_xboole_0(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.05/4.06  tff(c_651, plain, (![A_62, B_63]: (~r1_xboole_0(A_62, B_63) | k3_xboole_0(A_62, B_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_530])).
% 10.05/4.06  tff(c_659, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_651])).
% 10.05/4.06  tff(c_701, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4, c_659])).
% 10.05/4.06  tff(c_26, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.05/4.06  tff(c_727, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_701, c_26])).
% 10.05/4.06  tff(c_730, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_727])).
% 10.05/4.06  tff(c_34, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.05/4.06  tff(c_658, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_651])).
% 10.05/4.06  tff(c_666, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k4_xboole_0('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_658, c_26])).
% 10.05/4.06  tff(c_683, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_666])).
% 10.05/4.06  tff(c_14, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.05/4.06  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.05/4.06  tff(c_38, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.05/4.06  tff(c_39, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 10.05/4.06  tff(c_184, plain, (k2_xboole_0('#skF_6', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_39, c_2])).
% 10.05/4.06  tff(c_197, plain, (![B_38, A_39]: (k3_xboole_0(B_38, A_39)=k3_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.05/4.06  tff(c_16, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.05/4.06  tff(c_213, plain, (![A_39]: (k3_xboole_0(k1_xboole_0, A_39)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_197, c_16])).
% 10.05/4.06  tff(c_388, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.05/4.06  tff(c_406, plain, (![A_39]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_39))), inference(superposition, [status(thm), theory('equality')], [c_213, c_388])).
% 10.05/4.06  tff(c_421, plain, (![A_39]: (k4_xboole_0(k1_xboole_0, A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_406])).
% 10.05/4.06  tff(c_288, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.05/4.06  tff(c_303, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_288])).
% 10.05/4.06  tff(c_306, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_303])).
% 10.05/4.06  tff(c_844, plain, (![A_68, B_69, C_70]: (k4_xboole_0(k4_xboole_0(A_68, B_69), C_70)=k4_xboole_0(A_68, k2_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.05/4.06  tff(c_903, plain, (![A_18, C_70]: (k4_xboole_0(A_18, k2_xboole_0(A_18, C_70))=k4_xboole_0(k1_xboole_0, C_70))), inference(superposition, [status(thm), theory('equality')], [c_306, c_844])).
% 10.05/4.06  tff(c_1019, plain, (![A_73, C_74]: (k4_xboole_0(A_73, k2_xboole_0(A_73, C_74))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_421, c_903])).
% 10.05/4.06  tff(c_1061, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_184, c_1019])).
% 10.05/4.06  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.05/4.06  tff(c_19452, plain, (![C_238, A_239, B_240]: (k2_xboole_0(C_238, k4_xboole_0(A_239, k2_xboole_0(B_240, C_238)))=k2_xboole_0(C_238, k4_xboole_0(A_239, B_240)))), inference(superposition, [status(thm), theory('equality')], [c_844, c_18])).
% 10.05/4.06  tff(c_19805, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1061, c_19452])).
% 10.05/4.06  tff(c_19960, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_683, c_14, c_19805])).
% 10.05/4.06  tff(c_861, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k2_xboole_0(B_69, k4_xboole_0(A_68, B_69)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_844, c_306])).
% 10.05/4.06  tff(c_925, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k2_xboole_0(B_69, A_68))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_861])).
% 10.05/4.06  tff(c_20118, plain, (![A_241]: (k2_xboole_0('#skF_6', k4_xboole_0(A_241, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_6', k4_xboole_0(A_241, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_39, c_19452])).
% 10.05/4.06  tff(c_20315, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_925, c_20118])).
% 10.05/4.06  tff(c_20379, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19960, c_2, c_730, c_14, c_20315])).
% 10.05/4.06  tff(c_28, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.05/4.06  tff(c_1040, plain, (![A_73, C_74]: (k3_xboole_0(A_73, k2_xboole_0(A_73, C_74))=k4_xboole_0(A_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1019, c_28])).
% 10.05/4.06  tff(c_1085, plain, (![A_73, C_74]: (k3_xboole_0(A_73, k2_xboole_0(A_73, C_74))=A_73)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1040])).
% 10.05/4.06  tff(c_476, plain, (![A_51, B_52]: (k4_xboole_0(k2_xboole_0(A_51, B_52), B_52)=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.05/4.06  tff(c_2001, plain, (![B_93, A_94]: (k4_xboole_0(k2_xboole_0(B_93, A_94), B_93)=k4_xboole_0(A_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_2, c_476])).
% 10.05/4.06  tff(c_2017, plain, (![B_93, A_94]: (k4_xboole_0(k2_xboole_0(B_93, A_94), k4_xboole_0(A_94, B_93))=k3_xboole_0(k2_xboole_0(B_93, A_94), B_93))), inference(superposition, [status(thm), theory('equality')], [c_2001, c_28])).
% 10.05/4.06  tff(c_6603, plain, (![B_140, A_141]: (k4_xboole_0(k2_xboole_0(B_140, A_141), k4_xboole_0(A_141, B_140))=B_140)), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_4, c_2017])).
% 10.05/4.06  tff(c_6786, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k4_xboole_0('#skF_6', '#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_39, c_6603])).
% 10.05/4.06  tff(c_20401, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k4_xboole_0('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20379, c_6786])).
% 10.05/4.06  tff(c_20434, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_730, c_20401])).
% 10.05/4.06  tff(c_20416, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20379, c_658])).
% 10.05/4.06  tff(c_412, plain, (![B_4, A_3]: (k4_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_388])).
% 10.05/4.06  tff(c_21001, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20416, c_412])).
% 10.05/4.06  tff(c_21050, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20434, c_20, c_21001])).
% 10.05/4.06  tff(c_21052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_21050])).
% 10.05/4.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.05/4.06  
% 10.05/4.06  Inference rules
% 10.05/4.06  ----------------------
% 10.05/4.06  #Ref     : 0
% 10.05/4.06  #Sup     : 5284
% 10.05/4.06  #Fact    : 0
% 10.05/4.06  #Define  : 0
% 10.05/4.06  #Split   : 3
% 10.05/4.06  #Chain   : 0
% 10.05/4.06  #Close   : 0
% 10.05/4.06  
% 10.05/4.06  Ordering : KBO
% 10.05/4.06  
% 10.05/4.06  Simplification rules
% 10.05/4.06  ----------------------
% 10.05/4.06  #Subsume      : 158
% 10.05/4.06  #Demod        : 6078
% 10.05/4.06  #Tautology    : 3304
% 10.05/4.06  #SimpNegUnit  : 30
% 10.05/4.06  #BackRed      : 36
% 10.05/4.06  
% 10.05/4.06  #Partial instantiations: 0
% 10.05/4.06  #Strategies tried      : 1
% 10.05/4.06  
% 10.05/4.06  Timing (in seconds)
% 10.05/4.06  ----------------------
% 10.05/4.07  Preprocessing        : 0.30
% 10.05/4.07  Parsing              : 0.16
% 10.05/4.07  CNF conversion       : 0.02
% 10.05/4.07  Main loop            : 3.00
% 10.05/4.07  Inferencing          : 0.54
% 10.05/4.07  Reduction            : 1.85
% 10.05/4.07  Demodulation         : 1.67
% 10.05/4.07  BG Simplification    : 0.07
% 10.05/4.07  Subsumption          : 0.40
% 10.05/4.07  Abstraction          : 0.10
% 10.05/4.07  MUC search           : 0.00
% 10.05/4.07  Cooper               : 0.00
% 10.05/4.07  Total                : 3.34
% 10.05/4.07  Index Insertion      : 0.00
% 10.05/4.07  Index Deletion       : 0.00
% 10.05/4.07  Index Matching       : 0.00
% 10.05/4.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
