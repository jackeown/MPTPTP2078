%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:23 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 109 expanded)
%              Number of leaves         :   38 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 159 expanded)
%              Number of equality atoms :   39 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_44,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    ! [A_27] : v1_relat_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [A_27] : v1_funct_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_22] : k1_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_605,plain,(
    ! [B_100,A_101] :
      ( k3_xboole_0(k1_relat_1(B_100),A_101) = k1_relat_1(k7_relat_1(B_100,A_101))
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_661,plain,(
    ! [A_22,A_101] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_22),A_101)) = k3_xboole_0(A_22,A_101)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_605])).

tff(c_665,plain,(
    ! [A_22,A_101] : k1_relat_1(k7_relat_1(k6_relat_1(A_22),A_101)) = k3_xboole_0(A_22,A_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_661])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( k5_relat_1(k6_relat_1(A_25),B_26) = k7_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1030,plain,(
    ! [A_123,B_124] :
      ( k10_relat_1(A_123,k1_relat_1(B_124)) = k1_relat_1(k5_relat_1(A_123,B_124))
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1053,plain,(
    ! [A_123,A_22] :
      ( k1_relat_1(k5_relat_1(A_123,k6_relat_1(A_22))) = k10_relat_1(A_123,A_22)
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1030])).

tff(c_1957,plain,(
    ! [A_185,A_186] :
      ( k1_relat_1(k5_relat_1(A_185,k6_relat_1(A_186))) = k10_relat_1(A_185,A_186)
      | ~ v1_relat_1(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1053])).

tff(c_1976,plain,(
    ! [A_186,A_25] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_186),A_25)) = k10_relat_1(k6_relat_1(A_25),A_186)
      | ~ v1_relat_1(k6_relat_1(A_25))
      | ~ v1_relat_1(k6_relat_1(A_186)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1957])).

tff(c_1980,plain,(
    ! [A_25,A_186] : k10_relat_1(k6_relat_1(A_25),A_186) = k3_xboole_0(A_186,A_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_665,c_1976])).

tff(c_28,plain,(
    ! [A_22] : k2_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_187,plain,(
    ! [A_55] :
      ( k10_relat_1(A_55,k2_relat_1(A_55)) = k1_relat_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_196,plain,(
    ! [A_22] :
      ( k10_relat_1(k6_relat_1(A_22),A_22) = k1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_187])).

tff(c_200,plain,(
    ! [A_22] : k10_relat_1(k6_relat_1(A_22),A_22) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_196])).

tff(c_751,plain,(
    ! [B_108,A_109] :
      ( r1_tarski(k9_relat_1(B_108,k10_relat_1(B_108,A_109)),A_109)
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_766,plain,(
    ! [A_22] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_22),A_22),A_22)
      | ~ v1_funct_1(k6_relat_1(A_22))
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_751])).

tff(c_776,plain,(
    ! [A_110] : r1_tarski(k9_relat_1(k6_relat_1(A_110),A_110),A_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_766])).

tff(c_46,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_280,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(A_67,C_68)
      | ~ r1_tarski(B_69,C_68)
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_294,plain,(
    ! [A_67] :
      ( r1_tarski(A_67,'#skF_2')
      | ~ r1_tarski(A_67,k10_relat_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_280])).

tff(c_789,plain,(
    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),k10_relat_1('#skF_1','#skF_3')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_776,c_294])).

tff(c_42,plain,(
    ! [A_33,C_35,B_34] :
      ( r1_tarski(A_33,k10_relat_1(C_35,B_34))
      | ~ r1_tarski(k9_relat_1(C_35,A_33),B_34)
      | ~ r1_tarski(A_33,k1_relat_1(C_35))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4059,plain,
    ( r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),'#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),k1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3'))))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_789,c_42])).

tff(c_4066,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_6,c_26,c_1980,c_4059])).

tff(c_16,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    ! [A_47,B_48] : k1_setfam_1(k2_tarski(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,(
    ! [B_51,A_52] : k1_setfam_1(k2_tarski(B_51,A_52)) = k3_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_107])).

tff(c_20,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_137,plain,(
    ! [B_51,A_52] : k3_xboole_0(B_51,A_52) = k3_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_20])).

tff(c_226,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_244,plain,(
    ! [A_61,B_62] : r1_tarski(k3_xboole_0(A_61,B_62),A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_12])).

tff(c_247,plain,(
    ! [B_51,A_52] : r1_tarski(k3_xboole_0(B_51,A_52),A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_244])).

tff(c_261,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_272,plain,(
    ! [B_51,A_52] :
      ( k3_xboole_0(B_51,A_52) = A_52
      | ~ r1_tarski(A_52,k3_xboole_0(B_51,A_52)) ) ),
    inference(resolution,[status(thm)],[c_247,c_261])).

tff(c_4089,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_4066,c_272])).

tff(c_38,plain,(
    ! [A_28,C_30,B_29] :
      ( k3_xboole_0(A_28,k10_relat_1(C_30,B_29)) = k10_relat_1(k7_relat_1(C_30,A_28),B_29)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4163,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4089,c_38])).

tff(c_4231,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4163])).

tff(c_4233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_4231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.92  
% 4.88/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.93  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.88/1.93  
% 4.88/1.93  %Foreground sorts:
% 4.88/1.93  
% 4.88/1.93  
% 4.88/1.93  %Background operators:
% 4.88/1.93  
% 4.88/1.93  
% 4.88/1.93  %Foreground operators:
% 4.88/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.88/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.88/1.93  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.88/1.93  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.88/1.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.88/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.88/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.88/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.88/1.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.88/1.93  tff('#skF_2', type, '#skF_2': $i).
% 4.88/1.93  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.88/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.88/1.93  tff('#skF_1', type, '#skF_1': $i).
% 4.88/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/1.93  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.88/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.88/1.93  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.88/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.88/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.88/1.93  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.88/1.93  
% 5.24/1.94  tff(f_106, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 5.24/1.94  tff(f_76, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.24/1.94  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.24/1.94  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.24/1.94  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 5.24/1.94  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 5.24/1.94  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 5.24/1.94  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.24/1.94  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 5.24/1.94  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.24/1.94  tff(f_96, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 5.24/1.94  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.24/1.94  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.24/1.94  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.24/1.94  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.24/1.94  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 5.24/1.94  tff(c_44, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.24/1.94  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.24/1.94  tff(c_34, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.24/1.94  tff(c_36, plain, (![A_27]: (v1_funct_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.24/1.94  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.24/1.94  tff(c_26, plain, (![A_22]: (k1_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.24/1.94  tff(c_605, plain, (![B_100, A_101]: (k3_xboole_0(k1_relat_1(B_100), A_101)=k1_relat_1(k7_relat_1(B_100, A_101)) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.24/1.94  tff(c_661, plain, (![A_22, A_101]: (k1_relat_1(k7_relat_1(k6_relat_1(A_22), A_101))=k3_xboole_0(A_22, A_101) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_605])).
% 5.24/1.94  tff(c_665, plain, (![A_22, A_101]: (k1_relat_1(k7_relat_1(k6_relat_1(A_22), A_101))=k3_xboole_0(A_22, A_101))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_661])).
% 5.24/1.94  tff(c_32, plain, (![A_25, B_26]: (k5_relat_1(k6_relat_1(A_25), B_26)=k7_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.24/1.94  tff(c_1030, plain, (![A_123, B_124]: (k10_relat_1(A_123, k1_relat_1(B_124))=k1_relat_1(k5_relat_1(A_123, B_124)) | ~v1_relat_1(B_124) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.24/1.94  tff(c_1053, plain, (![A_123, A_22]: (k1_relat_1(k5_relat_1(A_123, k6_relat_1(A_22)))=k10_relat_1(A_123, A_22) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(A_123))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1030])).
% 5.24/1.94  tff(c_1957, plain, (![A_185, A_186]: (k1_relat_1(k5_relat_1(A_185, k6_relat_1(A_186)))=k10_relat_1(A_185, A_186) | ~v1_relat_1(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1053])).
% 5.24/1.94  tff(c_1976, plain, (![A_186, A_25]: (k1_relat_1(k7_relat_1(k6_relat_1(A_186), A_25))=k10_relat_1(k6_relat_1(A_25), A_186) | ~v1_relat_1(k6_relat_1(A_25)) | ~v1_relat_1(k6_relat_1(A_186)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1957])).
% 5.24/1.94  tff(c_1980, plain, (![A_25, A_186]: (k10_relat_1(k6_relat_1(A_25), A_186)=k3_xboole_0(A_186, A_25))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_665, c_1976])).
% 5.24/1.94  tff(c_28, plain, (![A_22]: (k2_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.24/1.94  tff(c_187, plain, (![A_55]: (k10_relat_1(A_55, k2_relat_1(A_55))=k1_relat_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.24/1.94  tff(c_196, plain, (![A_22]: (k10_relat_1(k6_relat_1(A_22), A_22)=k1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_187])).
% 5.24/1.94  tff(c_200, plain, (![A_22]: (k10_relat_1(k6_relat_1(A_22), A_22)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_196])).
% 5.24/1.94  tff(c_751, plain, (![B_108, A_109]: (r1_tarski(k9_relat_1(B_108, k10_relat_1(B_108, A_109)), A_109) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.24/1.94  tff(c_766, plain, (![A_22]: (r1_tarski(k9_relat_1(k6_relat_1(A_22), A_22), A_22) | ~v1_funct_1(k6_relat_1(A_22)) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_200, c_751])).
% 5.24/1.94  tff(c_776, plain, (![A_110]: (r1_tarski(k9_relat_1(k6_relat_1(A_110), A_110), A_110))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_766])).
% 5.24/1.94  tff(c_46, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.24/1.94  tff(c_280, plain, (![A_67, C_68, B_69]: (r1_tarski(A_67, C_68) | ~r1_tarski(B_69, C_68) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.24/1.94  tff(c_294, plain, (![A_67]: (r1_tarski(A_67, '#skF_2') | ~r1_tarski(A_67, k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_46, c_280])).
% 5.24/1.94  tff(c_789, plain, (r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), k10_relat_1('#skF_1', '#skF_3')), '#skF_2')), inference(resolution, [status(thm)], [c_776, c_294])).
% 5.24/1.94  tff(c_42, plain, (![A_33, C_35, B_34]: (r1_tarski(A_33, k10_relat_1(C_35, B_34)) | ~r1_tarski(k9_relat_1(C_35, A_33), B_34) | ~r1_tarski(A_33, k1_relat_1(C_35)) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.24/1.94  tff(c_4059, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))) | ~v1_funct_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3'))) | ~v1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_789, c_42])).
% 5.24/1.94  tff(c_4066, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_6, c_26, c_1980, c_4059])).
% 5.24/1.94  tff(c_16, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.24/1.94  tff(c_107, plain, (![A_47, B_48]: (k1_setfam_1(k2_tarski(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.24/1.94  tff(c_131, plain, (![B_51, A_52]: (k1_setfam_1(k2_tarski(B_51, A_52))=k3_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_16, c_107])).
% 5.24/1.94  tff(c_20, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.24/1.94  tff(c_137, plain, (![B_51, A_52]: (k3_xboole_0(B_51, A_52)=k3_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_131, c_20])).
% 5.24/1.94  tff(c_226, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.24/1.94  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.24/1.94  tff(c_244, plain, (![A_61, B_62]: (r1_tarski(k3_xboole_0(A_61, B_62), A_61))), inference(superposition, [status(thm), theory('equality')], [c_226, c_12])).
% 5.24/1.94  tff(c_247, plain, (![B_51, A_52]: (r1_tarski(k3_xboole_0(B_51, A_52), A_52))), inference(superposition, [status(thm), theory('equality')], [c_137, c_244])).
% 5.24/1.94  tff(c_261, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.24/1.94  tff(c_272, plain, (![B_51, A_52]: (k3_xboole_0(B_51, A_52)=A_52 | ~r1_tarski(A_52, k3_xboole_0(B_51, A_52)))), inference(resolution, [status(thm)], [c_247, c_261])).
% 5.24/1.94  tff(c_4089, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_4066, c_272])).
% 5.24/1.94  tff(c_38, plain, (![A_28, C_30, B_29]: (k3_xboole_0(A_28, k10_relat_1(C_30, B_29))=k10_relat_1(k7_relat_1(C_30, A_28), B_29) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.24/1.94  tff(c_4163, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4089, c_38])).
% 5.24/1.94  tff(c_4231, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4163])).
% 5.24/1.94  tff(c_4233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_4231])).
% 5.24/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/1.94  
% 5.24/1.94  Inference rules
% 5.24/1.94  ----------------------
% 5.24/1.94  #Ref     : 0
% 5.24/1.94  #Sup     : 977
% 5.24/1.94  #Fact    : 0
% 5.24/1.94  #Define  : 0
% 5.24/1.94  #Split   : 1
% 5.24/1.94  #Chain   : 0
% 5.24/1.94  #Close   : 0
% 5.24/1.94  
% 5.24/1.94  Ordering : KBO
% 5.24/1.94  
% 5.24/1.94  Simplification rules
% 5.24/1.94  ----------------------
% 5.24/1.94  #Subsume      : 19
% 5.24/1.94  #Demod        : 404
% 5.24/1.94  #Tautology    : 366
% 5.24/1.94  #SimpNegUnit  : 1
% 5.24/1.94  #BackRed      : 1
% 5.24/1.94  
% 5.24/1.94  #Partial instantiations: 0
% 5.24/1.94  #Strategies tried      : 1
% 5.24/1.94  
% 5.24/1.94  Timing (in seconds)
% 5.24/1.94  ----------------------
% 5.24/1.94  Preprocessing        : 0.32
% 5.24/1.94  Parsing              : 0.17
% 5.24/1.94  CNF conversion       : 0.02
% 5.24/1.94  Main loop            : 0.87
% 5.24/1.94  Inferencing          : 0.25
% 5.24/1.94  Reduction            : 0.34
% 5.24/1.94  Demodulation         : 0.28
% 5.24/1.94  BG Simplification    : 0.03
% 5.24/1.94  Subsumption          : 0.18
% 5.24/1.94  Abstraction          : 0.04
% 5.24/1.94  MUC search           : 0.00
% 5.24/1.94  Cooper               : 0.00
% 5.24/1.95  Total                : 1.22
% 5.24/1.95  Index Insertion      : 0.00
% 5.24/1.95  Index Deletion       : 0.00
% 5.24/1.95  Index Matching       : 0.00
% 5.24/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
