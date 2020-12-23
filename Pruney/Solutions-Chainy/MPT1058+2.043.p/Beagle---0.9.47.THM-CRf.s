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
% DateTime   : Thu Dec  3 10:17:27 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 176 expanded)
%              Number of leaves         :   36 (  78 expanded)
%              Depth                    :   17
%              Number of atoms          :  116 ( 316 expanded)
%              Number of equality atoms :   23 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_81,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_103,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_69,axiom,(
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

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k7_relat_1(B_29,A_28),B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k7_relat_1(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [B_21,A_20,C_23] :
      ( r1_tarski(k10_relat_1(B_21,A_20),k10_relat_1(C_23,A_20))
      | ~ r1_tarski(B_21,C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    ! [A_31,C_33,B_32] :
      ( k3_xboole_0(A_31,k10_relat_1(C_33,B_32)) = k10_relat_1(k7_relat_1(C_33,A_31),B_32)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [A_30] : v1_funct_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    ! [B_40,A_39] : k5_relat_1(k6_relat_1(B_40),k6_relat_1(A_39)) = k6_relat_1(k3_xboole_0(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_263,plain,(
    ! [A_84,B_85] :
      ( k10_relat_1(A_84,k1_relat_1(B_85)) = k1_relat_1(k5_relat_1(A_84,B_85))
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_283,plain,(
    ! [A_84,A_27] :
      ( k1_relat_1(k5_relat_1(A_84,k6_relat_1(A_27))) = k10_relat_1(A_84,A_27)
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_263])).

tff(c_292,plain,(
    ! [A_86,A_87] :
      ( k1_relat_1(k5_relat_1(A_86,k6_relat_1(A_87))) = k10_relat_1(A_86,A_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_283])).

tff(c_304,plain,(
    ! [A_39,B_40] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_39,B_40))) = k10_relat_1(k6_relat_1(B_40),A_39)
      | ~ v1_relat_1(k6_relat_1(B_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_292])).

tff(c_308,plain,(
    ! [B_40,A_39] : k10_relat_1(k6_relat_1(B_40),A_39) = k3_xboole_0(A_39,B_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_304])).

tff(c_28,plain,(
    ! [A_27] : k2_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_93,plain,(
    ! [A_56] :
      ( k10_relat_1(A_56,k2_relat_1(A_56)) = k1_relat_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_102,plain,(
    ! [A_27] :
      ( k10_relat_1(k6_relat_1(A_27),A_27) = k1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_93])).

tff(c_106,plain,(
    ! [A_27] : k10_relat_1(k6_relat_1(A_27),A_27) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_102])).

tff(c_181,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(k9_relat_1(B_72,k10_relat_1(B_72,A_73)),A_73)
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_196,plain,(
    ! [A_27] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_27),A_27),A_27)
      | ~ v1_funct_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_181])).

tff(c_206,plain,(
    ! [A_74] : r1_tarski(k9_relat_1(k6_relat_1(A_74),A_74),A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_196])).

tff(c_46,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_147,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(A_65,C_66)
      | ~ r1_tarski(B_67,C_66)
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_155,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,'#skF_2')
      | ~ r1_tarski(A_65,k10_relat_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_147])).

tff(c_220,plain,(
    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),k10_relat_1('#skF_1','#skF_3')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_206,c_155])).

tff(c_680,plain,(
    ! [A_112,C_113,B_114] :
      ( r1_tarski(A_112,k10_relat_1(C_113,B_114))
      | ~ r1_tarski(k9_relat_1(C_113,A_112),B_114)
      | ~ r1_tarski(A_112,k1_relat_1(C_113))
      | ~ v1_funct_1(C_113)
      | ~ v1_relat_1(C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_692,plain,
    ( r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),'#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),k1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3'))))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_220,c_680])).

tff(c_712,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_6,c_26,c_308,c_692])).

tff(c_725,plain,
    ( r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_712])).

tff(c_729,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_725])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_733,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ r1_tarski(k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3'),k10_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_729,c_2])).

tff(c_737,plain,(
    ~ r1_tarski(k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3'),k10_relat_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_733])).

tff(c_740,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_737])).

tff(c_743,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_740])).

tff(c_767,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_743])).

tff(c_770,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_767])).

tff(c_774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_770])).

tff(c_775,plain,(
    ~ r1_tarski(k7_relat_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_743])).

tff(c_779,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_775])).

tff(c_783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_779])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:06:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.48  
% 3.04/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.48  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.04/1.48  
% 3.04/1.48  %Foreground sorts:
% 3.04/1.48  
% 3.04/1.48  
% 3.04/1.48  %Background operators:
% 3.04/1.48  
% 3.04/1.48  
% 3.04/1.48  %Foreground operators:
% 3.04/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.04/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.04/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.04/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.04/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.04/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.04/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.04/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.04/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.04/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.04/1.48  
% 3.04/1.50  tff(f_113, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.04/1.50  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.04/1.50  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.04/1.50  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t179_relat_1)).
% 3.04/1.50  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 3.04/1.50  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.04/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.04/1.50  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.04/1.50  tff(f_103, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.04/1.50  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.04/1.50  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.04/1.50  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 3.04/1.50  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.04/1.50  tff(f_101, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 3.04/1.50  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.04/1.50  tff(c_30, plain, (![B_29, A_28]: (r1_tarski(k7_relat_1(B_29, A_28), B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.04/1.50  tff(c_18, plain, (![A_17, B_18]: (v1_relat_1(k7_relat_1(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.04/1.50  tff(c_22, plain, (![B_21, A_20, C_23]: (r1_tarski(k10_relat_1(B_21, A_20), k10_relat_1(C_23, A_20)) | ~r1_tarski(B_21, C_23) | ~v1_relat_1(C_23) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.04/1.50  tff(c_44, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.04/1.50  tff(c_36, plain, (![A_31, C_33, B_32]: (k3_xboole_0(A_31, k10_relat_1(C_33, B_32))=k10_relat_1(k7_relat_1(C_33, A_31), B_32) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.04/1.50  tff(c_32, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.04/1.50  tff(c_34, plain, (![A_30]: (v1_funct_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.04/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.04/1.50  tff(c_26, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.04/1.50  tff(c_42, plain, (![B_40, A_39]: (k5_relat_1(k6_relat_1(B_40), k6_relat_1(A_39))=k6_relat_1(k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.04/1.50  tff(c_263, plain, (![A_84, B_85]: (k10_relat_1(A_84, k1_relat_1(B_85))=k1_relat_1(k5_relat_1(A_84, B_85)) | ~v1_relat_1(B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.04/1.50  tff(c_283, plain, (![A_84, A_27]: (k1_relat_1(k5_relat_1(A_84, k6_relat_1(A_27)))=k10_relat_1(A_84, A_27) | ~v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_26, c_263])).
% 3.04/1.50  tff(c_292, plain, (![A_86, A_87]: (k1_relat_1(k5_relat_1(A_86, k6_relat_1(A_87)))=k10_relat_1(A_86, A_87) | ~v1_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_283])).
% 3.04/1.50  tff(c_304, plain, (![A_39, B_40]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_39, B_40)))=k10_relat_1(k6_relat_1(B_40), A_39) | ~v1_relat_1(k6_relat_1(B_40)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_292])).
% 3.04/1.50  tff(c_308, plain, (![B_40, A_39]: (k10_relat_1(k6_relat_1(B_40), A_39)=k3_xboole_0(A_39, B_40))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_304])).
% 3.04/1.50  tff(c_28, plain, (![A_27]: (k2_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.04/1.50  tff(c_93, plain, (![A_56]: (k10_relat_1(A_56, k2_relat_1(A_56))=k1_relat_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.04/1.50  tff(c_102, plain, (![A_27]: (k10_relat_1(k6_relat_1(A_27), A_27)=k1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_93])).
% 3.04/1.50  tff(c_106, plain, (![A_27]: (k10_relat_1(k6_relat_1(A_27), A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_102])).
% 3.04/1.50  tff(c_181, plain, (![B_72, A_73]: (r1_tarski(k9_relat_1(B_72, k10_relat_1(B_72, A_73)), A_73) | ~v1_funct_1(B_72) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.04/1.50  tff(c_196, plain, (![A_27]: (r1_tarski(k9_relat_1(k6_relat_1(A_27), A_27), A_27) | ~v1_funct_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_181])).
% 3.04/1.50  tff(c_206, plain, (![A_74]: (r1_tarski(k9_relat_1(k6_relat_1(A_74), A_74), A_74))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_196])).
% 3.04/1.50  tff(c_46, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.04/1.50  tff(c_147, plain, (![A_65, C_66, B_67]: (r1_tarski(A_65, C_66) | ~r1_tarski(B_67, C_66) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.04/1.50  tff(c_155, plain, (![A_65]: (r1_tarski(A_65, '#skF_2') | ~r1_tarski(A_65, k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_46, c_147])).
% 3.04/1.50  tff(c_220, plain, (r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), k10_relat_1('#skF_1', '#skF_3')), '#skF_2')), inference(resolution, [status(thm)], [c_206, c_155])).
% 3.04/1.50  tff(c_680, plain, (![A_112, C_113, B_114]: (r1_tarski(A_112, k10_relat_1(C_113, B_114)) | ~r1_tarski(k9_relat_1(C_113, A_112), B_114) | ~r1_tarski(A_112, k1_relat_1(C_113)) | ~v1_funct_1(C_113) | ~v1_relat_1(C_113))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.04/1.50  tff(c_692, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))) | ~v1_funct_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3'))) | ~v1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_220, c_680])).
% 3.04/1.50  tff(c_712, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_6, c_26, c_308, c_692])).
% 3.04/1.50  tff(c_725, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_712])).
% 3.04/1.50  tff(c_729, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_725])).
% 3.04/1.50  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.04/1.50  tff(c_733, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~r1_tarski(k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3'), k10_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_729, c_2])).
% 3.04/1.50  tff(c_737, plain, (~r1_tarski(k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3'), k10_relat_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_733])).
% 3.04/1.50  tff(c_740, plain, (~r1_tarski(k7_relat_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_737])).
% 3.04/1.50  tff(c_743, plain, (~r1_tarski(k7_relat_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_740])).
% 3.04/1.50  tff(c_767, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_743])).
% 3.04/1.50  tff(c_770, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_767])).
% 3.04/1.50  tff(c_774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_770])).
% 3.04/1.50  tff(c_775, plain, (~r1_tarski(k7_relat_1('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_743])).
% 3.04/1.50  tff(c_779, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_30, c_775])).
% 3.04/1.50  tff(c_783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_779])).
% 3.04/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.50  
% 3.04/1.50  Inference rules
% 3.04/1.50  ----------------------
% 3.04/1.50  #Ref     : 0
% 3.04/1.50  #Sup     : 160
% 3.04/1.50  #Fact    : 0
% 3.04/1.50  #Define  : 0
% 3.04/1.50  #Split   : 4
% 3.04/1.50  #Chain   : 0
% 3.04/1.50  #Close   : 0
% 3.04/1.50  
% 3.04/1.50  Ordering : KBO
% 3.04/1.50  
% 3.04/1.50  Simplification rules
% 3.04/1.50  ----------------------
% 3.04/1.50  #Subsume      : 3
% 3.04/1.50  #Demod        : 101
% 3.04/1.50  #Tautology    : 55
% 3.04/1.50  #SimpNegUnit  : 1
% 3.04/1.50  #BackRed      : 0
% 3.04/1.50  
% 3.04/1.50  #Partial instantiations: 0
% 3.04/1.50  #Strategies tried      : 1
% 3.04/1.50  
% 3.04/1.50  Timing (in seconds)
% 3.04/1.50  ----------------------
% 3.04/1.51  Preprocessing        : 0.34
% 3.04/1.51  Parsing              : 0.18
% 3.04/1.51  CNF conversion       : 0.02
% 3.04/1.51  Main loop            : 0.38
% 3.04/1.51  Inferencing          : 0.13
% 3.04/1.51  Reduction            : 0.12
% 3.04/1.51  Demodulation         : 0.09
% 3.04/1.51  BG Simplification    : 0.02
% 3.04/1.51  Subsumption          : 0.08
% 3.04/1.51  Abstraction          : 0.02
% 3.04/1.51  MUC search           : 0.00
% 3.04/1.51  Cooper               : 0.00
% 3.04/1.51  Total                : 0.76
% 3.04/1.51  Index Insertion      : 0.00
% 3.04/1.51  Index Deletion       : 0.00
% 3.04/1.51  Index Matching       : 0.00
% 3.04/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
