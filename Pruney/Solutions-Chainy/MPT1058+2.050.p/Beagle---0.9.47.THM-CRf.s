%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:28 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 115 expanded)
%              Number of leaves         :   31 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  101 ( 182 expanded)
%              Number of equality atoms :   24 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_82,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_34,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [A_16] : v1_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [B_26,A_25] : k5_relat_1(k6_relat_1(B_26),k6_relat_1(A_25)) = k6_relat_1(k3_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_214,plain,(
    ! [A_63,B_64] :
      ( k10_relat_1(A_63,k1_relat_1(B_64)) = k1_relat_1(k5_relat_1(A_63,B_64))
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_256,plain,(
    ! [A_63,A_15] :
      ( k1_relat_1(k5_relat_1(A_63,k6_relat_1(A_15))) = k10_relat_1(A_63,A_15)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_214])).

tff(c_671,plain,(
    ! [A_100,A_101] :
      ( k1_relat_1(k5_relat_1(A_100,k6_relat_1(A_101))) = k10_relat_1(A_100,A_101)
      | ~ v1_relat_1(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_256])).

tff(c_694,plain,(
    ! [A_25,B_26] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_25,B_26))) = k10_relat_1(k6_relat_1(B_26),A_25)
      | ~ v1_relat_1(k6_relat_1(B_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_671])).

tff(c_702,plain,(
    ! [B_26,A_25] : k10_relat_1(k6_relat_1(B_26),A_25) = k3_xboole_0(A_25,B_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_694])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_715,plain,(
    ! [B_102,A_103] : k10_relat_1(k6_relat_1(B_102),A_103) = k3_xboole_0(A_103,B_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_694])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k9_relat_1(B_21,k10_relat_1(B_21,A_20)),A_20)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_731,plain,(
    ! [B_102,A_103] :
      ( r1_tarski(k9_relat_1(k6_relat_1(B_102),k3_xboole_0(A_103,B_102)),A_103)
      | ~ v1_funct_1(k6_relat_1(B_102))
      | ~ v1_relat_1(k6_relat_1(B_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_28])).

tff(c_756,plain,(
    ! [B_104,A_105] : r1_tarski(k9_relat_1(k6_relat_1(B_104),k3_xboole_0(A_105,B_104)),A_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_731])).

tff(c_784,plain,(
    ! [A_106] : r1_tarski(k9_relat_1(k6_relat_1(A_106),A_106),A_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_756])).

tff(c_36,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_113,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_124,plain,(
    ! [A_45] :
      ( r1_tarski(A_45,'#skF_2')
      | ~ r1_tarski(A_45,k10_relat_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_36,c_113])).

tff(c_803,plain,(
    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),k10_relat_1('#skF_1','#skF_3')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_784,c_124])).

tff(c_30,plain,(
    ! [A_22,C_24,B_23] :
      ( r1_tarski(A_22,k10_relat_1(C_24,B_23))
      | ~ r1_tarski(k9_relat_1(C_24,A_22),B_23)
      | ~ r1_tarski(A_22,k1_relat_1(C_24))
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_931,plain,
    ( r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),'#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),k1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3'))))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_803,c_30])).

tff(c_938,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_8,c_18,c_702,c_931])).

tff(c_81,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(k10_relat_1(B_37,A_38),k1_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [A_15,A_38] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_15),A_38),A_15)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_81])).

tff(c_86,plain,(
    ! [A_15,A_38] : r1_tarski(k10_relat_1(k6_relat_1(A_15),A_38),A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_84])).

tff(c_247,plain,(
    ! [A_15,B_64] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_15),B_64)),A_15)
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_86])).

tff(c_273,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_65),B_66)),A_65)
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_247])).

tff(c_292,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_25,B_26))),B_26)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_273])).

tff(c_300,plain,(
    ! [A_67,B_68] : r1_tarski(k3_xboole_0(A_67,B_68),B_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_292])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_324,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = B_68
      | ~ r1_tarski(B_68,k3_xboole_0(A_67,B_68)) ) ),
    inference(resolution,[status(thm)],[c_300,c_4])).

tff(c_983,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_938,c_324])).

tff(c_26,plain,(
    ! [A_17,C_19,B_18] :
      ( k3_xboole_0(A_17,k10_relat_1(C_19,B_18)) = k10_relat_1(k7_relat_1(C_19,A_17),B_18)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1008,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_983,c_26])).

tff(c_1033,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1008])).

tff(c_1035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1033])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:44:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.53  
% 3.08/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.53  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.20/1.53  
% 3.20/1.53  %Foreground sorts:
% 3.20/1.53  
% 3.20/1.53  
% 3.20/1.53  %Background operators:
% 3.20/1.53  
% 3.20/1.53  
% 3.20/1.53  %Foreground operators:
% 3.20/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.20/1.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.20/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.20/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.20/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.20/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.20/1.53  
% 3.20/1.55  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.20/1.55  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.20/1.55  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.20/1.55  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.20/1.55  tff(f_82, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.20/1.55  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.20/1.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.20/1.55  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 3.20/1.55  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.20/1.55  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 3.20/1.55  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 3.20/1.55  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.20/1.55  tff(c_34, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.20/1.55  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.20/1.55  tff(c_22, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.55  tff(c_24, plain, (![A_16]: (v1_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.55  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.20/1.55  tff(c_18, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.20/1.55  tff(c_32, plain, (![B_26, A_25]: (k5_relat_1(k6_relat_1(B_26), k6_relat_1(A_25))=k6_relat_1(k3_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.20/1.55  tff(c_214, plain, (![A_63, B_64]: (k10_relat_1(A_63, k1_relat_1(B_64))=k1_relat_1(k5_relat_1(A_63, B_64)) | ~v1_relat_1(B_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.20/1.55  tff(c_256, plain, (![A_63, A_15]: (k1_relat_1(k5_relat_1(A_63, k6_relat_1(A_15)))=k10_relat_1(A_63, A_15) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(A_63))), inference(superposition, [status(thm), theory('equality')], [c_18, c_214])).
% 3.20/1.55  tff(c_671, plain, (![A_100, A_101]: (k1_relat_1(k5_relat_1(A_100, k6_relat_1(A_101)))=k10_relat_1(A_100, A_101) | ~v1_relat_1(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_256])).
% 3.20/1.55  tff(c_694, plain, (![A_25, B_26]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_25, B_26)))=k10_relat_1(k6_relat_1(B_26), A_25) | ~v1_relat_1(k6_relat_1(B_26)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_671])).
% 3.20/1.55  tff(c_702, plain, (![B_26, A_25]: (k10_relat_1(k6_relat_1(B_26), A_25)=k3_xboole_0(A_25, B_26))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_694])).
% 3.20/1.55  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.55  tff(c_715, plain, (![B_102, A_103]: (k10_relat_1(k6_relat_1(B_102), A_103)=k3_xboole_0(A_103, B_102))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_694])).
% 3.20/1.55  tff(c_28, plain, (![B_21, A_20]: (r1_tarski(k9_relat_1(B_21, k10_relat_1(B_21, A_20)), A_20) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.20/1.55  tff(c_731, plain, (![B_102, A_103]: (r1_tarski(k9_relat_1(k6_relat_1(B_102), k3_xboole_0(A_103, B_102)), A_103) | ~v1_funct_1(k6_relat_1(B_102)) | ~v1_relat_1(k6_relat_1(B_102)))), inference(superposition, [status(thm), theory('equality')], [c_715, c_28])).
% 3.20/1.55  tff(c_756, plain, (![B_104, A_105]: (r1_tarski(k9_relat_1(k6_relat_1(B_104), k3_xboole_0(A_105, B_104)), A_105))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_731])).
% 3.20/1.55  tff(c_784, plain, (![A_106]: (r1_tarski(k9_relat_1(k6_relat_1(A_106), A_106), A_106))), inference(superposition, [status(thm), theory('equality')], [c_2, c_756])).
% 3.20/1.55  tff(c_36, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.20/1.55  tff(c_113, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.55  tff(c_124, plain, (![A_45]: (r1_tarski(A_45, '#skF_2') | ~r1_tarski(A_45, k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_36, c_113])).
% 3.20/1.55  tff(c_803, plain, (r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), k10_relat_1('#skF_1', '#skF_3')), '#skF_2')), inference(resolution, [status(thm)], [c_784, c_124])).
% 3.20/1.55  tff(c_30, plain, (![A_22, C_24, B_23]: (r1_tarski(A_22, k10_relat_1(C_24, B_23)) | ~r1_tarski(k9_relat_1(C_24, A_22), B_23) | ~r1_tarski(A_22, k1_relat_1(C_24)) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.55  tff(c_931, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))) | ~v1_funct_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3'))) | ~v1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_803, c_30])).
% 3.20/1.55  tff(c_938, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_8, c_18, c_702, c_931])).
% 3.20/1.55  tff(c_81, plain, (![B_37, A_38]: (r1_tarski(k10_relat_1(B_37, A_38), k1_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.55  tff(c_84, plain, (![A_15, A_38]: (r1_tarski(k10_relat_1(k6_relat_1(A_15), A_38), A_15) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_81])).
% 3.20/1.55  tff(c_86, plain, (![A_15, A_38]: (r1_tarski(k10_relat_1(k6_relat_1(A_15), A_38), A_15))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_84])).
% 3.20/1.55  tff(c_247, plain, (![A_15, B_64]: (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_15), B_64)), A_15) | ~v1_relat_1(B_64) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_214, c_86])).
% 3.20/1.55  tff(c_273, plain, (![A_65, B_66]: (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_65), B_66)), A_65) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_247])).
% 3.20/1.55  tff(c_292, plain, (![A_25, B_26]: (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_25, B_26))), B_26) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_273])).
% 3.20/1.55  tff(c_300, plain, (![A_67, B_68]: (r1_tarski(k3_xboole_0(A_67, B_68), B_68))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_292])).
% 3.20/1.55  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.20/1.55  tff(c_324, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=B_68 | ~r1_tarski(B_68, k3_xboole_0(A_67, B_68)))), inference(resolution, [status(thm)], [c_300, c_4])).
% 3.20/1.55  tff(c_983, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_938, c_324])).
% 3.20/1.55  tff(c_26, plain, (![A_17, C_19, B_18]: (k3_xboole_0(A_17, k10_relat_1(C_19, B_18))=k10_relat_1(k7_relat_1(C_19, A_17), B_18) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.20/1.55  tff(c_1008, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_983, c_26])).
% 3.20/1.55  tff(c_1033, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1008])).
% 3.20/1.55  tff(c_1035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1033])).
% 3.20/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.55  
% 3.20/1.55  Inference rules
% 3.20/1.55  ----------------------
% 3.20/1.55  #Ref     : 0
% 3.20/1.55  #Sup     : 219
% 3.20/1.55  #Fact    : 0
% 3.20/1.55  #Define  : 0
% 3.20/1.55  #Split   : 1
% 3.20/1.55  #Chain   : 0
% 3.20/1.55  #Close   : 0
% 3.20/1.55  
% 3.20/1.55  Ordering : KBO
% 3.20/1.55  
% 3.20/1.55  Simplification rules
% 3.20/1.55  ----------------------
% 3.20/1.55  #Subsume      : 4
% 3.20/1.55  #Demod        : 108
% 3.20/1.55  #Tautology    : 61
% 3.20/1.55  #SimpNegUnit  : 1
% 3.20/1.55  #BackRed      : 8
% 3.20/1.55  
% 3.20/1.55  #Partial instantiations: 0
% 3.20/1.55  #Strategies tried      : 1
% 3.20/1.55  
% 3.20/1.55  Timing (in seconds)
% 3.20/1.55  ----------------------
% 3.20/1.55  Preprocessing        : 0.33
% 3.20/1.55  Parsing              : 0.18
% 3.20/1.55  CNF conversion       : 0.02
% 3.20/1.55  Main loop            : 0.36
% 3.20/1.55  Inferencing          : 0.13
% 3.20/1.55  Reduction            : 0.12
% 3.20/1.55  Demodulation         : 0.09
% 3.20/1.55  BG Simplification    : 0.02
% 3.20/1.55  Subsumption          : 0.08
% 3.20/1.55  Abstraction          : 0.02
% 3.20/1.55  MUC search           : 0.00
% 3.20/1.55  Cooper               : 0.00
% 3.20/1.55  Total                : 0.73
% 3.20/1.55  Index Insertion      : 0.00
% 3.20/1.55  Index Deletion       : 0.00
% 3.20/1.55  Index Matching       : 0.00
% 3.20/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
