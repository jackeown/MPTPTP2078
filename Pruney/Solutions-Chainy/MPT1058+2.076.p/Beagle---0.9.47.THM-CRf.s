%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:32 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 249 expanded)
%              Number of leaves         :   28 ( 104 expanded)
%              Depth                    :   19
%              Number of atoms          :  125 ( 447 expanded)
%              Number of equality atoms :   46 ( 174 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(c_28,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_57,plain,(
    ! [A_26] :
      ( k7_relat_1(A_26,k1_relat_1(A_26)) = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_66,plain,(
    ! [A_7] :
      ( k7_relat_1(k6_relat_1(A_7),A_7) = k6_relat_1(A_7)
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_57])).

tff(c_70,plain,(
    ! [A_7] : k7_relat_1(k6_relat_1(A_7),A_7) = k6_relat_1(A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_66])).

tff(c_80,plain,(
    ! [B_28,A_29] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_28,A_29)),A_29)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_83,plain,(
    ! [A_7] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_7)),A_7)
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_80])).

tff(c_88,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_83])).

tff(c_8,plain,(
    ! [A_7] : k2_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_90,plain,(
    ! [B_31,A_32] :
      ( k2_relat_1(k7_relat_1(B_31,A_32)) = k9_relat_1(B_31,A_32)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ! [A_7] :
      ( k9_relat_1(k6_relat_1(A_7),A_7) = k2_relat_1(k6_relat_1(A_7))
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_90])).

tff(c_106,plain,(
    ! [A_7] : k9_relat_1(k6_relat_1(A_7),A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8,c_99])).

tff(c_20,plain,(
    ! [A_15] : v1_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_126,plain,(
    ! [B_36,A_37] :
      ( k7_relat_1(B_36,A_37) = B_36
      | ~ r1_tarski(k1_relat_1(B_36),A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_136,plain,(
    ! [A_7,A_37] :
      ( k7_relat_1(k6_relat_1(A_7),A_37) = k6_relat_1(A_7)
      | ~ r1_tarski(A_7,A_37)
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_126])).

tff(c_140,plain,(
    ! [A_7,A_37] :
      ( k7_relat_1(k6_relat_1(A_7),A_37) = k6_relat_1(A_7)
      | ~ r1_tarski(A_7,A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_136])).

tff(c_16,plain,(
    ! [A_14] :
      ( k7_relat_1(A_14,k1_relat_1(A_14)) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    ! [A_14] :
      ( k9_relat_1(A_14,k1_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_90])).

tff(c_314,plain,(
    ! [B_53,A_54] :
      ( k10_relat_1(B_53,k9_relat_1(B_53,A_54)) = A_54
      | ~ v2_funct_1(B_53)
      | ~ r1_tarski(A_54,k1_relat_1(B_53))
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_322,plain,(
    ! [A_7,A_54] :
      ( k10_relat_1(k6_relat_1(A_7),k9_relat_1(k6_relat_1(A_7),A_54)) = A_54
      | ~ v2_funct_1(k6_relat_1(A_7))
      | ~ r1_tarski(A_54,A_7)
      | ~ v1_funct_1(k6_relat_1(A_7))
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_314])).

tff(c_327,plain,(
    ! [A_55,A_56] :
      ( k10_relat_1(k6_relat_1(A_55),k9_relat_1(k6_relat_1(A_55),A_56)) = A_56
      | ~ r1_tarski(A_56,A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_24,c_322])).

tff(c_340,plain,(
    ! [A_55] :
      ( k10_relat_1(k6_relat_1(A_55),k2_relat_1(k6_relat_1(A_55))) = k1_relat_1(k6_relat_1(A_55))
      | ~ r1_tarski(k1_relat_1(k6_relat_1(A_55)),A_55)
      | ~ v1_relat_1(k6_relat_1(A_55))
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_327])).

tff(c_352,plain,(
    ! [A_55] : k10_relat_1(k6_relat_1(A_55),A_55) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_88,c_6,c_6,c_8,c_340])).

tff(c_355,plain,(
    ! [A_57] : k10_relat_1(k6_relat_1(A_57),A_57) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_88,c_6,c_6,c_8,c_340])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_187,plain,(
    ! [B_40,C_41,A_42] :
      ( k10_relat_1(k5_relat_1(B_40,C_41),A_42) = k10_relat_1(B_40,k10_relat_1(C_41,A_42))
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_196,plain,(
    ! [A_10,B_11,A_42] :
      ( k10_relat_1(k6_relat_1(A_10),k10_relat_1(B_11,A_42)) = k10_relat_1(k7_relat_1(B_11,A_10),A_42)
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_187])).

tff(c_200,plain,(
    ! [A_10,B_11,A_42] :
      ( k10_relat_1(k6_relat_1(A_10),k10_relat_1(B_11,A_42)) = k10_relat_1(k7_relat_1(B_11,A_10),A_42)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_196])).

tff(c_361,plain,(
    ! [A_57,A_10] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_57),A_10),A_57) = k10_relat_1(k6_relat_1(A_10),A_57)
      | ~ v1_relat_1(k6_relat_1(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_200])).

tff(c_424,plain,(
    ! [A_59,A_60] : k10_relat_1(k7_relat_1(k6_relat_1(A_59),A_60),A_59) = k10_relat_1(k6_relat_1(A_60),A_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_361])).

tff(c_436,plain,(
    ! [A_7,A_37] :
      ( k10_relat_1(k6_relat_1(A_7),A_7) = k10_relat_1(k6_relat_1(A_37),A_7)
      | ~ r1_tarski(A_7,A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_424])).

tff(c_450,plain,(
    ! [A_61,A_62] :
      ( k10_relat_1(k6_relat_1(A_61),A_62) = A_62
      | ~ r1_tarski(A_62,A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_436])).

tff(c_468,plain,(
    ! [A_61,A_10,A_62] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_61),A_10),A_62) = k10_relat_1(k6_relat_1(A_10),A_62)
      | ~ v1_relat_1(k6_relat_1(A_61))
      | ~ r1_tarski(A_62,A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_200])).

tff(c_854,plain,(
    ! [A_76,A_77,A_78] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_76),A_77),A_78) = k10_relat_1(k6_relat_1(A_77),A_78)
      | ~ r1_tarski(A_78,A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_468])).

tff(c_1462,plain,(
    ! [A_99,A_100,A_101] :
      ( k10_relat_1(k6_relat_1(A_99),A_100) = k10_relat_1(k6_relat_1(A_101),A_100)
      | ~ r1_tarski(A_100,A_99)
      | ~ r1_tarski(A_99,A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_854])).

tff(c_1659,plain,(
    ! [A_106] :
      ( k10_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),A_106) = k10_relat_1(k6_relat_1('#skF_2'),A_106)
      | ~ r1_tarski(A_106,k10_relat_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_1462])).

tff(c_323,plain,(
    ! [B_53] :
      ( k10_relat_1(B_53,k9_relat_1(B_53,k1_relat_1(B_53))) = k1_relat_1(B_53)
      | ~ v2_funct_1(B_53)
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_88,c_314])).

tff(c_1694,plain,
    ( k10_relat_1(k6_relat_1('#skF_2'),k9_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),k1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3'))))) = k1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))
    | ~ v2_funct_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),k1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))),k10_relat_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1659,c_323])).

tff(c_1759,plain,(
    k10_relat_1(k6_relat_1('#skF_2'),k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_106,c_6,c_22,c_20,c_24,c_106,c_6,c_6,c_1694])).

tff(c_1789,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1759,c_200])).

tff(c_1813,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1789])).

tff(c_1815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1813])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/2.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/2.87  
% 4.92/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/2.87  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.92/2.87  
% 4.92/2.87  %Foreground sorts:
% 4.92/2.87  
% 4.92/2.87  
% 4.92/2.87  %Background operators:
% 4.92/2.87  
% 4.92/2.87  
% 4.92/2.87  %Foreground operators:
% 4.92/2.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.92/2.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.92/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/2.87  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.92/2.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.92/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.92/2.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.92/2.87  tff('#skF_2', type, '#skF_2': $i).
% 4.92/2.87  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.92/2.87  tff('#skF_3', type, '#skF_3': $i).
% 4.92/2.87  tff('#skF_1', type, '#skF_1': $i).
% 4.92/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/2.87  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.92/2.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.92/2.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.92/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/2.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.92/2.87  
% 5.34/2.91  tff(f_86, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 5.34/2.91  tff(f_66, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.34/2.91  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.34/2.91  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 5.34/2.91  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 5.34/2.91  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.34/2.91  tff(f_62, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.34/2.91  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 5.34/2.91  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 5.34/2.91  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 5.34/2.91  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 5.34/2.91  tff(c_28, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.34/2.91  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.34/2.91  tff(c_22, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.34/2.91  tff(c_6, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.34/2.91  tff(c_57, plain, (![A_26]: (k7_relat_1(A_26, k1_relat_1(A_26))=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.34/2.91  tff(c_66, plain, (![A_7]: (k7_relat_1(k6_relat_1(A_7), A_7)=k6_relat_1(A_7) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_57])).
% 5.34/2.91  tff(c_70, plain, (![A_7]: (k7_relat_1(k6_relat_1(A_7), A_7)=k6_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_66])).
% 5.34/2.91  tff(c_80, plain, (![B_28, A_29]: (r1_tarski(k1_relat_1(k7_relat_1(B_28, A_29)), A_29) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.34/2.91  tff(c_83, plain, (![A_7]: (r1_tarski(k1_relat_1(k6_relat_1(A_7)), A_7) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_80])).
% 5.34/2.91  tff(c_88, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_83])).
% 5.34/2.91  tff(c_8, plain, (![A_7]: (k2_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.34/2.91  tff(c_90, plain, (![B_31, A_32]: (k2_relat_1(k7_relat_1(B_31, A_32))=k9_relat_1(B_31, A_32) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.34/2.91  tff(c_99, plain, (![A_7]: (k9_relat_1(k6_relat_1(A_7), A_7)=k2_relat_1(k6_relat_1(A_7)) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_90])).
% 5.34/2.91  tff(c_106, plain, (![A_7]: (k9_relat_1(k6_relat_1(A_7), A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8, c_99])).
% 5.43/2.91  tff(c_20, plain, (![A_15]: (v1_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.43/2.91  tff(c_24, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.43/2.91  tff(c_30, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.43/2.91  tff(c_126, plain, (![B_36, A_37]: (k7_relat_1(B_36, A_37)=B_36 | ~r1_tarski(k1_relat_1(B_36), A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.43/2.91  tff(c_136, plain, (![A_7, A_37]: (k7_relat_1(k6_relat_1(A_7), A_37)=k6_relat_1(A_7) | ~r1_tarski(A_7, A_37) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_126])).
% 5.43/2.91  tff(c_140, plain, (![A_7, A_37]: (k7_relat_1(k6_relat_1(A_7), A_37)=k6_relat_1(A_7) | ~r1_tarski(A_7, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_136])).
% 5.43/2.91  tff(c_16, plain, (![A_14]: (k7_relat_1(A_14, k1_relat_1(A_14))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.43/2.91  tff(c_102, plain, (![A_14]: (k9_relat_1(A_14, k1_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_90])).
% 5.43/2.91  tff(c_314, plain, (![B_53, A_54]: (k10_relat_1(B_53, k9_relat_1(B_53, A_54))=A_54 | ~v2_funct_1(B_53) | ~r1_tarski(A_54, k1_relat_1(B_53)) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.43/2.91  tff(c_322, plain, (![A_7, A_54]: (k10_relat_1(k6_relat_1(A_7), k9_relat_1(k6_relat_1(A_7), A_54))=A_54 | ~v2_funct_1(k6_relat_1(A_7)) | ~r1_tarski(A_54, A_7) | ~v1_funct_1(k6_relat_1(A_7)) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_314])).
% 5.43/2.91  tff(c_327, plain, (![A_55, A_56]: (k10_relat_1(k6_relat_1(A_55), k9_relat_1(k6_relat_1(A_55), A_56))=A_56 | ~r1_tarski(A_56, A_55))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_24, c_322])).
% 5.43/2.91  tff(c_340, plain, (![A_55]: (k10_relat_1(k6_relat_1(A_55), k2_relat_1(k6_relat_1(A_55)))=k1_relat_1(k6_relat_1(A_55)) | ~r1_tarski(k1_relat_1(k6_relat_1(A_55)), A_55) | ~v1_relat_1(k6_relat_1(A_55)) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_327])).
% 5.43/2.91  tff(c_352, plain, (![A_55]: (k10_relat_1(k6_relat_1(A_55), A_55)=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_88, c_6, c_6, c_8, c_340])).
% 5.43/2.91  tff(c_355, plain, (![A_57]: (k10_relat_1(k6_relat_1(A_57), A_57)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_88, c_6, c_6, c_8, c_340])).
% 5.43/2.91  tff(c_12, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.43/2.91  tff(c_187, plain, (![B_40, C_41, A_42]: (k10_relat_1(k5_relat_1(B_40, C_41), A_42)=k10_relat_1(B_40, k10_relat_1(C_41, A_42)) | ~v1_relat_1(C_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.43/2.91  tff(c_196, plain, (![A_10, B_11, A_42]: (k10_relat_1(k6_relat_1(A_10), k10_relat_1(B_11, A_42))=k10_relat_1(k7_relat_1(B_11, A_10), A_42) | ~v1_relat_1(B_11) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(B_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_187])).
% 5.43/2.91  tff(c_200, plain, (![A_10, B_11, A_42]: (k10_relat_1(k6_relat_1(A_10), k10_relat_1(B_11, A_42))=k10_relat_1(k7_relat_1(B_11, A_10), A_42) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_196])).
% 5.43/2.91  tff(c_361, plain, (![A_57, A_10]: (k10_relat_1(k7_relat_1(k6_relat_1(A_57), A_10), A_57)=k10_relat_1(k6_relat_1(A_10), A_57) | ~v1_relat_1(k6_relat_1(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_355, c_200])).
% 5.43/2.91  tff(c_424, plain, (![A_59, A_60]: (k10_relat_1(k7_relat_1(k6_relat_1(A_59), A_60), A_59)=k10_relat_1(k6_relat_1(A_60), A_59))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_361])).
% 5.43/2.91  tff(c_436, plain, (![A_7, A_37]: (k10_relat_1(k6_relat_1(A_7), A_7)=k10_relat_1(k6_relat_1(A_37), A_7) | ~r1_tarski(A_7, A_37))), inference(superposition, [status(thm), theory('equality')], [c_140, c_424])).
% 5.43/2.91  tff(c_450, plain, (![A_61, A_62]: (k10_relat_1(k6_relat_1(A_61), A_62)=A_62 | ~r1_tarski(A_62, A_61))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_436])).
% 5.43/2.91  tff(c_468, plain, (![A_61, A_10, A_62]: (k10_relat_1(k7_relat_1(k6_relat_1(A_61), A_10), A_62)=k10_relat_1(k6_relat_1(A_10), A_62) | ~v1_relat_1(k6_relat_1(A_61)) | ~r1_tarski(A_62, A_61))), inference(superposition, [status(thm), theory('equality')], [c_450, c_200])).
% 5.43/2.91  tff(c_854, plain, (![A_76, A_77, A_78]: (k10_relat_1(k7_relat_1(k6_relat_1(A_76), A_77), A_78)=k10_relat_1(k6_relat_1(A_77), A_78) | ~r1_tarski(A_78, A_76))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_468])).
% 5.43/2.91  tff(c_1462, plain, (![A_99, A_100, A_101]: (k10_relat_1(k6_relat_1(A_99), A_100)=k10_relat_1(k6_relat_1(A_101), A_100) | ~r1_tarski(A_100, A_99) | ~r1_tarski(A_99, A_101))), inference(superposition, [status(thm), theory('equality')], [c_140, c_854])).
% 5.43/2.91  tff(c_1659, plain, (![A_106]: (k10_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), A_106)=k10_relat_1(k6_relat_1('#skF_2'), A_106) | ~r1_tarski(A_106, k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_30, c_1462])).
% 5.43/2.91  tff(c_323, plain, (![B_53]: (k10_relat_1(B_53, k9_relat_1(B_53, k1_relat_1(B_53)))=k1_relat_1(B_53) | ~v2_funct_1(B_53) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_88, c_314])).
% 5.43/2.91  tff(c_1694, plain, (k10_relat_1(k6_relat_1('#skF_2'), k9_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), k1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))))=k1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3'))) | ~v2_funct_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3'))) | ~v1_funct_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3'))) | ~v1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3'))) | ~r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), k1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))), k10_relat_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1659, c_323])).
% 5.43/2.91  tff(c_1759, plain, (k10_relat_1(k6_relat_1('#skF_2'), k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_106, c_6, c_22, c_20, c_24, c_106, c_6, c_6, c_1694])).
% 5.43/2.91  tff(c_1789, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1759, c_200])).
% 5.43/2.91  tff(c_1813, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1789])).
% 5.43/2.91  tff(c_1815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1813])).
% 5.43/2.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.91  
% 5.43/2.91  Inference rules
% 5.43/2.91  ----------------------
% 5.43/2.91  #Ref     : 0
% 5.43/2.91  #Sup     : 399
% 5.43/2.91  #Fact    : 0
% 5.43/2.91  #Define  : 0
% 5.43/2.91  #Split   : 1
% 5.43/2.91  #Chain   : 0
% 5.43/2.91  #Close   : 0
% 5.43/2.91  
% 5.43/2.91  Ordering : KBO
% 5.43/2.91  
% 5.43/2.91  Simplification rules
% 5.43/2.91  ----------------------
% 5.43/2.91  #Subsume      : 44
% 5.43/2.91  #Demod        : 565
% 5.43/2.91  #Tautology    : 170
% 5.43/2.91  #SimpNegUnit  : 1
% 5.43/2.91  #BackRed      : 0
% 5.43/2.91  
% 5.43/2.91  #Partial instantiations: 0
% 5.43/2.91  #Strategies tried      : 1
% 5.43/2.91  
% 5.43/2.91  Timing (in seconds)
% 5.43/2.91  ----------------------
% 5.44/2.93  Preprocessing        : 0.60
% 5.44/2.93  Parsing              : 0.35
% 5.44/2.93  CNF conversion       : 0.04
% 5.44/2.93  Main loop            : 1.20
% 5.44/2.93  Inferencing          : 0.47
% 5.44/2.93  Reduction            : 0.40
% 5.44/2.93  Demodulation         : 0.29
% 5.44/2.93  BG Simplification    : 0.07
% 5.44/2.93  Subsumption          : 0.20
% 5.44/2.93  Abstraction          : 0.06
% 5.44/2.93  MUC search           : 0.00
% 5.44/2.93  Cooper               : 0.00
% 5.44/2.93  Total                : 1.87
% 5.44/2.93  Index Insertion      : 0.00
% 5.44/2.93  Index Deletion       : 0.00
% 5.44/2.93  Index Matching       : 0.00
% 5.44/2.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
