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

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 122 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :   98 ( 221 expanded)
%              Number of equality atoms :   38 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_64,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_66,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_44,axiom,(
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

tff(c_24,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_12] : v1_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_16] : k2_funct_1(k6_relat_1(A_16)) = k6_relat_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_108,plain,(
    ! [B_35,A_36] :
      ( k10_relat_1(k2_funct_1(B_35),A_36) = k9_relat_1(B_35,A_36)
      | ~ v2_funct_1(B_35)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_117,plain,(
    ! [A_16,A_36] :
      ( k9_relat_1(k6_relat_1(A_16),A_36) = k10_relat_1(k6_relat_1(A_16),A_36)
      | ~ v2_funct_1(k6_relat_1(A_16))
      | ~ v1_funct_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_108])).

tff(c_121,plain,(
    ! [A_16,A_36] : k9_relat_1(k6_relat_1(A_16),A_36) = k10_relat_1(k6_relat_1(A_16),A_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_20,c_117])).

tff(c_8,plain,(
    ! [A_7] : k2_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    ! [B_29,A_30] :
      ( k7_relat_1(B_29,A_30) = B_29
      | ~ r1_tarski(k1_relat_1(B_29),A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    ! [A_7,A_30] :
      ( k7_relat_1(k6_relat_1(A_7),A_30) = k6_relat_1(A_7)
      | ~ r1_tarski(A_7,A_30)
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_79])).

tff(c_85,plain,(
    ! [A_31,A_32] :
      ( k7_relat_1(k6_relat_1(A_31),A_32) = k6_relat_1(A_31)
      | ~ r1_tarski(A_31,A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k2_relat_1(k7_relat_1(B_2,A_1)) = k9_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    ! [A_31,A_32] :
      ( k9_relat_1(k6_relat_1(A_31),A_32) = k2_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ r1_tarski(A_31,A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2])).

tff(c_97,plain,(
    ! [A_31,A_32] :
      ( k9_relat_1(k6_relat_1(A_31),A_32) = A_31
      | ~ r1_tarski(A_31,A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8,c_91])).

tff(c_122,plain,(
    ! [A_31,A_32] :
      ( k10_relat_1(k6_relat_1(A_31),A_32) = A_31
      | ~ r1_tarski(A_31,A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_97])).

tff(c_84,plain,(
    ! [A_7,A_30] :
      ( k7_relat_1(k6_relat_1(A_7),A_30) = k6_relat_1(A_7)
      | ~ r1_tarski(A_7,A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),B_9) = k7_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_141,plain,(
    ! [B_41,C_42,A_43] :
      ( k10_relat_1(k5_relat_1(B_41,C_42),A_43) = k10_relat_1(B_41,k10_relat_1(C_42,A_43))
      | ~ v1_relat_1(C_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_150,plain,(
    ! [A_8,B_9,A_43] :
      ( k10_relat_1(k6_relat_1(A_8),k10_relat_1(B_9,A_43)) = k10_relat_1(k7_relat_1(B_9,A_8),A_43)
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_141])).

tff(c_155,plain,(
    ! [A_44,B_45,A_46] :
      ( k10_relat_1(k6_relat_1(A_44),k10_relat_1(B_45,A_46)) = k10_relat_1(k7_relat_1(B_45,A_44),A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_150])).

tff(c_176,plain,(
    ! [A_31,A_44,A_32] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_31),A_44),A_32) = k10_relat_1(k6_relat_1(A_44),A_31)
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ r1_tarski(A_31,A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_155])).

tff(c_209,plain,(
    ! [A_50,A_51,A_52] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_50),A_51),A_52) = k10_relat_1(k6_relat_1(A_51),A_50)
      | ~ r1_tarski(A_50,A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_176])).

tff(c_251,plain,(
    ! [A_58,A_56,A_57] :
      ( k10_relat_1(k6_relat_1(A_58),A_56) = k10_relat_1(k6_relat_1(A_56),A_57)
      | ~ r1_tarski(A_56,A_57)
      | ~ r1_tarski(A_56,A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_209])).

tff(c_397,plain,(
    ! [A_66,A_67,A_68] :
      ( k10_relat_1(k6_relat_1(A_66),A_67) = A_67
      | ~ r1_tarski(A_67,A_68)
      | ~ r1_tarski(A_67,A_66)
      | ~ r1_tarski(A_67,A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_251])).

tff(c_399,plain,(
    ! [A_66] :
      ( k10_relat_1(k6_relat_1(A_66),k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3')
      | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),A_66)
      | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_397])).

tff(c_403,plain,(
    ! [A_69] :
      ( k10_relat_1(k6_relat_1(A_69),k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3')
      | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_399])).

tff(c_154,plain,(
    ! [A_8,B_9,A_43] :
      ( k10_relat_1(k6_relat_1(A_8),k10_relat_1(B_9,A_43)) = k10_relat_1(k7_relat_1(B_9,A_8),A_43)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_150])).

tff(c_424,plain,(
    ! [A_69] :
      ( k10_relat_1(k7_relat_1('#skF_1',A_69),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
      | ~ v1_relat_1('#skF_1')
      | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_154])).

tff(c_459,plain,(
    ! [A_70] :
      ( k10_relat_1(k7_relat_1('#skF_1',A_70),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
      | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_424])).

tff(c_462,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_459])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:32:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.30  
% 2.11/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.30  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.30  
% 2.11/1.30  %Foreground sorts:
% 2.11/1.30  
% 2.11/1.30  
% 2.11/1.30  %Background operators:
% 2.11/1.30  
% 2.11/1.30  
% 2.11/1.30  %Foreground operators:
% 2.11/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.11/1.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.11/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.11/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.11/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.11/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.11/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.30  
% 2.44/1.32  tff(f_76, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 2.44/1.32  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.44/1.32  tff(f_64, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 2.44/1.32  tff(f_66, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 2.44/1.32  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 2.44/1.32  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.44/1.32  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.44/1.32  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.44/1.32  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.44/1.32  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 2.44/1.32  tff(c_24, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.44/1.32  tff(c_26, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.44/1.32  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.44/1.32  tff(c_14, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.44/1.32  tff(c_16, plain, (![A_12]: (v1_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.44/1.32  tff(c_20, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.44/1.32  tff(c_22, plain, (![A_16]: (k2_funct_1(k6_relat_1(A_16))=k6_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.44/1.32  tff(c_108, plain, (![B_35, A_36]: (k10_relat_1(k2_funct_1(B_35), A_36)=k9_relat_1(B_35, A_36) | ~v2_funct_1(B_35) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.44/1.32  tff(c_117, plain, (![A_16, A_36]: (k9_relat_1(k6_relat_1(A_16), A_36)=k10_relat_1(k6_relat_1(A_16), A_36) | ~v2_funct_1(k6_relat_1(A_16)) | ~v1_funct_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_108])).
% 2.44/1.32  tff(c_121, plain, (![A_16, A_36]: (k9_relat_1(k6_relat_1(A_16), A_36)=k10_relat_1(k6_relat_1(A_16), A_36))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_20, c_117])).
% 2.44/1.32  tff(c_8, plain, (![A_7]: (k2_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.44/1.32  tff(c_6, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.44/1.32  tff(c_79, plain, (![B_29, A_30]: (k7_relat_1(B_29, A_30)=B_29 | ~r1_tarski(k1_relat_1(B_29), A_30) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.32  tff(c_82, plain, (![A_7, A_30]: (k7_relat_1(k6_relat_1(A_7), A_30)=k6_relat_1(A_7) | ~r1_tarski(A_7, A_30) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_79])).
% 2.44/1.32  tff(c_85, plain, (![A_31, A_32]: (k7_relat_1(k6_relat_1(A_31), A_32)=k6_relat_1(A_31) | ~r1_tarski(A_31, A_32))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_82])).
% 2.44/1.32  tff(c_2, plain, (![B_2, A_1]: (k2_relat_1(k7_relat_1(B_2, A_1))=k9_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.44/1.32  tff(c_91, plain, (![A_31, A_32]: (k9_relat_1(k6_relat_1(A_31), A_32)=k2_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(k6_relat_1(A_31)) | ~r1_tarski(A_31, A_32))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2])).
% 2.44/1.32  tff(c_97, plain, (![A_31, A_32]: (k9_relat_1(k6_relat_1(A_31), A_32)=A_31 | ~r1_tarski(A_31, A_32))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_8, c_91])).
% 2.44/1.32  tff(c_122, plain, (![A_31, A_32]: (k10_relat_1(k6_relat_1(A_31), A_32)=A_31 | ~r1_tarski(A_31, A_32))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_97])).
% 2.44/1.32  tff(c_84, plain, (![A_7, A_30]: (k7_relat_1(k6_relat_1(A_7), A_30)=k6_relat_1(A_7) | ~r1_tarski(A_7, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_82])).
% 2.44/1.32  tff(c_10, plain, (![A_8, B_9]: (k5_relat_1(k6_relat_1(A_8), B_9)=k7_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.32  tff(c_141, plain, (![B_41, C_42, A_43]: (k10_relat_1(k5_relat_1(B_41, C_42), A_43)=k10_relat_1(B_41, k10_relat_1(C_42, A_43)) | ~v1_relat_1(C_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.44/1.32  tff(c_150, plain, (![A_8, B_9, A_43]: (k10_relat_1(k6_relat_1(A_8), k10_relat_1(B_9, A_43))=k10_relat_1(k7_relat_1(B_9, A_8), A_43) | ~v1_relat_1(B_9) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(B_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_141])).
% 2.44/1.32  tff(c_155, plain, (![A_44, B_45, A_46]: (k10_relat_1(k6_relat_1(A_44), k10_relat_1(B_45, A_46))=k10_relat_1(k7_relat_1(B_45, A_44), A_46) | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_150])).
% 2.44/1.32  tff(c_176, plain, (![A_31, A_44, A_32]: (k10_relat_1(k7_relat_1(k6_relat_1(A_31), A_44), A_32)=k10_relat_1(k6_relat_1(A_44), A_31) | ~v1_relat_1(k6_relat_1(A_31)) | ~r1_tarski(A_31, A_32))), inference(superposition, [status(thm), theory('equality')], [c_122, c_155])).
% 2.44/1.32  tff(c_209, plain, (![A_50, A_51, A_52]: (k10_relat_1(k7_relat_1(k6_relat_1(A_50), A_51), A_52)=k10_relat_1(k6_relat_1(A_51), A_50) | ~r1_tarski(A_50, A_52))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_176])).
% 2.44/1.32  tff(c_251, plain, (![A_58, A_56, A_57]: (k10_relat_1(k6_relat_1(A_58), A_56)=k10_relat_1(k6_relat_1(A_56), A_57) | ~r1_tarski(A_56, A_57) | ~r1_tarski(A_56, A_58))), inference(superposition, [status(thm), theory('equality')], [c_84, c_209])).
% 2.44/1.32  tff(c_397, plain, (![A_66, A_67, A_68]: (k10_relat_1(k6_relat_1(A_66), A_67)=A_67 | ~r1_tarski(A_67, A_68) | ~r1_tarski(A_67, A_66) | ~r1_tarski(A_67, A_68))), inference(superposition, [status(thm), theory('equality')], [c_122, c_251])).
% 2.44/1.32  tff(c_399, plain, (![A_66]: (k10_relat_1(k6_relat_1(A_66), k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3') | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), A_66) | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_397])).
% 2.44/1.32  tff(c_403, plain, (![A_69]: (k10_relat_1(k6_relat_1(A_69), k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3') | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), A_69))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_399])).
% 2.44/1.32  tff(c_154, plain, (![A_8, B_9, A_43]: (k10_relat_1(k6_relat_1(A_8), k10_relat_1(B_9, A_43))=k10_relat_1(k7_relat_1(B_9, A_8), A_43) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_150])).
% 2.44/1.32  tff(c_424, plain, (![A_69]: (k10_relat_1(k7_relat_1('#skF_1', A_69), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1') | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), A_69))), inference(superposition, [status(thm), theory('equality')], [c_403, c_154])).
% 2.44/1.32  tff(c_459, plain, (![A_70]: (k10_relat_1(k7_relat_1('#skF_1', A_70), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), A_70))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_424])).
% 2.44/1.32  tff(c_462, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_459])).
% 2.44/1.32  tff(c_466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_462])).
% 2.44/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.32  
% 2.44/1.32  Inference rules
% 2.44/1.32  ----------------------
% 2.44/1.32  #Ref     : 0
% 2.44/1.32  #Sup     : 106
% 2.44/1.32  #Fact    : 0
% 2.44/1.32  #Define  : 0
% 2.44/1.32  #Split   : 1
% 2.44/1.32  #Chain   : 0
% 2.44/1.32  #Close   : 0
% 2.44/1.32  
% 2.44/1.32  Ordering : KBO
% 2.44/1.32  
% 2.44/1.32  Simplification rules
% 2.44/1.32  ----------------------
% 2.44/1.32  #Subsume      : 8
% 2.44/1.32  #Demod        : 27
% 2.44/1.32  #Tautology    : 32
% 2.44/1.32  #SimpNegUnit  : 1
% 2.44/1.32  #BackRed      : 1
% 2.44/1.32  
% 2.44/1.32  #Partial instantiations: 0
% 2.44/1.32  #Strategies tried      : 1
% 2.44/1.32  
% 2.44/1.32  Timing (in seconds)
% 2.44/1.32  ----------------------
% 2.44/1.32  Preprocessing        : 0.28
% 2.44/1.32  Parsing              : 0.16
% 2.44/1.32  CNF conversion       : 0.02
% 2.44/1.32  Main loop            : 0.28
% 2.44/1.32  Inferencing          : 0.12
% 2.44/1.32  Reduction            : 0.08
% 2.44/1.32  Demodulation         : 0.05
% 2.44/1.32  BG Simplification    : 0.02
% 2.44/1.32  Subsumption          : 0.05
% 2.44/1.32  Abstraction          : 0.02
% 2.44/1.32  MUC search           : 0.00
% 2.44/1.32  Cooper               : 0.00
% 2.44/1.32  Total                : 0.60
% 2.44/1.32  Index Insertion      : 0.00
% 2.44/1.32  Index Deletion       : 0.00
% 2.44/1.32  Index Matching       : 0.00
% 2.44/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
