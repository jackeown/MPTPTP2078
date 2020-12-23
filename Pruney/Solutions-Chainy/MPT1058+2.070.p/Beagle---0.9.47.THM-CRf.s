%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:31 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 141 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :  110 ( 265 expanded)
%              Number of equality atoms :   38 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_74,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(c_30,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [B_27,A_28] :
      ( v4_relat_1(B_27,A_28)
      | ~ r1_tarski(k1_relat_1(B_27),A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_11,A_28] :
      ( v4_relat_1(k6_relat_1(A_11),A_28)
      | ~ r1_tarski(A_11,A_28)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_68])).

tff(c_73,plain,(
    ! [A_11,A_28] :
      ( v4_relat_1(k6_relat_1(A_11),A_28)
      | ~ r1_tarski(A_11,A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_71])).

tff(c_99,plain,(
    ! [B_37,A_38] :
      ( k7_relat_1(B_37,A_38) = B_37
      | ~ v4_relat_1(B_37,A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_102,plain,(
    ! [A_11,A_28] :
      ( k7_relat_1(k6_relat_1(A_11),A_28) = k6_relat_1(A_11)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ r1_tarski(A_11,A_28) ) ),
    inference(resolution,[status(thm)],[c_73,c_99])).

tff(c_105,plain,(
    ! [A_11,A_28] :
      ( k7_relat_1(k6_relat_1(A_11),A_28) = k6_relat_1(A_11)
      | ~ r1_tarski(A_11,A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_102])).

tff(c_20,plain,(
    ! [A_14] : v1_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [A_18] : k2_funct_1(k6_relat_1(A_18)) = k6_relat_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_138,plain,(
    ! [B_45,A_46] :
      ( k10_relat_1(k2_funct_1(B_45),A_46) = k9_relat_1(B_45,A_46)
      | ~ v2_funct_1(B_45)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_147,plain,(
    ! [A_18,A_46] :
      ( k9_relat_1(k6_relat_1(A_18),A_46) = k10_relat_1(k6_relat_1(A_18),A_46)
      | ~ v2_funct_1(k6_relat_1(A_18))
      | ~ v1_funct_1(k6_relat_1(A_18))
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_138])).

tff(c_151,plain,(
    ! [A_18,A_46] : k9_relat_1(k6_relat_1(A_18),A_46) = k10_relat_1(k6_relat_1(A_18),A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_24,c_147])).

tff(c_14,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_115,plain,(
    ! [A_41,A_42] :
      ( k7_relat_1(k6_relat_1(A_41),A_42) = k6_relat_1(A_41)
      | ~ r1_tarski(A_41,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_102])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    ! [A_41,A_42] :
      ( k9_relat_1(k6_relat_1(A_41),A_42) = k2_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ r1_tarski(A_41,A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_6])).

tff(c_127,plain,(
    ! [A_41,A_42] :
      ( k9_relat_1(k6_relat_1(A_41),A_42) = A_41
      | ~ r1_tarski(A_41,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14,c_121])).

tff(c_152,plain,(
    ! [A_41,A_42] :
      ( k10_relat_1(k6_relat_1(A_41),A_42) = A_41
      | ~ r1_tarski(A_41,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_127])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_relat_1(A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_171,plain,(
    ! [B_51,C_52,A_53] :
      ( k10_relat_1(k5_relat_1(B_51,C_52),A_53) = k10_relat_1(B_51,k10_relat_1(C_52,A_53))
      | ~ v1_relat_1(C_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_180,plain,(
    ! [A_12,B_13,A_53] :
      ( k10_relat_1(k6_relat_1(A_12),k10_relat_1(B_13,A_53)) = k10_relat_1(k7_relat_1(B_13,A_12),A_53)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(k6_relat_1(A_12))
      | ~ v1_relat_1(B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_171])).

tff(c_185,plain,(
    ! [A_54,B_55,A_56] :
      ( k10_relat_1(k6_relat_1(A_54),k10_relat_1(B_55,A_56)) = k10_relat_1(k7_relat_1(B_55,A_54),A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_180])).

tff(c_206,plain,(
    ! [A_41,A_54,A_42] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_41),A_54),A_42) = k10_relat_1(k6_relat_1(A_54),A_41)
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ r1_tarski(A_41,A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_185])).

tff(c_284,plain,(
    ! [A_64,A_65,A_66] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_64),A_65),A_66) = k10_relat_1(k6_relat_1(A_65),A_64)
      | ~ r1_tarski(A_64,A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_206])).

tff(c_413,plain,(
    ! [A_74,A_75,A_73] :
      ( k10_relat_1(k6_relat_1(A_74),A_75) = k10_relat_1(k6_relat_1(A_73),A_74)
      | ~ r1_tarski(A_74,A_75)
      | ~ r1_tarski(A_74,A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_284])).

tff(c_545,plain,(
    ! [A_82,A_83,A_84] :
      ( k10_relat_1(k6_relat_1(A_82),A_83) = A_83
      | ~ r1_tarski(A_83,A_84)
      | ~ r1_tarski(A_83,A_84)
      | ~ r1_tarski(A_83,A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_152])).

tff(c_549,plain,(
    ! [A_82] :
      ( k10_relat_1(k6_relat_1(A_82),k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3')
      | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2')
      | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),A_82) ) ),
    inference(resolution,[status(thm)],[c_32,c_545])).

tff(c_554,plain,(
    ! [A_85] :
      ( k10_relat_1(k6_relat_1(A_85),k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3')
      | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_549])).

tff(c_184,plain,(
    ! [A_12,B_13,A_53] :
      ( k10_relat_1(k6_relat_1(A_12),k10_relat_1(B_13,A_53)) = k10_relat_1(k7_relat_1(B_13,A_12),A_53)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_180])).

tff(c_578,plain,(
    ! [A_85] :
      ( k10_relat_1(k7_relat_1('#skF_1',A_85),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
      | ~ v1_relat_1('#skF_1')
      | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_184])).

tff(c_616,plain,(
    ! [A_86] :
      ( k10_relat_1(k7_relat_1('#skF_1',A_86),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
      | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_578])).

tff(c_619,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_616])).

tff(c_623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_619])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:57:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  
% 2.65/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  %$ v4_relat_1 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.65/1.35  
% 2.65/1.35  %Foreground sorts:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Background operators:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Foreground operators:
% 2.65/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.35  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.65/1.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.65/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.65/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.65/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.65/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.65/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.35  
% 2.81/1.37  tff(f_84, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 2.81/1.37  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.81/1.37  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.81/1.37  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.81/1.37  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.81/1.37  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.81/1.37  tff(f_74, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 2.81/1.37  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 2.81/1.37  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.81/1.37  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.81/1.37  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 2.81/1.37  tff(c_30, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.81/1.37  tff(c_32, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.81/1.37  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.81/1.37  tff(c_22, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.37  tff(c_12, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.81/1.37  tff(c_68, plain, (![B_27, A_28]: (v4_relat_1(B_27, A_28) | ~r1_tarski(k1_relat_1(B_27), A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.37  tff(c_71, plain, (![A_11, A_28]: (v4_relat_1(k6_relat_1(A_11), A_28) | ~r1_tarski(A_11, A_28) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_68])).
% 2.81/1.37  tff(c_73, plain, (![A_11, A_28]: (v4_relat_1(k6_relat_1(A_11), A_28) | ~r1_tarski(A_11, A_28))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_71])).
% 2.81/1.37  tff(c_99, plain, (![B_37, A_38]: (k7_relat_1(B_37, A_38)=B_37 | ~v4_relat_1(B_37, A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.81/1.37  tff(c_102, plain, (![A_11, A_28]: (k7_relat_1(k6_relat_1(A_11), A_28)=k6_relat_1(A_11) | ~v1_relat_1(k6_relat_1(A_11)) | ~r1_tarski(A_11, A_28))), inference(resolution, [status(thm)], [c_73, c_99])).
% 2.81/1.37  tff(c_105, plain, (![A_11, A_28]: (k7_relat_1(k6_relat_1(A_11), A_28)=k6_relat_1(A_11) | ~r1_tarski(A_11, A_28))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_102])).
% 2.81/1.37  tff(c_20, plain, (![A_14]: (v1_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.81/1.37  tff(c_24, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.37  tff(c_28, plain, (![A_18]: (k2_funct_1(k6_relat_1(A_18))=k6_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.81/1.37  tff(c_138, plain, (![B_45, A_46]: (k10_relat_1(k2_funct_1(B_45), A_46)=k9_relat_1(B_45, A_46) | ~v2_funct_1(B_45) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.81/1.37  tff(c_147, plain, (![A_18, A_46]: (k9_relat_1(k6_relat_1(A_18), A_46)=k10_relat_1(k6_relat_1(A_18), A_46) | ~v2_funct_1(k6_relat_1(A_18)) | ~v1_funct_1(k6_relat_1(A_18)) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_138])).
% 2.81/1.37  tff(c_151, plain, (![A_18, A_46]: (k9_relat_1(k6_relat_1(A_18), A_46)=k10_relat_1(k6_relat_1(A_18), A_46))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_24, c_147])).
% 2.81/1.37  tff(c_14, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.81/1.37  tff(c_115, plain, (![A_41, A_42]: (k7_relat_1(k6_relat_1(A_41), A_42)=k6_relat_1(A_41) | ~r1_tarski(A_41, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_102])).
% 2.81/1.37  tff(c_6, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.37  tff(c_121, plain, (![A_41, A_42]: (k9_relat_1(k6_relat_1(A_41), A_42)=k2_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(k6_relat_1(A_41)) | ~r1_tarski(A_41, A_42))), inference(superposition, [status(thm), theory('equality')], [c_115, c_6])).
% 2.81/1.37  tff(c_127, plain, (![A_41, A_42]: (k9_relat_1(k6_relat_1(A_41), A_42)=A_41 | ~r1_tarski(A_41, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_14, c_121])).
% 2.81/1.37  tff(c_152, plain, (![A_41, A_42]: (k10_relat_1(k6_relat_1(A_41), A_42)=A_41 | ~r1_tarski(A_41, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_127])).
% 2.81/1.37  tff(c_16, plain, (![A_12, B_13]: (k5_relat_1(k6_relat_1(A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.81/1.37  tff(c_171, plain, (![B_51, C_52, A_53]: (k10_relat_1(k5_relat_1(B_51, C_52), A_53)=k10_relat_1(B_51, k10_relat_1(C_52, A_53)) | ~v1_relat_1(C_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.81/1.37  tff(c_180, plain, (![A_12, B_13, A_53]: (k10_relat_1(k6_relat_1(A_12), k10_relat_1(B_13, A_53))=k10_relat_1(k7_relat_1(B_13, A_12), A_53) | ~v1_relat_1(B_13) | ~v1_relat_1(k6_relat_1(A_12)) | ~v1_relat_1(B_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_171])).
% 2.81/1.37  tff(c_185, plain, (![A_54, B_55, A_56]: (k10_relat_1(k6_relat_1(A_54), k10_relat_1(B_55, A_56))=k10_relat_1(k7_relat_1(B_55, A_54), A_56) | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_180])).
% 2.81/1.37  tff(c_206, plain, (![A_41, A_54, A_42]: (k10_relat_1(k7_relat_1(k6_relat_1(A_41), A_54), A_42)=k10_relat_1(k6_relat_1(A_54), A_41) | ~v1_relat_1(k6_relat_1(A_41)) | ~r1_tarski(A_41, A_42))), inference(superposition, [status(thm), theory('equality')], [c_152, c_185])).
% 2.81/1.37  tff(c_284, plain, (![A_64, A_65, A_66]: (k10_relat_1(k7_relat_1(k6_relat_1(A_64), A_65), A_66)=k10_relat_1(k6_relat_1(A_65), A_64) | ~r1_tarski(A_64, A_66))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_206])).
% 2.81/1.37  tff(c_413, plain, (![A_74, A_75, A_73]: (k10_relat_1(k6_relat_1(A_74), A_75)=k10_relat_1(k6_relat_1(A_73), A_74) | ~r1_tarski(A_74, A_75) | ~r1_tarski(A_74, A_73))), inference(superposition, [status(thm), theory('equality')], [c_105, c_284])).
% 2.81/1.37  tff(c_545, plain, (![A_82, A_83, A_84]: (k10_relat_1(k6_relat_1(A_82), A_83)=A_83 | ~r1_tarski(A_83, A_84) | ~r1_tarski(A_83, A_84) | ~r1_tarski(A_83, A_82))), inference(superposition, [status(thm), theory('equality')], [c_413, c_152])).
% 2.81/1.37  tff(c_549, plain, (![A_82]: (k10_relat_1(k6_relat_1(A_82), k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3') | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2') | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), A_82))), inference(resolution, [status(thm)], [c_32, c_545])).
% 2.81/1.37  tff(c_554, plain, (![A_85]: (k10_relat_1(k6_relat_1(A_85), k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3') | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), A_85))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_549])).
% 2.81/1.37  tff(c_184, plain, (![A_12, B_13, A_53]: (k10_relat_1(k6_relat_1(A_12), k10_relat_1(B_13, A_53))=k10_relat_1(k7_relat_1(B_13, A_12), A_53) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_180])).
% 2.81/1.37  tff(c_578, plain, (![A_85]: (k10_relat_1(k7_relat_1('#skF_1', A_85), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1') | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), A_85))), inference(superposition, [status(thm), theory('equality')], [c_554, c_184])).
% 2.81/1.37  tff(c_616, plain, (![A_86]: (k10_relat_1(k7_relat_1('#skF_1', A_86), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), A_86))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_578])).
% 2.81/1.37  tff(c_619, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_616])).
% 2.81/1.37  tff(c_623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_619])).
% 2.81/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.37  
% 2.81/1.37  Inference rules
% 2.81/1.37  ----------------------
% 2.81/1.37  #Ref     : 0
% 2.81/1.37  #Sup     : 138
% 2.81/1.37  #Fact    : 0
% 2.81/1.37  #Define  : 0
% 2.81/1.37  #Split   : 1
% 2.81/1.37  #Chain   : 0
% 2.81/1.37  #Close   : 0
% 2.81/1.37  
% 2.81/1.37  Ordering : KBO
% 2.81/1.37  
% 2.81/1.37  Simplification rules
% 2.81/1.37  ----------------------
% 2.81/1.37  #Subsume      : 10
% 2.81/1.37  #Demod        : 44
% 2.81/1.37  #Tautology    : 39
% 2.81/1.37  #SimpNegUnit  : 1
% 2.81/1.37  #BackRed      : 1
% 2.81/1.37  
% 2.81/1.37  #Partial instantiations: 0
% 2.81/1.37  #Strategies tried      : 1
% 2.81/1.37  
% 2.81/1.37  Timing (in seconds)
% 2.81/1.37  ----------------------
% 2.81/1.37  Preprocessing        : 0.28
% 2.81/1.37  Parsing              : 0.16
% 2.81/1.37  CNF conversion       : 0.02
% 2.81/1.37  Main loop            : 0.32
% 2.81/1.37  Inferencing          : 0.13
% 2.81/1.37  Reduction            : 0.08
% 2.81/1.37  Demodulation         : 0.06
% 2.81/1.37  BG Simplification    : 0.02
% 2.81/1.37  Subsumption          : 0.06
% 2.81/1.37  Abstraction          : 0.02
% 2.81/1.37  MUC search           : 0.00
% 2.81/1.37  Cooper               : 0.00
% 2.81/1.37  Total                : 0.63
% 2.81/1.37  Index Insertion      : 0.00
% 2.81/1.37  Index Deletion       : 0.00
% 2.81/1.37  Index Matching       : 0.00
% 2.81/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
