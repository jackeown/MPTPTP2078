%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:29 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 126 expanded)
%              Number of leaves         :   39 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  115 ( 185 expanded)
%              Number of equality atoms :   32 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_98,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_48,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_95,plain,(
    ! [A_66,B_67] :
      ( k2_xboole_0(A_66,B_67) = B_67
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_102,plain,(
    k2_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_50,c_95])).

tff(c_36,plain,(
    ! [A_44] : v1_relat_1(k6_relat_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_43] : k1_relat_1(k6_relat_1(A_43)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    ! [B_54,A_53] : k5_relat_1(k6_relat_1(B_54),k6_relat_1(A_53)) = k6_relat_1(k3_xboole_0(A_53,B_54)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1223,plain,(
    ! [A_150,B_151] :
      ( k10_relat_1(A_150,k1_relat_1(B_151)) = k1_relat_1(k5_relat_1(A_150,B_151))
      | ~ v1_relat_1(B_151)
      | ~ v1_relat_1(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1300,plain,(
    ! [A_150,A_43] :
      ( k1_relat_1(k5_relat_1(A_150,k6_relat_1(A_43))) = k10_relat_1(A_150,A_43)
      | ~ v1_relat_1(k6_relat_1(A_43))
      | ~ v1_relat_1(A_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1223])).

tff(c_2699,plain,(
    ! [A_248,A_249] :
      ( k1_relat_1(k5_relat_1(A_248,k6_relat_1(A_249))) = k10_relat_1(A_248,A_249)
      | ~ v1_relat_1(A_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1300])).

tff(c_2724,plain,(
    ! [A_53,B_54] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_53,B_54))) = k10_relat_1(k6_relat_1(B_54),A_53)
      | ~ v1_relat_1(k6_relat_1(B_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2699])).

tff(c_2730,plain,(
    ! [B_54,A_53] : k10_relat_1(k6_relat_1(B_54),A_53) = k3_xboole_0(A_53,B_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_2724])).

tff(c_38,plain,(
    ! [A_44] : v1_funct_1(k6_relat_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_43] : k2_relat_1(k6_relat_1(A_43)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_213,plain,(
    ! [A_84] :
      ( k10_relat_1(A_84,k2_relat_1(A_84)) = k1_relat_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_233,plain,(
    ! [A_43] :
      ( k10_relat_1(k6_relat_1(A_43),A_43) = k1_relat_1(k6_relat_1(A_43))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_213])).

tff(c_242,plain,(
    ! [A_43] : k10_relat_1(k6_relat_1(A_43),A_43) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_233])).

tff(c_511,plain,(
    ! [B_106,A_107] :
      ( r1_tarski(k9_relat_1(B_106,k10_relat_1(B_106,A_107)),A_107)
      | ~ v1_funct_1(B_106)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_519,plain,(
    ! [A_43] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_43),A_43),A_43)
      | ~ v1_funct_1(k6_relat_1(A_43))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_511])).

tff(c_527,plain,(
    ! [A_108] : r1_tarski(k9_relat_1(k6_relat_1(A_108),A_108),A_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_519])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_535,plain,(
    ! [A_109] : k2_xboole_0(k9_relat_1(k6_relat_1(A_109),A_109),A_109) = A_109 ),
    inference(resolution,[status(thm)],[c_527,c_10])).

tff(c_117,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_tarski(A_69,C_70)
      | ~ r1_tarski(k2_xboole_0(A_69,B_71),C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_139,plain,(
    ! [A_74,B_75] : r1_tarski(A_74,k2_xboole_0(A_74,B_75)) ),
    inference(resolution,[status(thm)],[c_6,c_117])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_153,plain,(
    ! [A_3,B_4,B_75] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_75)) ),
    inference(resolution,[status(thm)],[c_139,c_8])).

tff(c_550,plain,(
    ! [A_109,B_75] : r1_tarski(k9_relat_1(k6_relat_1(A_109),A_109),k2_xboole_0(A_109,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_153])).

tff(c_2731,plain,(
    ! [A_250,C_251,B_252] :
      ( r1_tarski(A_250,k10_relat_1(C_251,B_252))
      | ~ r1_tarski(k9_relat_1(C_251,A_250),B_252)
      | ~ r1_tarski(A_250,k1_relat_1(C_251))
      | ~ v1_funct_1(C_251)
      | ~ v1_relat_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2750,plain,(
    ! [A_109,B_75] :
      ( r1_tarski(A_109,k10_relat_1(k6_relat_1(A_109),k2_xboole_0(A_109,B_75)))
      | ~ r1_tarski(A_109,k1_relat_1(k6_relat_1(A_109)))
      | ~ v1_funct_1(k6_relat_1(A_109))
      | ~ v1_relat_1(k6_relat_1(A_109)) ) ),
    inference(resolution,[status(thm)],[c_550,c_2731])).

tff(c_2784,plain,(
    ! [A_109,B_75] : r1_tarski(A_109,k10_relat_1(k6_relat_1(A_109),k2_xboole_0(A_109,B_75))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_6,c_32,c_2750])).

tff(c_3062,plain,(
    ! [A_259,B_260] : r1_tarski(A_259,k3_xboole_0(k2_xboole_0(A_259,B_260),A_259)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2730,c_2784])).

tff(c_129,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(k10_relat_1(B_72,A_73),k1_relat_1(B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_135,plain,(
    ! [A_43,A_73] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_43),A_73),A_43)
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_129])).

tff(c_138,plain,(
    ! [A_43,A_73] : r1_tarski(k10_relat_1(k6_relat_1(A_43),A_73),A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_135])).

tff(c_1287,plain,(
    ! [A_43,B_151] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_43),B_151)),A_43)
      | ~ v1_relat_1(B_151)
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1223,c_138])).

tff(c_1333,plain,(
    ! [A_152,B_153] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_152),B_153)),A_152)
      | ~ v1_relat_1(B_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1287])).

tff(c_1341,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_53,B_54))),B_54)
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1333])).

tff(c_1346,plain,(
    ! [A_154,B_155] : r1_tarski(k3_xboole_0(A_154,B_155),B_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1341])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1352,plain,(
    ! [A_154,B_155] :
      ( k3_xboole_0(A_154,B_155) = B_155
      | ~ r1_tarski(B_155,k3_xboole_0(A_154,B_155)) ) ),
    inference(resolution,[status(thm)],[c_1346,c_2])).

tff(c_3142,plain,(
    ! [A_261,B_262] : k3_xboole_0(k2_xboole_0(A_261,B_262),A_261) = A_261 ),
    inference(resolution,[status(thm)],[c_3062,c_1352])).

tff(c_3297,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_3142])).

tff(c_40,plain,(
    ! [A_45,C_47,B_46] :
      ( k3_xboole_0(A_45,k10_relat_1(C_47,B_46)) = k10_relat_1(k7_relat_1(C_47,A_45),B_46)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3432,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3297,c_40])).

tff(c_3467,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3432])).

tff(c_3469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_3467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:53:24 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/2.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/2.11  
% 4.55/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/2.11  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.55/2.11  
% 4.55/2.11  %Foreground sorts:
% 4.55/2.11  
% 4.55/2.11  
% 4.55/2.11  %Background operators:
% 4.55/2.11  
% 4.55/2.11  
% 4.55/2.11  %Foreground operators:
% 4.55/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.55/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/2.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.55/2.11  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.55/2.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.55/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/2.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.55/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.55/2.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.55/2.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.55/2.11  tff('#skF_2', type, '#skF_2': $i).
% 4.55/2.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.55/2.11  tff('#skF_3', type, '#skF_3': $i).
% 4.55/2.11  tff('#skF_1', type, '#skF_1': $i).
% 4.55/2.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.55/2.11  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/2.11  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.55/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.55/2.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.55/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.55/2.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.55/2.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.55/2.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.55/2.11  
% 4.80/2.12  tff(f_108, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 4.80/2.12  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.80/2.12  tff(f_76, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.80/2.12  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.80/2.12  tff(f_98, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 4.80/2.12  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 4.80/2.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.80/2.12  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.80/2.12  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 4.80/2.12  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.80/2.12  tff(f_96, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.80/2.12  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 4.80/2.12  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 4.80/2.12  tff(c_48, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.80/2.12  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.80/2.12  tff(c_50, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.80/2.12  tff(c_95, plain, (![A_66, B_67]: (k2_xboole_0(A_66, B_67)=B_67 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.80/2.12  tff(c_102, plain, (k2_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_50, c_95])).
% 4.80/2.12  tff(c_36, plain, (![A_44]: (v1_relat_1(k6_relat_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.80/2.12  tff(c_32, plain, (![A_43]: (k1_relat_1(k6_relat_1(A_43))=A_43)), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.80/2.12  tff(c_46, plain, (![B_54, A_53]: (k5_relat_1(k6_relat_1(B_54), k6_relat_1(A_53))=k6_relat_1(k3_xboole_0(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.80/2.12  tff(c_1223, plain, (![A_150, B_151]: (k10_relat_1(A_150, k1_relat_1(B_151))=k1_relat_1(k5_relat_1(A_150, B_151)) | ~v1_relat_1(B_151) | ~v1_relat_1(A_150))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.80/2.12  tff(c_1300, plain, (![A_150, A_43]: (k1_relat_1(k5_relat_1(A_150, k6_relat_1(A_43)))=k10_relat_1(A_150, A_43) | ~v1_relat_1(k6_relat_1(A_43)) | ~v1_relat_1(A_150))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1223])).
% 4.80/2.12  tff(c_2699, plain, (![A_248, A_249]: (k1_relat_1(k5_relat_1(A_248, k6_relat_1(A_249)))=k10_relat_1(A_248, A_249) | ~v1_relat_1(A_248))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1300])).
% 4.80/2.12  tff(c_2724, plain, (![A_53, B_54]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_53, B_54)))=k10_relat_1(k6_relat_1(B_54), A_53) | ~v1_relat_1(k6_relat_1(B_54)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2699])).
% 4.80/2.12  tff(c_2730, plain, (![B_54, A_53]: (k10_relat_1(k6_relat_1(B_54), A_53)=k3_xboole_0(A_53, B_54))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_2724])).
% 4.80/2.12  tff(c_38, plain, (![A_44]: (v1_funct_1(k6_relat_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.80/2.12  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.80/2.12  tff(c_34, plain, (![A_43]: (k2_relat_1(k6_relat_1(A_43))=A_43)), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.80/2.12  tff(c_213, plain, (![A_84]: (k10_relat_1(A_84, k2_relat_1(A_84))=k1_relat_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.80/2.12  tff(c_233, plain, (![A_43]: (k10_relat_1(k6_relat_1(A_43), A_43)=k1_relat_1(k6_relat_1(A_43)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_213])).
% 4.80/2.12  tff(c_242, plain, (![A_43]: (k10_relat_1(k6_relat_1(A_43), A_43)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_233])).
% 4.80/2.12  tff(c_511, plain, (![B_106, A_107]: (r1_tarski(k9_relat_1(B_106, k10_relat_1(B_106, A_107)), A_107) | ~v1_funct_1(B_106) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.80/2.12  tff(c_519, plain, (![A_43]: (r1_tarski(k9_relat_1(k6_relat_1(A_43), A_43), A_43) | ~v1_funct_1(k6_relat_1(A_43)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_242, c_511])).
% 4.80/2.12  tff(c_527, plain, (![A_108]: (r1_tarski(k9_relat_1(k6_relat_1(A_108), A_108), A_108))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_519])).
% 4.80/2.12  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.80/2.12  tff(c_535, plain, (![A_109]: (k2_xboole_0(k9_relat_1(k6_relat_1(A_109), A_109), A_109)=A_109)), inference(resolution, [status(thm)], [c_527, c_10])).
% 4.80/2.12  tff(c_117, plain, (![A_69, C_70, B_71]: (r1_tarski(A_69, C_70) | ~r1_tarski(k2_xboole_0(A_69, B_71), C_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/2.12  tff(c_139, plain, (![A_74, B_75]: (r1_tarski(A_74, k2_xboole_0(A_74, B_75)))), inference(resolution, [status(thm)], [c_6, c_117])).
% 4.80/2.12  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/2.12  tff(c_153, plain, (![A_3, B_4, B_75]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_75)))), inference(resolution, [status(thm)], [c_139, c_8])).
% 4.80/2.12  tff(c_550, plain, (![A_109, B_75]: (r1_tarski(k9_relat_1(k6_relat_1(A_109), A_109), k2_xboole_0(A_109, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_535, c_153])).
% 4.80/2.12  tff(c_2731, plain, (![A_250, C_251, B_252]: (r1_tarski(A_250, k10_relat_1(C_251, B_252)) | ~r1_tarski(k9_relat_1(C_251, A_250), B_252) | ~r1_tarski(A_250, k1_relat_1(C_251)) | ~v1_funct_1(C_251) | ~v1_relat_1(C_251))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.80/2.12  tff(c_2750, plain, (![A_109, B_75]: (r1_tarski(A_109, k10_relat_1(k6_relat_1(A_109), k2_xboole_0(A_109, B_75))) | ~r1_tarski(A_109, k1_relat_1(k6_relat_1(A_109))) | ~v1_funct_1(k6_relat_1(A_109)) | ~v1_relat_1(k6_relat_1(A_109)))), inference(resolution, [status(thm)], [c_550, c_2731])).
% 4.80/2.12  tff(c_2784, plain, (![A_109, B_75]: (r1_tarski(A_109, k10_relat_1(k6_relat_1(A_109), k2_xboole_0(A_109, B_75))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_6, c_32, c_2750])).
% 4.80/2.12  tff(c_3062, plain, (![A_259, B_260]: (r1_tarski(A_259, k3_xboole_0(k2_xboole_0(A_259, B_260), A_259)))), inference(demodulation, [status(thm), theory('equality')], [c_2730, c_2784])).
% 4.80/2.12  tff(c_129, plain, (![B_72, A_73]: (r1_tarski(k10_relat_1(B_72, A_73), k1_relat_1(B_72)) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.80/2.12  tff(c_135, plain, (![A_43, A_73]: (r1_tarski(k10_relat_1(k6_relat_1(A_43), A_73), A_43) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_129])).
% 4.80/2.12  tff(c_138, plain, (![A_43, A_73]: (r1_tarski(k10_relat_1(k6_relat_1(A_43), A_73), A_43))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_135])).
% 4.80/2.12  tff(c_1287, plain, (![A_43, B_151]: (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_43), B_151)), A_43) | ~v1_relat_1(B_151) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_1223, c_138])).
% 4.80/2.12  tff(c_1333, plain, (![A_152, B_153]: (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_152), B_153)), A_152) | ~v1_relat_1(B_153))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1287])).
% 4.80/2.12  tff(c_1341, plain, (![A_53, B_54]: (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_53, B_54))), B_54) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1333])).
% 4.80/2.12  tff(c_1346, plain, (![A_154, B_155]: (r1_tarski(k3_xboole_0(A_154, B_155), B_155))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1341])).
% 4.80/2.12  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.80/2.12  tff(c_1352, plain, (![A_154, B_155]: (k3_xboole_0(A_154, B_155)=B_155 | ~r1_tarski(B_155, k3_xboole_0(A_154, B_155)))), inference(resolution, [status(thm)], [c_1346, c_2])).
% 4.80/2.12  tff(c_3142, plain, (![A_261, B_262]: (k3_xboole_0(k2_xboole_0(A_261, B_262), A_261)=A_261)), inference(resolution, [status(thm)], [c_3062, c_1352])).
% 4.80/2.12  tff(c_3297, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_102, c_3142])).
% 4.80/2.12  tff(c_40, plain, (![A_45, C_47, B_46]: (k3_xboole_0(A_45, k10_relat_1(C_47, B_46))=k10_relat_1(k7_relat_1(C_47, A_45), B_46) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.80/2.12  tff(c_3432, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3297, c_40])).
% 4.80/2.12  tff(c_3467, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3432])).
% 4.80/2.12  tff(c_3469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_3467])).
% 4.80/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/2.12  
% 4.80/2.12  Inference rules
% 4.80/2.12  ----------------------
% 4.80/2.12  #Ref     : 0
% 4.80/2.12  #Sup     : 834
% 4.80/2.12  #Fact    : 0
% 4.80/2.12  #Define  : 0
% 4.80/2.12  #Split   : 1
% 4.80/2.12  #Chain   : 0
% 4.80/2.12  #Close   : 0
% 4.80/2.12  
% 4.80/2.12  Ordering : KBO
% 4.80/2.12  
% 4.80/2.12  Simplification rules
% 4.80/2.12  ----------------------
% 4.80/2.12  #Subsume      : 29
% 4.80/2.12  #Demod        : 460
% 4.80/2.12  #Tautology    : 358
% 4.80/2.12  #SimpNegUnit  : 1
% 4.80/2.12  #BackRed      : 16
% 4.80/2.12  
% 4.80/2.12  #Partial instantiations: 0
% 4.80/2.12  #Strategies tried      : 1
% 4.80/2.12  
% 4.80/2.12  Timing (in seconds)
% 4.80/2.12  ----------------------
% 4.80/2.13  Preprocessing        : 0.48
% 4.80/2.13  Parsing              : 0.29
% 4.80/2.13  CNF conversion       : 0.03
% 4.80/2.13  Main loop            : 0.78
% 4.80/2.13  Inferencing          : 0.25
% 4.80/2.13  Reduction            : 0.31
% 4.80/2.13  Demodulation         : 0.24
% 4.80/2.13  BG Simplification    : 0.04
% 4.80/2.13  Subsumption          : 0.14
% 4.80/2.13  Abstraction          : 0.04
% 4.80/2.13  MUC search           : 0.00
% 4.80/2.13  Cooper               : 0.00
% 4.80/2.13  Total                : 1.30
% 4.80/2.13  Index Insertion      : 0.00
% 4.80/2.13  Index Deletion       : 0.00
% 4.80/2.13  Index Matching       : 0.00
% 4.80/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
