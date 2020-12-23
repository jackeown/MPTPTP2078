%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:51 EST 2020

% Result     : Theorem 36.04s
% Output     : CNFRefutation 36.24s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 134 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  129 ( 275 expanded)
%              Number of equality atoms :   41 (  87 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(A,k2_relat_1(B))
         => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k2_relat_1(B))
       => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k9_relat_1(k8_relat_1(A,C),B) = k3_xboole_0(A,k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(c_30,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = k8_relat_1(A_12,B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_223,plain,(
    ! [A_54,B_55] :
      ( k10_relat_1(A_54,k1_relat_1(B_55)) = k1_relat_1(k5_relat_1(A_54,B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_235,plain,(
    ! [A_54,A_18] :
      ( k1_relat_1(k5_relat_1(A_54,k6_relat_1(A_18))) = k10_relat_1(A_54,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_223])).

tff(c_309,plain,(
    ! [A_61,A_62] :
      ( k1_relat_1(k5_relat_1(A_61,k6_relat_1(A_62))) = k10_relat_1(A_61,A_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_235])).

tff(c_324,plain,(
    ! [A_12,B_13] :
      ( k1_relat_1(k8_relat_1(A_12,B_13)) = k10_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_309])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_144,plain,(
    ! [A_49,B_50] :
      ( k2_relat_1(k8_relat_1(A_49,B_50)) = A_49
      | ~ r1_tarski(A_49,k2_relat_1(B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_158,plain,
    ( k2_relat_1(k8_relat_1('#skF_1','#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_144])).

tff(c_166,plain,(
    k2_relat_1(k8_relat_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_158])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k8_relat_1(A_19,B_20))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k3_xboole_0(k2_relat_1(B_9),A_8) = k2_relat_1(k8_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_175,plain,(
    ! [A_8] :
      ( k2_relat_1(k8_relat_1(A_8,k8_relat_1('#skF_1','#skF_2'))) = k3_xboole_0('#skF_1',A_8)
      | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_8])).

tff(c_179,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_182,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_179])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_182])).

tff(c_188,plain,(
    v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_421,plain,(
    ! [A_69,C_70,B_71] :
      ( k9_relat_1(k8_relat_1(A_69,C_70),B_71) = k3_xboole_0(A_69,k9_relat_1(C_70,B_71))
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_14] :
      ( k9_relat_1(A_14,k1_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1711,plain,(
    ! [A_149,C_150] :
      ( k3_xboole_0(A_149,k9_relat_1(C_150,k1_relat_1(k8_relat_1(A_149,C_150)))) = k2_relat_1(k8_relat_1(A_149,C_150))
      | ~ v1_relat_1(k8_relat_1(A_149,C_150))
      | ~ v1_funct_1(C_150)
      | ~ v1_relat_1(C_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_14])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_163,plain,(
    ! [A_1,C_3,B_50] :
      ( k2_relat_1(k8_relat_1(k3_xboole_0(A_1,C_3),B_50)) = k3_xboole_0(A_1,C_3)
      | ~ v1_relat_1(B_50)
      | ~ r1_tarski(A_1,k2_relat_1(B_50)) ) ),
    inference(resolution,[status(thm)],[c_2,c_144])).

tff(c_40791,plain,(
    ! [A_1060,C_1061,B_1062] :
      ( k3_xboole_0(A_1060,k9_relat_1(C_1061,k1_relat_1(k8_relat_1(A_1060,C_1061)))) = k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(A_1060,C_1061)),B_1062))
      | ~ v1_relat_1(B_1062)
      | ~ r1_tarski(A_1060,k2_relat_1(B_1062))
      | ~ v1_relat_1(k8_relat_1(A_1060,C_1061))
      | ~ v1_funct_1(C_1061)
      | ~ v1_relat_1(C_1061) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1711,c_163])).

tff(c_41632,plain,(
    ! [B_1062] :
      ( k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k1_relat_1(k8_relat_1('#skF_1','#skF_2')))) = k2_relat_1(k8_relat_1('#skF_1',B_1062))
      | ~ v1_relat_1(B_1062)
      | ~ r1_tarski('#skF_1',k2_relat_1(B_1062))
      | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_40791])).

tff(c_76805,plain,(
    ! [B_1467] :
      ( k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k1_relat_1(k8_relat_1('#skF_1','#skF_2')))) = k2_relat_1(k8_relat_1('#skF_1',B_1467))
      | ~ v1_relat_1(B_1467)
      | ~ r1_tarski('#skF_1',k2_relat_1(B_1467)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_188,c_41632])).

tff(c_76867,plain,
    ( k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k1_relat_1(k8_relat_1('#skF_1','#skF_2')))) = k2_relat_1(k8_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_76805])).

tff(c_76874,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k1_relat_1(k8_relat_1('#skF_1','#skF_2')))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_166,c_76867])).

tff(c_77409,plain,
    ( k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1'))) = '#skF_1'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_76874])).

tff(c_77472,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_77409])).

tff(c_20,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k9_relat_1(B_25,k10_relat_1(B_25,A_24)),A_24)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2648,plain,(
    ! [B_183,B_184] :
      ( k2_relat_1(k8_relat_1(k9_relat_1(B_183,k10_relat_1(B_183,k2_relat_1(B_184))),B_184)) = k9_relat_1(B_183,k10_relat_1(B_183,k2_relat_1(B_184)))
      | ~ v1_relat_1(B_184)
      | ~ v1_funct_1(B_183)
      | ~ v1_relat_1(B_183) ) ),
    inference(resolution,[status(thm)],[c_28,c_144])).

tff(c_91,plain,(
    ! [B_40,A_41] :
      ( k3_xboole_0(k2_relat_1(B_40),A_41) = k2_relat_1(k8_relat_1(A_41,B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    ! [A_41,A_18] :
      ( k2_relat_1(k8_relat_1(A_41,k6_relat_1(A_18))) = k3_xboole_0(A_18,A_41)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_91])).

tff(c_107,plain,(
    ! [A_41,A_18] : k2_relat_1(k8_relat_1(A_41,k6_relat_1(A_18))) = k3_xboole_0(A_18,A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_103])).

tff(c_2683,plain,(
    ! [A_18,B_183] :
      ( k3_xboole_0(A_18,k9_relat_1(B_183,k10_relat_1(B_183,k2_relat_1(k6_relat_1(A_18))))) = k9_relat_1(B_183,k10_relat_1(B_183,k2_relat_1(k6_relat_1(A_18))))
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_funct_1(B_183)
      | ~ v1_relat_1(B_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2648,c_107])).

tff(c_2735,plain,(
    ! [A_18,B_183] :
      ( k3_xboole_0(A_18,k9_relat_1(B_183,k10_relat_1(B_183,A_18))) = k9_relat_1(B_183,k10_relat_1(B_183,A_18))
      | ~ v1_funct_1(B_183)
      | ~ v1_relat_1(B_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20,c_20,c_2683])).

tff(c_77880,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_77472,c_2735])).

tff(c_78047,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_77880])).

tff(c_78049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_78047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:06:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.04/24.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.04/24.96  
% 36.04/24.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.04/24.97  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 36.04/24.97  
% 36.04/24.97  %Foreground sorts:
% 36.04/24.97  
% 36.04/24.97  
% 36.04/24.97  %Background operators:
% 36.04/24.97  
% 36.04/24.97  
% 36.04/24.97  %Foreground operators:
% 36.04/24.97  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 36.04/24.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 36.04/24.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.04/24.97  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 36.04/24.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.04/24.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 36.04/24.97  tff('#skF_2', type, '#skF_2': $i).
% 36.04/24.97  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 36.04/24.97  tff('#skF_1', type, '#skF_1': $i).
% 36.04/24.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.04/24.97  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 36.04/24.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 36.04/24.97  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 36.04/24.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.04/24.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.04/24.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 36.04/24.97  
% 36.04/24.98  tff(f_91, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 36.04/24.98  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 36.04/24.98  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 36.04/24.98  tff(f_62, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 36.04/24.98  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 36.04/24.98  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 36.04/24.98  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_relat_1(k8_relat_1(A, B)) & v1_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_funct_1)).
% 36.04/24.98  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 36.04/24.98  tff(f_76, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(k8_relat_1(A, C), B) = k3_xboole_0(A, k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_funct_1)).
% 36.04/24.98  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 36.04/24.98  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 36.04/24.98  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 36.04/24.98  tff(c_30, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.04/24.98  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.04/24.98  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.04/24.98  tff(c_12, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=k8_relat_1(A_12, B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 36.04/24.98  tff(c_6, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 36.04/24.98  tff(c_18, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_62])).
% 36.04/24.98  tff(c_223, plain, (![A_54, B_55]: (k10_relat_1(A_54, k1_relat_1(B_55))=k1_relat_1(k5_relat_1(A_54, B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 36.04/24.98  tff(c_235, plain, (![A_54, A_18]: (k1_relat_1(k5_relat_1(A_54, k6_relat_1(A_18)))=k10_relat_1(A_54, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_18, c_223])).
% 36.04/24.98  tff(c_309, plain, (![A_61, A_62]: (k1_relat_1(k5_relat_1(A_61, k6_relat_1(A_62)))=k10_relat_1(A_61, A_62) | ~v1_relat_1(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_235])).
% 36.04/24.98  tff(c_324, plain, (![A_12, B_13]: (k1_relat_1(k8_relat_1(A_12, B_13))=k10_relat_1(B_13, A_12) | ~v1_relat_1(B_13) | ~v1_relat_1(B_13))), inference(superposition, [status(thm), theory('equality')], [c_12, c_309])).
% 36.04/24.98  tff(c_32, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.04/24.98  tff(c_144, plain, (![A_49, B_50]: (k2_relat_1(k8_relat_1(A_49, B_50))=A_49 | ~r1_tarski(A_49, k2_relat_1(B_50)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.04/24.98  tff(c_158, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_144])).
% 36.04/24.98  tff(c_166, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_158])).
% 36.04/24.98  tff(c_24, plain, (![A_19, B_20]: (v1_relat_1(k8_relat_1(A_19, B_20)) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 36.04/24.98  tff(c_8, plain, (![B_9, A_8]: (k3_xboole_0(k2_relat_1(B_9), A_8)=k2_relat_1(k8_relat_1(A_8, B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 36.04/24.98  tff(c_175, plain, (![A_8]: (k2_relat_1(k8_relat_1(A_8, k8_relat_1('#skF_1', '#skF_2')))=k3_xboole_0('#skF_1', A_8) | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_166, c_8])).
% 36.04/24.98  tff(c_179, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_175])).
% 36.04/24.98  tff(c_182, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_179])).
% 36.04/24.98  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_182])).
% 36.04/24.98  tff(c_188, plain, (v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_175])).
% 36.04/24.98  tff(c_421, plain, (![A_69, C_70, B_71]: (k9_relat_1(k8_relat_1(A_69, C_70), B_71)=k3_xboole_0(A_69, k9_relat_1(C_70, B_71)) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_76])).
% 36.04/24.98  tff(c_14, plain, (![A_14]: (k9_relat_1(A_14, k1_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 36.04/24.98  tff(c_1711, plain, (![A_149, C_150]: (k3_xboole_0(A_149, k9_relat_1(C_150, k1_relat_1(k8_relat_1(A_149, C_150))))=k2_relat_1(k8_relat_1(A_149, C_150)) | ~v1_relat_1(k8_relat_1(A_149, C_150)) | ~v1_funct_1(C_150) | ~v1_relat_1(C_150))), inference(superposition, [status(thm), theory('equality')], [c_421, c_14])).
% 36.04/24.98  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 36.04/24.98  tff(c_163, plain, (![A_1, C_3, B_50]: (k2_relat_1(k8_relat_1(k3_xboole_0(A_1, C_3), B_50))=k3_xboole_0(A_1, C_3) | ~v1_relat_1(B_50) | ~r1_tarski(A_1, k2_relat_1(B_50)))), inference(resolution, [status(thm)], [c_2, c_144])).
% 36.04/24.98  tff(c_40791, plain, (![A_1060, C_1061, B_1062]: (k3_xboole_0(A_1060, k9_relat_1(C_1061, k1_relat_1(k8_relat_1(A_1060, C_1061))))=k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(A_1060, C_1061)), B_1062)) | ~v1_relat_1(B_1062) | ~r1_tarski(A_1060, k2_relat_1(B_1062)) | ~v1_relat_1(k8_relat_1(A_1060, C_1061)) | ~v1_funct_1(C_1061) | ~v1_relat_1(C_1061))), inference(superposition, [status(thm), theory('equality')], [c_1711, c_163])).
% 36.04/24.98  tff(c_41632, plain, (![B_1062]: (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k1_relat_1(k8_relat_1('#skF_1', '#skF_2'))))=k2_relat_1(k8_relat_1('#skF_1', B_1062)) | ~v1_relat_1(B_1062) | ~r1_tarski('#skF_1', k2_relat_1(B_1062)) | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_40791])).
% 36.04/24.98  tff(c_76805, plain, (![B_1467]: (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k1_relat_1(k8_relat_1('#skF_1', '#skF_2'))))=k2_relat_1(k8_relat_1('#skF_1', B_1467)) | ~v1_relat_1(B_1467) | ~r1_tarski('#skF_1', k2_relat_1(B_1467)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_188, c_41632])).
% 36.04/24.98  tff(c_76867, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k1_relat_1(k8_relat_1('#skF_1', '#skF_2'))))=k2_relat_1(k8_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_76805])).
% 36.04/24.98  tff(c_76874, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k1_relat_1(k8_relat_1('#skF_1', '#skF_2'))))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_166, c_76867])).
% 36.04/24.98  tff(c_77409, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')))='#skF_1' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_324, c_76874])).
% 36.24/24.98  tff(c_77472, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_77409])).
% 36.24/24.98  tff(c_20, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_62])).
% 36.24/24.98  tff(c_28, plain, (![B_25, A_24]: (r1_tarski(k9_relat_1(B_25, k10_relat_1(B_25, A_24)), A_24) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_82])).
% 36.24/24.98  tff(c_2648, plain, (![B_183, B_184]: (k2_relat_1(k8_relat_1(k9_relat_1(B_183, k10_relat_1(B_183, k2_relat_1(B_184))), B_184))=k9_relat_1(B_183, k10_relat_1(B_183, k2_relat_1(B_184))) | ~v1_relat_1(B_184) | ~v1_funct_1(B_183) | ~v1_relat_1(B_183))), inference(resolution, [status(thm)], [c_28, c_144])).
% 36.24/24.98  tff(c_91, plain, (![B_40, A_41]: (k3_xboole_0(k2_relat_1(B_40), A_41)=k2_relat_1(k8_relat_1(A_41, B_40)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 36.24/24.98  tff(c_103, plain, (![A_41, A_18]: (k2_relat_1(k8_relat_1(A_41, k6_relat_1(A_18)))=k3_xboole_0(A_18, A_41) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_91])).
% 36.24/24.98  tff(c_107, plain, (![A_41, A_18]: (k2_relat_1(k8_relat_1(A_41, k6_relat_1(A_18)))=k3_xboole_0(A_18, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_103])).
% 36.24/24.98  tff(c_2683, plain, (![A_18, B_183]: (k3_xboole_0(A_18, k9_relat_1(B_183, k10_relat_1(B_183, k2_relat_1(k6_relat_1(A_18)))))=k9_relat_1(B_183, k10_relat_1(B_183, k2_relat_1(k6_relat_1(A_18)))) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_funct_1(B_183) | ~v1_relat_1(B_183))), inference(superposition, [status(thm), theory('equality')], [c_2648, c_107])).
% 36.24/24.98  tff(c_2735, plain, (![A_18, B_183]: (k3_xboole_0(A_18, k9_relat_1(B_183, k10_relat_1(B_183, A_18)))=k9_relat_1(B_183, k10_relat_1(B_183, A_18)) | ~v1_funct_1(B_183) | ~v1_relat_1(B_183))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20, c_20, c_2683])).
% 36.24/24.98  tff(c_77880, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_77472, c_2735])).
% 36.24/24.98  tff(c_78047, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_77880])).
% 36.24/24.98  tff(c_78049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_78047])).
% 36.24/24.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.24/24.98  
% 36.24/24.98  Inference rules
% 36.24/24.98  ----------------------
% 36.24/24.98  #Ref     : 0
% 36.24/24.98  #Sup     : 21647
% 36.24/24.98  #Fact    : 0
% 36.24/24.98  #Define  : 0
% 36.24/24.98  #Split   : 20
% 36.24/24.98  #Chain   : 0
% 36.24/24.98  #Close   : 0
% 36.24/24.98  
% 36.24/24.98  Ordering : KBO
% 36.24/24.98  
% 36.24/24.98  Simplification rules
% 36.24/24.98  ----------------------
% 36.24/24.98  #Subsume      : 6803
% 36.24/24.98  #Demod        : 9648
% 36.24/24.98  #Tautology    : 341
% 36.24/24.98  #SimpNegUnit  : 1
% 36.24/24.98  #BackRed      : 1
% 36.24/24.98  
% 36.24/24.98  #Partial instantiations: 0
% 36.24/24.98  #Strategies tried      : 1
% 36.24/24.98  
% 36.24/24.98  Timing (in seconds)
% 36.24/24.98  ----------------------
% 36.24/24.98  Preprocessing        : 0.30
% 36.24/24.98  Parsing              : 0.17
% 36.24/24.98  CNF conversion       : 0.02
% 36.24/24.98  Main loop            : 23.89
% 36.24/24.99  Inferencing          : 2.26
% 36.24/24.99  Reduction            : 3.59
% 36.24/24.99  Demodulation         : 2.67
% 36.24/24.99  BG Simplification    : 0.36
% 36.24/24.99  Subsumption          : 16.95
% 36.24/24.99  Abstraction          : 0.49
% 36.24/24.99  MUC search           : 0.00
% 36.24/24.99  Cooper               : 0.00
% 36.24/24.99  Total                : 24.23
% 36.24/24.99  Index Insertion      : 0.00
% 36.24/24.99  Index Deletion       : 0.00
% 36.24/24.99  Index Matching       : 0.00
% 36.24/24.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
