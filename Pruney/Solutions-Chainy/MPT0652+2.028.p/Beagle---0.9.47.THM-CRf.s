%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:56 EST 2020

% Result     : Theorem 7.01s
% Output     : CNFRefutation 7.03s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 188 expanded)
%              Number of leaves         :   28 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 ( 515 expanded)
%              Number of equality atoms :   29 ( 130 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    ! [A_18] :
      ( v1_relat_1(k2_funct_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_relat_1(A_16),B_17) = k7_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3176,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_144,B_145)),k2_relat_1(B_145))
      | ~ v1_relat_1(B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3185,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_17,A_16)),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3176])).

tff(c_3210,plain,(
    ! [B_148,A_149] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_148,A_149)),k2_relat_1(B_148))
      | ~ v1_relat_1(B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_3185])).

tff(c_3223,plain,(
    ! [B_150,A_151] :
      ( r1_tarski(k9_relat_1(B_150,A_151),k2_relat_1(B_150))
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(B_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3210])).

tff(c_3236,plain,(
    ! [A_152] :
      ( r1_tarski(k2_relat_1(A_152),k2_relat_1(A_152))
      | ~ v1_relat_1(A_152)
      | ~ v1_relat_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3223])).

tff(c_3488,plain,(
    ! [A_171] :
      ( r1_tarski(k2_relat_1(k4_relat_1(A_171)),k1_relat_1(A_171))
      | ~ v1_relat_1(k4_relat_1(A_171))
      | ~ v1_relat_1(k4_relat_1(A_171))
      | ~ v1_relat_1(k4_relat_1(A_171))
      | ~ v1_relat_1(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3236])).

tff(c_3503,plain,(
    ! [A_6] :
      ( r1_tarski(k1_relat_1(A_6),k1_relat_1(A_6))
      | ~ v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3488])).

tff(c_26,plain,(
    ! [A_19] :
      ( k2_relat_1(k2_funct_1(A_19)) = k1_relat_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3255,plain,(
    ! [B_153,A_154] :
      ( k2_relat_1(k5_relat_1(B_153,A_154)) = k2_relat_1(A_154)
      | ~ r1_tarski(k1_relat_1(A_154),k2_relat_1(B_153))
      | ~ v1_relat_1(B_153)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5172,plain,(
    ! [A_228,A_229] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_228),A_229)) = k2_relat_1(A_229)
      | ~ r1_tarski(k1_relat_1(A_229),k1_relat_1(A_228))
      | ~ v1_relat_1(k2_funct_1(A_228))
      | ~ v1_relat_1(A_229)
      | ~ v2_funct_1(A_228)
      | ~ v1_funct_1(A_228)
      | ~ v1_relat_1(A_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3255])).

tff(c_5253,plain,(
    ! [A_230] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_230),A_230)) = k2_relat_1(A_230)
      | ~ v1_relat_1(k2_funct_1(A_230))
      | ~ v2_funct_1(A_230)
      | ~ v1_funct_1(A_230)
      | ~ v1_relat_1(k4_relat_1(A_230))
      | ~ v1_relat_1(A_230) ) ),
    inference(resolution,[status(thm)],[c_3503,c_5172])).

tff(c_28,plain,(
    ! [A_19] :
      ( k1_relat_1(k2_funct_1(A_19)) = k2_relat_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_90,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_31,B_32)),k2_relat_1(B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_93,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_17,A_16)),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_90])).

tff(c_114,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_34,A_35)),k2_relat_1(B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_93])).

tff(c_124,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(k9_relat_1(B_36,A_37),k2_relat_1(B_36))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_114])).

tff(c_168,plain,(
    ! [A_41] :
      ( r1_tarski(k2_relat_1(A_41),k2_relat_1(A_41))
      | ~ v1_relat_1(A_41)
      | ~ v1_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_124])).

tff(c_2959,plain,(
    ! [A_135] :
      ( r1_tarski(k2_relat_1(k2_funct_1(A_135)),k1_relat_1(A_135))
      | ~ v1_relat_1(k2_funct_1(A_135))
      | ~ v1_relat_1(k2_funct_1(A_135))
      | ~ v1_relat_1(k2_funct_1(A_135))
      | ~ v2_funct_1(A_135)
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_168])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( k1_relat_1(k5_relat_1(A_10,B_12)) = k1_relat_1(A_10)
      | ~ r1_tarski(k2_relat_1(A_10),k1_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2997,plain,(
    ! [A_136] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_136),A_136)) = k1_relat_1(k2_funct_1(A_136))
      | ~ v1_relat_1(k2_funct_1(A_136))
      | ~ v2_funct_1(A_136)
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(resolution,[status(thm)],[c_2959,c_16])).

tff(c_30,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_59,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_3090,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2997,c_59])).

tff(c_3096,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_3090])).

tff(c_3098,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3096])).

tff(c_3101,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_3098])).

tff(c_3105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_3101])).

tff(c_3106,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3096])).

tff(c_3110,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3106])).

tff(c_3114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_3110])).

tff(c_3115,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_5338,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5253,c_3115])).

tff(c_5345,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_5338])).

tff(c_5347,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5345])).

tff(c_5350,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_5347])).

tff(c_5354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5350])).

tff(c_5355,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5345])).

tff(c_5359,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_5355])).

tff(c_5363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_5359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.01/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.03/2.35  
% 7.03/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.03/2.35  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 7.03/2.35  
% 7.03/2.35  %Foreground sorts:
% 7.03/2.35  
% 7.03/2.35  
% 7.03/2.35  %Background operators:
% 7.03/2.35  
% 7.03/2.35  
% 7.03/2.35  %Foreground operators:
% 7.03/2.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.03/2.35  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.03/2.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.03/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.03/2.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.03/2.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.03/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.03/2.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.03/2.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.03/2.35  tff('#skF_1', type, '#skF_1': $i).
% 7.03/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.03/2.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.03/2.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.03/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.03/2.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.03/2.35  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.03/2.35  
% 7.03/2.36  tff(f_103, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 7.03/2.36  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.03/2.36  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 7.03/2.36  tff(f_45, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 7.03/2.36  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 7.03/2.36  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 7.03/2.36  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 7.03/2.36  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 7.03/2.36  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 7.03/2.36  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.03/2.36  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 7.03/2.36  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 7.03/2.36  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.03/2.36  tff(c_34, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.03/2.36  tff(c_24, plain, (![A_18]: (v1_relat_1(k2_funct_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.03/2.36  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.03/2.36  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.03/2.36  tff(c_10, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.03/2.36  tff(c_6, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.03/2.36  tff(c_8, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.03/2.36  tff(c_4, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.03/2.36  tff(c_20, plain, (![A_16, B_17]: (k5_relat_1(k6_relat_1(A_16), B_17)=k7_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.03/2.36  tff(c_3176, plain, (![A_144, B_145]: (r1_tarski(k2_relat_1(k5_relat_1(A_144, B_145)), k2_relat_1(B_145)) | ~v1_relat_1(B_145) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.03/2.36  tff(c_3185, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(k7_relat_1(B_17, A_16)), k2_relat_1(B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3176])).
% 7.03/2.36  tff(c_3210, plain, (![B_148, A_149]: (r1_tarski(k2_relat_1(k7_relat_1(B_148, A_149)), k2_relat_1(B_148)) | ~v1_relat_1(B_148))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_3185])).
% 7.03/2.36  tff(c_3223, plain, (![B_150, A_151]: (r1_tarski(k9_relat_1(B_150, A_151), k2_relat_1(B_150)) | ~v1_relat_1(B_150) | ~v1_relat_1(B_150))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3210])).
% 7.03/2.36  tff(c_3236, plain, (![A_152]: (r1_tarski(k2_relat_1(A_152), k2_relat_1(A_152)) | ~v1_relat_1(A_152) | ~v1_relat_1(A_152) | ~v1_relat_1(A_152))), inference(superposition, [status(thm), theory('equality')], [c_6, c_3223])).
% 7.03/2.36  tff(c_3488, plain, (![A_171]: (r1_tarski(k2_relat_1(k4_relat_1(A_171)), k1_relat_1(A_171)) | ~v1_relat_1(k4_relat_1(A_171)) | ~v1_relat_1(k4_relat_1(A_171)) | ~v1_relat_1(k4_relat_1(A_171)) | ~v1_relat_1(A_171))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3236])).
% 7.03/2.36  tff(c_3503, plain, (![A_6]: (r1_tarski(k1_relat_1(A_6), k1_relat_1(A_6)) | ~v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3488])).
% 7.03/2.36  tff(c_26, plain, (![A_19]: (k2_relat_1(k2_funct_1(A_19))=k1_relat_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.03/2.36  tff(c_3255, plain, (![B_153, A_154]: (k2_relat_1(k5_relat_1(B_153, A_154))=k2_relat_1(A_154) | ~r1_tarski(k1_relat_1(A_154), k2_relat_1(B_153)) | ~v1_relat_1(B_153) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.03/2.36  tff(c_5172, plain, (![A_228, A_229]: (k2_relat_1(k5_relat_1(k2_funct_1(A_228), A_229))=k2_relat_1(A_229) | ~r1_tarski(k1_relat_1(A_229), k1_relat_1(A_228)) | ~v1_relat_1(k2_funct_1(A_228)) | ~v1_relat_1(A_229) | ~v2_funct_1(A_228) | ~v1_funct_1(A_228) | ~v1_relat_1(A_228))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3255])).
% 7.03/2.36  tff(c_5253, plain, (![A_230]: (k2_relat_1(k5_relat_1(k2_funct_1(A_230), A_230))=k2_relat_1(A_230) | ~v1_relat_1(k2_funct_1(A_230)) | ~v2_funct_1(A_230) | ~v1_funct_1(A_230) | ~v1_relat_1(k4_relat_1(A_230)) | ~v1_relat_1(A_230))), inference(resolution, [status(thm)], [c_3503, c_5172])).
% 7.03/2.36  tff(c_28, plain, (![A_19]: (k1_relat_1(k2_funct_1(A_19))=k2_relat_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.03/2.36  tff(c_90, plain, (![A_31, B_32]: (r1_tarski(k2_relat_1(k5_relat_1(A_31, B_32)), k2_relat_1(B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.03/2.36  tff(c_93, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(k7_relat_1(B_17, A_16)), k2_relat_1(B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_90])).
% 7.03/2.36  tff(c_114, plain, (![B_34, A_35]: (r1_tarski(k2_relat_1(k7_relat_1(B_34, A_35)), k2_relat_1(B_34)) | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_93])).
% 7.03/2.36  tff(c_124, plain, (![B_36, A_37]: (r1_tarski(k9_relat_1(B_36, A_37), k2_relat_1(B_36)) | ~v1_relat_1(B_36) | ~v1_relat_1(B_36))), inference(superposition, [status(thm), theory('equality')], [c_8, c_114])).
% 7.03/2.36  tff(c_168, plain, (![A_41]: (r1_tarski(k2_relat_1(A_41), k2_relat_1(A_41)) | ~v1_relat_1(A_41) | ~v1_relat_1(A_41) | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_6, c_124])).
% 7.03/2.36  tff(c_2959, plain, (![A_135]: (r1_tarski(k2_relat_1(k2_funct_1(A_135)), k1_relat_1(A_135)) | ~v1_relat_1(k2_funct_1(A_135)) | ~v1_relat_1(k2_funct_1(A_135)) | ~v1_relat_1(k2_funct_1(A_135)) | ~v2_funct_1(A_135) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_26, c_168])).
% 7.03/2.36  tff(c_16, plain, (![A_10, B_12]: (k1_relat_1(k5_relat_1(A_10, B_12))=k1_relat_1(A_10) | ~r1_tarski(k2_relat_1(A_10), k1_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.03/2.36  tff(c_2997, plain, (![A_136]: (k1_relat_1(k5_relat_1(k2_funct_1(A_136), A_136))=k1_relat_1(k2_funct_1(A_136)) | ~v1_relat_1(k2_funct_1(A_136)) | ~v2_funct_1(A_136) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(resolution, [status(thm)], [c_2959, c_16])).
% 7.03/2.36  tff(c_30, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.03/2.36  tff(c_59, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 7.03/2.36  tff(c_3090, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2997, c_59])).
% 7.03/2.36  tff(c_3096, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_3090])).
% 7.03/2.36  tff(c_3098, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_3096])).
% 7.03/2.36  tff(c_3101, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_3098])).
% 7.03/2.36  tff(c_3105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_3101])).
% 7.03/2.36  tff(c_3106, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_3096])).
% 7.03/2.36  tff(c_3110, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_3106])).
% 7.03/2.36  tff(c_3114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_3110])).
% 7.03/2.36  tff(c_3115, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 7.03/2.36  tff(c_5338, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5253, c_3115])).
% 7.03/2.36  tff(c_5345, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k4_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_5338])).
% 7.03/2.36  tff(c_5347, plain, (~v1_relat_1(k4_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_5345])).
% 7.03/2.36  tff(c_5350, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2, c_5347])).
% 7.03/2.36  tff(c_5354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_5350])).
% 7.03/2.36  tff(c_5355, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_5345])).
% 7.03/2.36  tff(c_5359, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_5355])).
% 7.03/2.36  tff(c_5363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_5359])).
% 7.03/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.03/2.36  
% 7.03/2.36  Inference rules
% 7.03/2.36  ----------------------
% 7.03/2.36  #Ref     : 0
% 7.03/2.36  #Sup     : 1560
% 7.03/2.36  #Fact    : 0
% 7.03/2.36  #Define  : 0
% 7.03/2.36  #Split   : 4
% 7.03/2.36  #Chain   : 0
% 7.03/2.36  #Close   : 0
% 7.03/2.36  
% 7.03/2.36  Ordering : KBO
% 7.03/2.36  
% 7.03/2.36  Simplification rules
% 7.03/2.36  ----------------------
% 7.03/2.36  #Subsume      : 143
% 7.03/2.36  #Demod        : 99
% 7.03/2.36  #Tautology    : 126
% 7.03/2.36  #SimpNegUnit  : 0
% 7.03/2.36  #BackRed      : 0
% 7.03/2.36  
% 7.03/2.36  #Partial instantiations: 0
% 7.03/2.36  #Strategies tried      : 1
% 7.03/2.36  
% 7.03/2.36  Timing (in seconds)
% 7.03/2.36  ----------------------
% 7.03/2.37  Preprocessing        : 0.29
% 7.03/2.37  Parsing              : 0.16
% 7.03/2.37  CNF conversion       : 0.02
% 7.03/2.37  Main loop            : 1.36
% 7.03/2.37  Inferencing          : 0.47
% 7.03/2.37  Reduction            : 0.41
% 7.03/2.37  Demodulation         : 0.29
% 7.03/2.37  BG Simplification    : 0.08
% 7.03/2.37  Subsumption          : 0.32
% 7.03/2.37  Abstraction          : 0.07
% 7.03/2.37  MUC search           : 0.00
% 7.03/2.37  Cooper               : 0.00
% 7.03/2.37  Total                : 1.69
% 7.03/2.37  Index Insertion      : 0.00
% 7.03/2.37  Index Deletion       : 0.00
% 7.03/2.37  Index Matching       : 0.00
% 7.03/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
