%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:26 EST 2020

% Result     : Theorem 8.31s
% Output     : CNFRefutation 8.31s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 179 expanded)
%              Number of leaves         :   43 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          :  127 ( 294 expanded)
%              Number of equality atoms :   44 (  99 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_68,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') != k10_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_74,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_70,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_97,plain,(
    ! [A_74,B_75] :
      ( k2_xboole_0(A_74,B_75) = B_75
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_104,plain,(
    k2_xboole_0(k10_relat_1('#skF_4','#skF_6'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_70,c_97])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,(
    ! [A_59] : v1_relat_1(k6_relat_1(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    ! [A_46] : k1_relat_1(k6_relat_1(A_46)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    ! [A_46] : k2_relat_1(k6_relat_1(A_46)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_147,plain,(
    ! [A_83] :
      ( k10_relat_1(A_83,k2_relat_1(A_83)) = k1_relat_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_156,plain,(
    ! [A_46] :
      ( k10_relat_1(k6_relat_1(A_46),A_46) = k1_relat_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_147])).

tff(c_160,plain,(
    ! [A_46] : k10_relat_1(k6_relat_1(A_46),A_46) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_36,c_156])).

tff(c_60,plain,(
    ! [A_59] : v1_funct_1(k6_relat_1(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1470,plain,(
    ! [B_187,A_188] :
      ( k9_relat_1(B_187,k10_relat_1(B_187,A_188)) = A_188
      | ~ r1_tarski(A_188,k2_relat_1(B_187))
      | ~ v1_funct_1(B_187)
      | ~ v1_relat_1(B_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1475,plain,(
    ! [A_46,A_188] :
      ( k9_relat_1(k6_relat_1(A_46),k10_relat_1(k6_relat_1(A_46),A_188)) = A_188
      | ~ r1_tarski(A_188,A_46)
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1470])).

tff(c_1483,plain,(
    ! [A_189,A_190] :
      ( k9_relat_1(k6_relat_1(A_189),k10_relat_1(k6_relat_1(A_189),A_190)) = A_190
      | ~ r1_tarski(A_190,A_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_1475])).

tff(c_1492,plain,(
    ! [A_46] :
      ( k9_relat_1(k6_relat_1(A_46),A_46) = A_46
      | ~ r1_tarski(A_46,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_1483])).

tff(c_1500,plain,(
    ! [A_46] : k9_relat_1(k6_relat_1(A_46),A_46) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1492])).

tff(c_105,plain,(
    ! [B_7] : k2_xboole_0(B_7,B_7) = B_7 ),
    inference(resolution,[status(thm)],[c_12,c_97])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1178,plain,(
    ! [D_168,A_169,B_170] :
      ( r2_hidden(D_168,k1_relat_1(A_169))
      | ~ r2_hidden(D_168,k10_relat_1(A_169,B_170))
      | ~ v1_funct_1(A_169)
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8978,plain,(
    ! [A_406,B_407,B_408] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_406,B_407),B_408),k1_relat_1(A_406))
      | ~ v1_funct_1(A_406)
      | ~ v1_relat_1(A_406)
      | r1_tarski(k10_relat_1(A_406,B_407),B_408) ) ),
    inference(resolution,[status(thm)],[c_6,c_1178])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9035,plain,(
    ! [A_409,B_410] :
      ( ~ v1_funct_1(A_409)
      | ~ v1_relat_1(A_409)
      | r1_tarski(k10_relat_1(A_409,B_410),k1_relat_1(A_409)) ) ),
    inference(resolution,[status(thm)],[c_8978,c_4])).

tff(c_9097,plain,(
    ! [A_46,B_410] :
      ( ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46))
      | r1_tarski(k10_relat_1(k6_relat_1(A_46),B_410),A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_9035])).

tff(c_9118,plain,(
    ! [A_46,B_410] : r1_tarski(k10_relat_1(k6_relat_1(A_46),B_410),A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_9097])).

tff(c_9124,plain,(
    ! [A_411,B_412] : r1_tarski(k10_relat_1(k6_relat_1(A_411),B_412),A_411) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_9097])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_9182,plain,(
    ! [A_411,B_412] : k2_xboole_0(k10_relat_1(k6_relat_1(A_411),B_412),A_411) = A_411 ),
    inference(resolution,[status(thm)],[c_9124,c_16])).

tff(c_1698,plain,(
    ! [C_199,A_200,B_201] :
      ( k2_xboole_0(k10_relat_1(C_199,A_200),k10_relat_1(C_199,B_201)) = k10_relat_1(C_199,k2_xboole_0(A_200,B_201))
      | ~ v1_relat_1(C_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1776,plain,(
    ! [A_46,A_200] :
      ( k2_xboole_0(k10_relat_1(k6_relat_1(A_46),A_200),A_46) = k10_relat_1(k6_relat_1(A_46),k2_xboole_0(A_200,A_46))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_1698])).

tff(c_1797,plain,(
    ! [A_46,A_200] : k2_xboole_0(k10_relat_1(k6_relat_1(A_46),A_200),A_46) = k10_relat_1(k6_relat_1(A_46),k2_xboole_0(A_200,A_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1776])).

tff(c_9545,plain,(
    ! [A_418,A_419] : k10_relat_1(k6_relat_1(A_418),k2_xboole_0(A_419,A_418)) = A_418 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9182,c_1797])).

tff(c_179,plain,(
    ! [A_89,C_90,B_91] :
      ( r1_tarski(A_89,C_90)
      | ~ r1_tarski(k2_xboole_0(A_89,B_91),C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_190,plain,(
    ! [A_89,B_91] : r1_tarski(A_89,k2_xboole_0(A_89,B_91)) ),
    inference(resolution,[status(thm)],[c_12,c_179])).

tff(c_1750,plain,(
    ! [C_199,A_200,B_201] :
      ( r1_tarski(k10_relat_1(C_199,A_200),k10_relat_1(C_199,k2_xboole_0(A_200,B_201)))
      | ~ v1_relat_1(C_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1698,c_190])).

tff(c_9705,plain,(
    ! [A_418,A_419,B_201] :
      ( r1_tarski(A_418,k10_relat_1(k6_relat_1(A_418),k2_xboole_0(k2_xboole_0(A_419,A_418),B_201)))
      | ~ v1_relat_1(k6_relat_1(A_418)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9545,c_1750])).

tff(c_11784,plain,(
    ! [A_457,A_458,B_459] : r1_tarski(A_457,k10_relat_1(k6_relat_1(A_457),k2_xboole_0(k2_xboole_0(A_458,A_457),B_459))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_9705])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11833,plain,(
    ! [A_457,A_458,B_459] :
      ( k10_relat_1(k6_relat_1(A_457),k2_xboole_0(k2_xboole_0(A_458,A_457),B_459)) = A_457
      | ~ r1_tarski(k10_relat_1(k6_relat_1(A_457),k2_xboole_0(k2_xboole_0(A_458,A_457),B_459)),A_457) ) ),
    inference(resolution,[status(thm)],[c_11784,c_8])).

tff(c_11938,plain,(
    ! [A_460,A_461,B_462] : k10_relat_1(k6_relat_1(A_460),k2_xboole_0(k2_xboole_0(A_461,A_460),B_462)) = A_460 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9118,c_11833])).

tff(c_12502,plain,(
    ! [B_468,B_469] : k10_relat_1(k6_relat_1(B_468),k2_xboole_0(B_468,B_469)) = B_468 ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_11938])).

tff(c_2239,plain,(
    ! [A_220,B_221] :
      ( k3_xboole_0(A_220,k9_relat_1(B_221,k1_relat_1(B_221))) = k9_relat_1(B_221,k10_relat_1(B_221,A_220))
      | ~ v1_funct_1(B_221)
      | ~ v1_relat_1(B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2251,plain,(
    ! [A_46,A_220] :
      ( k9_relat_1(k6_relat_1(A_46),k10_relat_1(k6_relat_1(A_46),A_220)) = k3_xboole_0(A_220,k9_relat_1(k6_relat_1(A_46),A_46))
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2239])).

tff(c_2255,plain,(
    ! [A_46,A_220] : k9_relat_1(k6_relat_1(A_46),k10_relat_1(k6_relat_1(A_46),A_220)) = k3_xboole_0(A_220,A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_1500,c_2251])).

tff(c_12589,plain,(
    ! [B_468,B_469] : k9_relat_1(k6_relat_1(B_468),B_468) = k3_xboole_0(k2_xboole_0(B_468,B_469),B_468) ),
    inference(superposition,[status(thm),theory(equality)],[c_12502,c_2255])).

tff(c_12713,plain,(
    ! [B_470,B_471] : k3_xboole_0(k2_xboole_0(B_470,B_471),B_470) = B_470 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1500,c_12589])).

tff(c_12787,plain,(
    k3_xboole_0('#skF_5',k10_relat_1('#skF_4','#skF_6')) = k10_relat_1('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_12713])).

tff(c_62,plain,(
    ! [A_60,C_62,B_61] :
      ( k3_xboole_0(A_60,k10_relat_1(C_62,B_61)) = k10_relat_1(k7_relat_1(C_62,A_60),B_61)
      | ~ v1_relat_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_13746,plain,
    ( k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12787,c_62])).

tff(c_13753,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_13746])).

tff(c_13755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_13753])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:02:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.31/3.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/3.13  
% 8.31/3.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/3.14  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 8.31/3.14  
% 8.31/3.14  %Foreground sorts:
% 8.31/3.14  
% 8.31/3.14  
% 8.31/3.14  %Background operators:
% 8.31/3.14  
% 8.31/3.14  
% 8.31/3.14  %Foreground operators:
% 8.31/3.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.31/3.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.31/3.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.31/3.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.31/3.14  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.31/3.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.31/3.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.31/3.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.31/3.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.31/3.14  tff('#skF_5', type, '#skF_5': $i).
% 8.31/3.14  tff('#skF_6', type, '#skF_6': $i).
% 8.31/3.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.31/3.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.31/3.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.31/3.14  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.31/3.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.31/3.14  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.31/3.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.31/3.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.31/3.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.31/3.14  tff('#skF_4', type, '#skF_4': $i).
% 8.31/3.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.31/3.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.31/3.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.31/3.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.31/3.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.31/3.14  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.31/3.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.31/3.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.31/3.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.31/3.14  
% 8.31/3.15  tff(f_118, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 8.31/3.15  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.31/3.15  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.31/3.15  tff(f_90, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 8.31/3.15  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.31/3.15  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 8.31/3.15  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 8.31/3.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.31/3.15  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 8.31/3.15  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 8.31/3.15  tff(f_42, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 8.31/3.15  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 8.31/3.15  tff(f_94, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 8.31/3.15  tff(c_68, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.31/3.15  tff(c_74, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.31/3.15  tff(c_70, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.31/3.15  tff(c_97, plain, (![A_74, B_75]: (k2_xboole_0(A_74, B_75)=B_75 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.31/3.15  tff(c_104, plain, (k2_xboole_0(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_70, c_97])).
% 8.31/3.15  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.31/3.15  tff(c_58, plain, (![A_59]: (v1_relat_1(k6_relat_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.31/3.15  tff(c_36, plain, (![A_46]: (k1_relat_1(k6_relat_1(A_46))=A_46)), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.31/3.15  tff(c_38, plain, (![A_46]: (k2_relat_1(k6_relat_1(A_46))=A_46)), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.31/3.15  tff(c_147, plain, (![A_83]: (k10_relat_1(A_83, k2_relat_1(A_83))=k1_relat_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.31/3.15  tff(c_156, plain, (![A_46]: (k10_relat_1(k6_relat_1(A_46), A_46)=k1_relat_1(k6_relat_1(A_46)) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_147])).
% 8.31/3.15  tff(c_160, plain, (![A_46]: (k10_relat_1(k6_relat_1(A_46), A_46)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_36, c_156])).
% 8.31/3.15  tff(c_60, plain, (![A_59]: (v1_funct_1(k6_relat_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.31/3.15  tff(c_1470, plain, (![B_187, A_188]: (k9_relat_1(B_187, k10_relat_1(B_187, A_188))=A_188 | ~r1_tarski(A_188, k2_relat_1(B_187)) | ~v1_funct_1(B_187) | ~v1_relat_1(B_187))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.31/3.15  tff(c_1475, plain, (![A_46, A_188]: (k9_relat_1(k6_relat_1(A_46), k10_relat_1(k6_relat_1(A_46), A_188))=A_188 | ~r1_tarski(A_188, A_46) | ~v1_funct_1(k6_relat_1(A_46)) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1470])).
% 8.31/3.15  tff(c_1483, plain, (![A_189, A_190]: (k9_relat_1(k6_relat_1(A_189), k10_relat_1(k6_relat_1(A_189), A_190))=A_190 | ~r1_tarski(A_190, A_189))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_1475])).
% 8.31/3.15  tff(c_1492, plain, (![A_46]: (k9_relat_1(k6_relat_1(A_46), A_46)=A_46 | ~r1_tarski(A_46, A_46))), inference(superposition, [status(thm), theory('equality')], [c_160, c_1483])).
% 8.31/3.15  tff(c_1500, plain, (![A_46]: (k9_relat_1(k6_relat_1(A_46), A_46)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1492])).
% 8.31/3.15  tff(c_105, plain, (![B_7]: (k2_xboole_0(B_7, B_7)=B_7)), inference(resolution, [status(thm)], [c_12, c_97])).
% 8.31/3.15  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.31/3.15  tff(c_1178, plain, (![D_168, A_169, B_170]: (r2_hidden(D_168, k1_relat_1(A_169)) | ~r2_hidden(D_168, k10_relat_1(A_169, B_170)) | ~v1_funct_1(A_169) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.31/3.15  tff(c_8978, plain, (![A_406, B_407, B_408]: (r2_hidden('#skF_1'(k10_relat_1(A_406, B_407), B_408), k1_relat_1(A_406)) | ~v1_funct_1(A_406) | ~v1_relat_1(A_406) | r1_tarski(k10_relat_1(A_406, B_407), B_408))), inference(resolution, [status(thm)], [c_6, c_1178])).
% 8.31/3.15  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.31/3.15  tff(c_9035, plain, (![A_409, B_410]: (~v1_funct_1(A_409) | ~v1_relat_1(A_409) | r1_tarski(k10_relat_1(A_409, B_410), k1_relat_1(A_409)))), inference(resolution, [status(thm)], [c_8978, c_4])).
% 8.31/3.15  tff(c_9097, plain, (![A_46, B_410]: (~v1_funct_1(k6_relat_1(A_46)) | ~v1_relat_1(k6_relat_1(A_46)) | r1_tarski(k10_relat_1(k6_relat_1(A_46), B_410), A_46))), inference(superposition, [status(thm), theory('equality')], [c_36, c_9035])).
% 8.31/3.15  tff(c_9118, plain, (![A_46, B_410]: (r1_tarski(k10_relat_1(k6_relat_1(A_46), B_410), A_46))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_9097])).
% 8.31/3.15  tff(c_9124, plain, (![A_411, B_412]: (r1_tarski(k10_relat_1(k6_relat_1(A_411), B_412), A_411))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_9097])).
% 8.31/3.15  tff(c_16, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.31/3.15  tff(c_9182, plain, (![A_411, B_412]: (k2_xboole_0(k10_relat_1(k6_relat_1(A_411), B_412), A_411)=A_411)), inference(resolution, [status(thm)], [c_9124, c_16])).
% 8.31/3.15  tff(c_1698, plain, (![C_199, A_200, B_201]: (k2_xboole_0(k10_relat_1(C_199, A_200), k10_relat_1(C_199, B_201))=k10_relat_1(C_199, k2_xboole_0(A_200, B_201)) | ~v1_relat_1(C_199))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.31/3.15  tff(c_1776, plain, (![A_46, A_200]: (k2_xboole_0(k10_relat_1(k6_relat_1(A_46), A_200), A_46)=k10_relat_1(k6_relat_1(A_46), k2_xboole_0(A_200, A_46)) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_1698])).
% 8.31/3.15  tff(c_1797, plain, (![A_46, A_200]: (k2_xboole_0(k10_relat_1(k6_relat_1(A_46), A_200), A_46)=k10_relat_1(k6_relat_1(A_46), k2_xboole_0(A_200, A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1776])).
% 8.31/3.15  tff(c_9545, plain, (![A_418, A_419]: (k10_relat_1(k6_relat_1(A_418), k2_xboole_0(A_419, A_418))=A_418)), inference(demodulation, [status(thm), theory('equality')], [c_9182, c_1797])).
% 8.31/3.15  tff(c_179, plain, (![A_89, C_90, B_91]: (r1_tarski(A_89, C_90) | ~r1_tarski(k2_xboole_0(A_89, B_91), C_90))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.31/3.15  tff(c_190, plain, (![A_89, B_91]: (r1_tarski(A_89, k2_xboole_0(A_89, B_91)))), inference(resolution, [status(thm)], [c_12, c_179])).
% 8.31/3.15  tff(c_1750, plain, (![C_199, A_200, B_201]: (r1_tarski(k10_relat_1(C_199, A_200), k10_relat_1(C_199, k2_xboole_0(A_200, B_201))) | ~v1_relat_1(C_199))), inference(superposition, [status(thm), theory('equality')], [c_1698, c_190])).
% 8.31/3.15  tff(c_9705, plain, (![A_418, A_419, B_201]: (r1_tarski(A_418, k10_relat_1(k6_relat_1(A_418), k2_xboole_0(k2_xboole_0(A_419, A_418), B_201))) | ~v1_relat_1(k6_relat_1(A_418)))), inference(superposition, [status(thm), theory('equality')], [c_9545, c_1750])).
% 8.31/3.15  tff(c_11784, plain, (![A_457, A_458, B_459]: (r1_tarski(A_457, k10_relat_1(k6_relat_1(A_457), k2_xboole_0(k2_xboole_0(A_458, A_457), B_459))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_9705])).
% 8.31/3.15  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.31/3.15  tff(c_11833, plain, (![A_457, A_458, B_459]: (k10_relat_1(k6_relat_1(A_457), k2_xboole_0(k2_xboole_0(A_458, A_457), B_459))=A_457 | ~r1_tarski(k10_relat_1(k6_relat_1(A_457), k2_xboole_0(k2_xboole_0(A_458, A_457), B_459)), A_457))), inference(resolution, [status(thm)], [c_11784, c_8])).
% 8.31/3.15  tff(c_11938, plain, (![A_460, A_461, B_462]: (k10_relat_1(k6_relat_1(A_460), k2_xboole_0(k2_xboole_0(A_461, A_460), B_462))=A_460)), inference(demodulation, [status(thm), theory('equality')], [c_9118, c_11833])).
% 8.31/3.15  tff(c_12502, plain, (![B_468, B_469]: (k10_relat_1(k6_relat_1(B_468), k2_xboole_0(B_468, B_469))=B_468)), inference(superposition, [status(thm), theory('equality')], [c_105, c_11938])).
% 8.31/3.15  tff(c_2239, plain, (![A_220, B_221]: (k3_xboole_0(A_220, k9_relat_1(B_221, k1_relat_1(B_221)))=k9_relat_1(B_221, k10_relat_1(B_221, A_220)) | ~v1_funct_1(B_221) | ~v1_relat_1(B_221))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.31/3.15  tff(c_2251, plain, (![A_46, A_220]: (k9_relat_1(k6_relat_1(A_46), k10_relat_1(k6_relat_1(A_46), A_220))=k3_xboole_0(A_220, k9_relat_1(k6_relat_1(A_46), A_46)) | ~v1_funct_1(k6_relat_1(A_46)) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2239])).
% 8.31/3.15  tff(c_2255, plain, (![A_46, A_220]: (k9_relat_1(k6_relat_1(A_46), k10_relat_1(k6_relat_1(A_46), A_220))=k3_xboole_0(A_220, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_1500, c_2251])).
% 8.31/3.15  tff(c_12589, plain, (![B_468, B_469]: (k9_relat_1(k6_relat_1(B_468), B_468)=k3_xboole_0(k2_xboole_0(B_468, B_469), B_468))), inference(superposition, [status(thm), theory('equality')], [c_12502, c_2255])).
% 8.31/3.15  tff(c_12713, plain, (![B_470, B_471]: (k3_xboole_0(k2_xboole_0(B_470, B_471), B_470)=B_470)), inference(demodulation, [status(thm), theory('equality')], [c_1500, c_12589])).
% 8.31/3.15  tff(c_12787, plain, (k3_xboole_0('#skF_5', k10_relat_1('#skF_4', '#skF_6'))=k10_relat_1('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_104, c_12713])).
% 8.31/3.15  tff(c_62, plain, (![A_60, C_62, B_61]: (k3_xboole_0(A_60, k10_relat_1(C_62, B_61))=k10_relat_1(k7_relat_1(C_62, A_60), B_61) | ~v1_relat_1(C_62))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.31/3.15  tff(c_13746, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12787, c_62])).
% 8.31/3.15  tff(c_13753, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_13746])).
% 8.31/3.15  tff(c_13755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_13753])).
% 8.31/3.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/3.15  
% 8.31/3.15  Inference rules
% 8.31/3.15  ----------------------
% 8.31/3.15  #Ref     : 0
% 8.31/3.15  #Sup     : 3339
% 8.31/3.15  #Fact    : 0
% 8.31/3.15  #Define  : 0
% 8.31/3.15  #Split   : 2
% 8.31/3.15  #Chain   : 0
% 8.31/3.15  #Close   : 0
% 8.31/3.15  
% 8.31/3.15  Ordering : KBO
% 8.31/3.15  
% 8.31/3.15  Simplification rules
% 8.31/3.15  ----------------------
% 8.31/3.15  #Subsume      : 226
% 8.31/3.15  #Demod        : 2224
% 8.31/3.15  #Tautology    : 1313
% 8.31/3.15  #SimpNegUnit  : 1
% 8.31/3.15  #BackRed      : 21
% 8.31/3.15  
% 8.31/3.15  #Partial instantiations: 0
% 8.31/3.15  #Strategies tried      : 1
% 8.31/3.15  
% 8.31/3.15  Timing (in seconds)
% 8.31/3.15  ----------------------
% 8.31/3.16  Preprocessing        : 0.37
% 8.31/3.16  Parsing              : 0.20
% 8.31/3.16  CNF conversion       : 0.03
% 8.31/3.16  Main loop            : 1.97
% 8.31/3.16  Inferencing          : 0.53
% 8.31/3.16  Reduction            : 0.83
% 8.31/3.16  Demodulation         : 0.68
% 8.31/3.16  BG Simplification    : 0.07
% 8.31/3.16  Subsumption          : 0.42
% 8.31/3.16  Abstraction          : 0.09
% 8.31/3.16  MUC search           : 0.00
% 8.31/3.16  Cooper               : 0.00
% 8.31/3.16  Total                : 2.38
% 8.31/3.16  Index Insertion      : 0.00
% 8.31/3.16  Index Deletion       : 0.00
% 8.31/3.16  Index Matching       : 0.00
% 8.31/3.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
