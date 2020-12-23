%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:28 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 480 expanded)
%              Number of leaves         :   33 ( 190 expanded)
%              Depth                    :   15
%              Number of atoms          :  119 ( 754 expanded)
%              Number of equality atoms :   48 ( 344 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_42,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_20] : v1_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_227,plain,(
    ! [B_62,A_63] : k5_relat_1(k6_relat_1(B_62),k6_relat_1(A_63)) = k6_relat_1(k3_xboole_0(A_63,B_62)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = k7_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_233,plain,(
    ! [A_63,B_62] :
      ( k7_relat_1(k6_relat_1(A_63),B_62) = k6_relat_1(k3_xboole_0(A_63,B_62))
      | ~ v1_relat_1(k6_relat_1(A_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_26])).

tff(c_243,plain,(
    ! [A_63,B_62] : k7_relat_1(k6_relat_1(A_63),B_62) = k6_relat_1(k3_xboole_0(A_63,B_62)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_233])).

tff(c_24,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_247,plain,(
    ! [A_64,B_65] : k7_relat_1(k6_relat_1(A_64),B_65) = k6_relat_1(k3_xboole_0(A_64,B_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_233])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_253,plain,(
    ! [A_64,B_65] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_64,B_65))) = k9_relat_1(k6_relat_1(A_64),B_65)
      | ~ v1_relat_1(k6_relat_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_16])).

tff(c_259,plain,(
    ! [A_64,B_65] : k9_relat_1(k6_relat_1(A_64),B_65) = k3_xboole_0(A_64,B_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_253])).

tff(c_785,plain,(
    ! [A_102,B_103] :
      ( k3_xboole_0(A_102,k9_relat_1(B_103,k1_relat_1(B_103))) = k9_relat_1(B_103,k10_relat_1(B_103,A_102))
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_831,plain,(
    ! [A_17,A_102] :
      ( k9_relat_1(k6_relat_1(A_17),k10_relat_1(k6_relat_1(A_17),A_102)) = k3_xboole_0(A_102,k9_relat_1(k6_relat_1(A_17),A_17))
      | ~ v1_funct_1(k6_relat_1(A_17))
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_785])).

tff(c_1922,plain,(
    ! [A_156,A_157] : k3_xboole_0(A_156,k10_relat_1(k6_relat_1(A_156),A_157)) = k3_xboole_0(A_157,A_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2,c_259,c_259,c_831])).

tff(c_32,plain,(
    ! [A_21,C_23,B_22] :
      ( k3_xboole_0(A_21,k10_relat_1(C_23,B_22)) = k10_relat_1(k7_relat_1(C_23,A_21),B_22)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2000,plain,(
    ! [A_156,A_157] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_156),A_156),A_157) = k3_xboole_0(A_157,A_156)
      | ~ v1_relat_1(k6_relat_1(A_156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1922,c_32])).

tff(c_2131,plain,(
    ! [A_160,A_161] : k10_relat_1(k6_relat_1(A_160),A_161) = k3_xboole_0(A_161,A_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2,c_243,c_2000])).

tff(c_98,plain,(
    ! [A_45] :
      ( k10_relat_1(A_45,k2_relat_1(A_45)) = k1_relat_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [A_17] :
      ( k10_relat_1(k6_relat_1(A_17),A_17) = k1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_98])).

tff(c_111,plain,(
    ! [A_17] : k10_relat_1(k6_relat_1(A_17),A_17) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_107])).

tff(c_447,plain,(
    ! [A_84,C_85,B_86] :
      ( k3_xboole_0(A_84,k10_relat_1(C_85,B_86)) = k10_relat_1(k7_relat_1(C_85,A_84),B_86)
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_468,plain,(
    ! [A_17,A_84] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_17),A_84),A_17) = k3_xboole_0(A_84,A_17)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_447])).

tff(c_483,plain,(
    ! [A_17,A_84] : k10_relat_1(k6_relat_1(k3_xboole_0(A_17,A_84)),A_17) = k3_xboole_0(A_84,A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_243,c_468])).

tff(c_2144,plain,(
    ! [A_161,A_84] : k3_xboole_0(A_161,k3_xboole_0(A_161,A_84)) = k3_xboole_0(A_84,A_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_2131,c_483])).

tff(c_558,plain,(
    ! [A_92,A_93] : k10_relat_1(k6_relat_1(k3_xboole_0(A_92,A_93)),A_92) = k3_xboole_0(A_93,A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_243,c_468])).

tff(c_121,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(k10_relat_1(B_47,A_48),k1_relat_1(B_47))
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_130,plain,(
    ! [A_17,A_48] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_17),A_48),A_17)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_121])).

tff(c_135,plain,(
    ! [A_17,A_48] : r1_tarski(k10_relat_1(k6_relat_1(A_17),A_48),A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_130])).

tff(c_596,plain,(
    ! [A_93,A_92] : r1_tarski(k3_xboole_0(A_93,A_92),k3_xboole_0(A_92,A_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_135])).

tff(c_650,plain,(
    ! [A_96,A_97] : r1_tarski(k3_xboole_0(A_96,A_97),k3_xboole_0(A_97,A_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_135])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_654,plain,(
    ! [A_97,A_96] :
      ( k3_xboole_0(A_97,A_96) = k3_xboole_0(A_96,A_97)
      | ~ r1_tarski(k3_xboole_0(A_97,A_96),k3_xboole_0(A_96,A_97)) ) ),
    inference(resolution,[status(thm)],[c_650,c_4])).

tff(c_670,plain,(
    ! [A_97,A_96] : k3_xboole_0(A_97,A_96) = k3_xboole_0(A_96,A_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_654])).

tff(c_2034,plain,(
    ! [A_156,A_157] : k10_relat_1(k6_relat_1(A_156),A_157) = k3_xboole_0(A_157,A_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2,c_243,c_2000])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_972,plain,(
    ! [A_110,C_111,B_112] :
      ( r1_tarski(A_110,k10_relat_1(C_111,B_112))
      | ~ r1_tarski(k9_relat_1(C_111,A_110),B_112)
      | ~ r1_tarski(A_110,k1_relat_1(C_111))
      | ~ v1_funct_1(C_111)
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3517,plain,(
    ! [A_194,C_195] :
      ( r1_tarski(A_194,k10_relat_1(C_195,k9_relat_1(C_195,A_194)))
      | ~ r1_tarski(A_194,k1_relat_1(C_195))
      | ~ v1_funct_1(C_195)
      | ~ v1_relat_1(C_195) ) ),
    inference(resolution,[status(thm)],[c_8,c_972])).

tff(c_3536,plain,(
    ! [A_194,A_156] :
      ( r1_tarski(A_194,k3_xboole_0(k9_relat_1(k6_relat_1(A_156),A_194),A_156))
      | ~ r1_tarski(A_194,k1_relat_1(k6_relat_1(A_156)))
      | ~ v1_funct_1(k6_relat_1(A_156))
      | ~ v1_relat_1(k6_relat_1(A_156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2034,c_3517])).

tff(c_3551,plain,(
    ! [A_196,A_197] :
      ( r1_tarski(A_196,k3_xboole_0(A_196,A_197))
      | ~ r1_tarski(A_196,A_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_22,c_2144,c_670,c_259,c_3536])).

tff(c_149,plain,(
    ! [A_51,A_52] : r1_tarski(k10_relat_1(k6_relat_1(A_51),A_52),A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_130])).

tff(c_159,plain,(
    ! [A_51,A_52] :
      ( k10_relat_1(k6_relat_1(A_51),A_52) = A_51
      | ~ r1_tarski(A_51,k10_relat_1(k6_relat_1(A_51),A_52)) ) ),
    inference(resolution,[status(thm)],[c_149,c_4])).

tff(c_2942,plain,(
    ! [A_173,A_174] :
      ( k3_xboole_0(A_173,A_174) = A_174
      | ~ r1_tarski(A_174,k3_xboole_0(A_173,A_174)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2034,c_2034,c_159])).

tff(c_2963,plain,(
    ! [A_97,A_96] :
      ( k3_xboole_0(A_97,A_96) = A_96
      | ~ r1_tarski(A_96,k3_xboole_0(A_96,A_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_2942])).

tff(c_3622,plain,(
    ! [A_198,A_199] :
      ( k3_xboole_0(A_198,A_199) = A_199
      | ~ r1_tarski(A_199,A_198) ) ),
    inference(resolution,[status(thm)],[c_3551,c_2963])).

tff(c_3720,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_3622])).

tff(c_3905,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3720,c_32])).

tff(c_3937,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3905])).

tff(c_3939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3937])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:23:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.87  
% 4.62/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.87  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.62/1.87  
% 4.62/1.87  %Foreground sorts:
% 4.62/1.87  
% 4.62/1.87  
% 4.62/1.87  %Background operators:
% 4.62/1.87  
% 4.62/1.87  
% 4.62/1.87  %Foreground operators:
% 4.62/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.62/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.87  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.62/1.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.62/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.62/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.62/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.62/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.62/1.87  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.62/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.62/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.62/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.87  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.62/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.62/1.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.62/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.62/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.62/1.87  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.62/1.87  
% 4.62/1.89  tff(f_105, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 4.62/1.89  tff(f_67, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.62/1.89  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.62/1.89  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.62/1.89  tff(f_95, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 4.62/1.89  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 4.62/1.89  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.62/1.89  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 4.62/1.89  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 4.62/1.89  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.62/1.89  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 4.62/1.89  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.62/1.89  tff(f_93, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.62/1.89  tff(c_42, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.62/1.89  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.62/1.89  tff(c_44, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.62/1.89  tff(c_28, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.62/1.89  tff(c_30, plain, (![A_20]: (v1_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.62/1.89  tff(c_22, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.62/1.89  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.62/1.89  tff(c_227, plain, (![B_62, A_63]: (k5_relat_1(k6_relat_1(B_62), k6_relat_1(A_63))=k6_relat_1(k3_xboole_0(A_63, B_62)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.62/1.89  tff(c_26, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=k7_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.62/1.89  tff(c_233, plain, (![A_63, B_62]: (k7_relat_1(k6_relat_1(A_63), B_62)=k6_relat_1(k3_xboole_0(A_63, B_62)) | ~v1_relat_1(k6_relat_1(A_63)))), inference(superposition, [status(thm), theory('equality')], [c_227, c_26])).
% 4.62/1.89  tff(c_243, plain, (![A_63, B_62]: (k7_relat_1(k6_relat_1(A_63), B_62)=k6_relat_1(k3_xboole_0(A_63, B_62)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_233])).
% 4.62/1.89  tff(c_24, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.62/1.89  tff(c_247, plain, (![A_64, B_65]: (k7_relat_1(k6_relat_1(A_64), B_65)=k6_relat_1(k3_xboole_0(A_64, B_65)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_233])).
% 4.62/1.89  tff(c_16, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.62/1.89  tff(c_253, plain, (![A_64, B_65]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_64, B_65)))=k9_relat_1(k6_relat_1(A_64), B_65) | ~v1_relat_1(k6_relat_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_247, c_16])).
% 4.62/1.89  tff(c_259, plain, (![A_64, B_65]: (k9_relat_1(k6_relat_1(A_64), B_65)=k3_xboole_0(A_64, B_65))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_253])).
% 4.62/1.89  tff(c_785, plain, (![A_102, B_103]: (k3_xboole_0(A_102, k9_relat_1(B_103, k1_relat_1(B_103)))=k9_relat_1(B_103, k10_relat_1(B_103, A_102)) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.62/1.89  tff(c_831, plain, (![A_17, A_102]: (k9_relat_1(k6_relat_1(A_17), k10_relat_1(k6_relat_1(A_17), A_102))=k3_xboole_0(A_102, k9_relat_1(k6_relat_1(A_17), A_17)) | ~v1_funct_1(k6_relat_1(A_17)) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_785])).
% 4.62/1.89  tff(c_1922, plain, (![A_156, A_157]: (k3_xboole_0(A_156, k10_relat_1(k6_relat_1(A_156), A_157))=k3_xboole_0(A_157, A_156))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2, c_259, c_259, c_831])).
% 4.62/1.89  tff(c_32, plain, (![A_21, C_23, B_22]: (k3_xboole_0(A_21, k10_relat_1(C_23, B_22))=k10_relat_1(k7_relat_1(C_23, A_21), B_22) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.62/1.89  tff(c_2000, plain, (![A_156, A_157]: (k10_relat_1(k7_relat_1(k6_relat_1(A_156), A_156), A_157)=k3_xboole_0(A_157, A_156) | ~v1_relat_1(k6_relat_1(A_156)))), inference(superposition, [status(thm), theory('equality')], [c_1922, c_32])).
% 4.62/1.89  tff(c_2131, plain, (![A_160, A_161]: (k10_relat_1(k6_relat_1(A_160), A_161)=k3_xboole_0(A_161, A_160))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2, c_243, c_2000])).
% 4.62/1.89  tff(c_98, plain, (![A_45]: (k10_relat_1(A_45, k2_relat_1(A_45))=k1_relat_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.62/1.89  tff(c_107, plain, (![A_17]: (k10_relat_1(k6_relat_1(A_17), A_17)=k1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_98])).
% 4.62/1.89  tff(c_111, plain, (![A_17]: (k10_relat_1(k6_relat_1(A_17), A_17)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_107])).
% 4.62/1.89  tff(c_447, plain, (![A_84, C_85, B_86]: (k3_xboole_0(A_84, k10_relat_1(C_85, B_86))=k10_relat_1(k7_relat_1(C_85, A_84), B_86) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.62/1.89  tff(c_468, plain, (![A_17, A_84]: (k10_relat_1(k7_relat_1(k6_relat_1(A_17), A_84), A_17)=k3_xboole_0(A_84, A_17) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_111, c_447])).
% 4.62/1.89  tff(c_483, plain, (![A_17, A_84]: (k10_relat_1(k6_relat_1(k3_xboole_0(A_17, A_84)), A_17)=k3_xboole_0(A_84, A_17))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_243, c_468])).
% 4.62/1.89  tff(c_2144, plain, (![A_161, A_84]: (k3_xboole_0(A_161, k3_xboole_0(A_161, A_84))=k3_xboole_0(A_84, A_161))), inference(superposition, [status(thm), theory('equality')], [c_2131, c_483])).
% 4.62/1.89  tff(c_558, plain, (![A_92, A_93]: (k10_relat_1(k6_relat_1(k3_xboole_0(A_92, A_93)), A_92)=k3_xboole_0(A_93, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_243, c_468])).
% 4.62/1.89  tff(c_121, plain, (![B_47, A_48]: (r1_tarski(k10_relat_1(B_47, A_48), k1_relat_1(B_47)) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.62/1.89  tff(c_130, plain, (![A_17, A_48]: (r1_tarski(k10_relat_1(k6_relat_1(A_17), A_48), A_17) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_121])).
% 4.62/1.89  tff(c_135, plain, (![A_17, A_48]: (r1_tarski(k10_relat_1(k6_relat_1(A_17), A_48), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_130])).
% 4.62/1.89  tff(c_596, plain, (![A_93, A_92]: (r1_tarski(k3_xboole_0(A_93, A_92), k3_xboole_0(A_92, A_93)))), inference(superposition, [status(thm), theory('equality')], [c_558, c_135])).
% 4.62/1.89  tff(c_650, plain, (![A_96, A_97]: (r1_tarski(k3_xboole_0(A_96, A_97), k3_xboole_0(A_97, A_96)))), inference(superposition, [status(thm), theory('equality')], [c_558, c_135])).
% 4.62/1.89  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.62/1.89  tff(c_654, plain, (![A_97, A_96]: (k3_xboole_0(A_97, A_96)=k3_xboole_0(A_96, A_97) | ~r1_tarski(k3_xboole_0(A_97, A_96), k3_xboole_0(A_96, A_97)))), inference(resolution, [status(thm)], [c_650, c_4])).
% 4.62/1.89  tff(c_670, plain, (![A_97, A_96]: (k3_xboole_0(A_97, A_96)=k3_xboole_0(A_96, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_596, c_654])).
% 4.62/1.89  tff(c_2034, plain, (![A_156, A_157]: (k10_relat_1(k6_relat_1(A_156), A_157)=k3_xboole_0(A_157, A_156))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2, c_243, c_2000])).
% 4.62/1.89  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.62/1.89  tff(c_972, plain, (![A_110, C_111, B_112]: (r1_tarski(A_110, k10_relat_1(C_111, B_112)) | ~r1_tarski(k9_relat_1(C_111, A_110), B_112) | ~r1_tarski(A_110, k1_relat_1(C_111)) | ~v1_funct_1(C_111) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.62/1.89  tff(c_3517, plain, (![A_194, C_195]: (r1_tarski(A_194, k10_relat_1(C_195, k9_relat_1(C_195, A_194))) | ~r1_tarski(A_194, k1_relat_1(C_195)) | ~v1_funct_1(C_195) | ~v1_relat_1(C_195))), inference(resolution, [status(thm)], [c_8, c_972])).
% 4.62/1.89  tff(c_3536, plain, (![A_194, A_156]: (r1_tarski(A_194, k3_xboole_0(k9_relat_1(k6_relat_1(A_156), A_194), A_156)) | ~r1_tarski(A_194, k1_relat_1(k6_relat_1(A_156))) | ~v1_funct_1(k6_relat_1(A_156)) | ~v1_relat_1(k6_relat_1(A_156)))), inference(superposition, [status(thm), theory('equality')], [c_2034, c_3517])).
% 4.62/1.89  tff(c_3551, plain, (![A_196, A_197]: (r1_tarski(A_196, k3_xboole_0(A_196, A_197)) | ~r1_tarski(A_196, A_197))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_22, c_2144, c_670, c_259, c_3536])).
% 4.62/1.89  tff(c_149, plain, (![A_51, A_52]: (r1_tarski(k10_relat_1(k6_relat_1(A_51), A_52), A_51))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_130])).
% 4.62/1.89  tff(c_159, plain, (![A_51, A_52]: (k10_relat_1(k6_relat_1(A_51), A_52)=A_51 | ~r1_tarski(A_51, k10_relat_1(k6_relat_1(A_51), A_52)))), inference(resolution, [status(thm)], [c_149, c_4])).
% 4.62/1.89  tff(c_2942, plain, (![A_173, A_174]: (k3_xboole_0(A_173, A_174)=A_174 | ~r1_tarski(A_174, k3_xboole_0(A_173, A_174)))), inference(demodulation, [status(thm), theory('equality')], [c_2034, c_2034, c_159])).
% 4.62/1.89  tff(c_2963, plain, (![A_97, A_96]: (k3_xboole_0(A_97, A_96)=A_96 | ~r1_tarski(A_96, k3_xboole_0(A_96, A_97)))), inference(superposition, [status(thm), theory('equality')], [c_670, c_2942])).
% 4.62/1.89  tff(c_3622, plain, (![A_198, A_199]: (k3_xboole_0(A_198, A_199)=A_199 | ~r1_tarski(A_199, A_198))), inference(resolution, [status(thm)], [c_3551, c_2963])).
% 4.62/1.89  tff(c_3720, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_3622])).
% 4.62/1.89  tff(c_3905, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3720, c_32])).
% 4.62/1.89  tff(c_3937, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3905])).
% 4.62/1.89  tff(c_3939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_3937])).
% 4.62/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.89  
% 4.62/1.89  Inference rules
% 4.62/1.89  ----------------------
% 4.62/1.89  #Ref     : 0
% 4.62/1.89  #Sup     : 896
% 4.62/1.89  #Fact    : 0
% 4.62/1.89  #Define  : 0
% 4.62/1.89  #Split   : 1
% 4.62/1.89  #Chain   : 0
% 4.62/1.89  #Close   : 0
% 4.62/1.89  
% 4.62/1.89  Ordering : KBO
% 4.62/1.89  
% 4.62/1.89  Simplification rules
% 4.62/1.89  ----------------------
% 4.62/1.89  #Subsume      : 42
% 4.62/1.89  #Demod        : 771
% 4.62/1.89  #Tautology    : 455
% 4.62/1.89  #SimpNegUnit  : 2
% 4.62/1.89  #BackRed      : 17
% 4.62/1.89  
% 4.62/1.89  #Partial instantiations: 0
% 4.62/1.89  #Strategies tried      : 1
% 4.62/1.89  
% 4.62/1.89  Timing (in seconds)
% 4.62/1.89  ----------------------
% 4.62/1.89  Preprocessing        : 0.33
% 4.62/1.89  Parsing              : 0.18
% 4.62/1.89  CNF conversion       : 0.02
% 4.62/1.89  Main loop            : 0.79
% 4.62/1.89  Inferencing          : 0.23
% 4.62/1.89  Reduction            : 0.34
% 4.62/1.89  Demodulation         : 0.26
% 4.62/1.89  BG Simplification    : 0.03
% 4.62/1.89  Subsumption          : 0.14
% 4.62/1.89  Abstraction          : 0.05
% 4.62/1.89  MUC search           : 0.00
% 4.62/1.89  Cooper               : 0.00
% 4.62/1.89  Total                : 1.15
% 4.62/1.89  Index Insertion      : 0.00
% 4.62/1.90  Index Deletion       : 0.00
% 4.62/1.90  Index Matching       : 0.00
% 4.62/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
