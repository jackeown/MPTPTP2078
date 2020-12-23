%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:26 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 231 expanded)
%              Number of leaves         :   33 (  97 expanded)
%              Depth                    :   20
%              Number of atoms          :  183 ( 460 expanded)
%              Number of equality atoms :   49 ( 111 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_48,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(k2_relat_1(B),k1_relat_1(C))
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(k5_relat_1(B,C),k9_relat_1(C,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    ! [A_19] : v1_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [A_10] : k4_relat_1(k6_relat_1(A_10)) = k6_relat_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_195,plain,(
    ! [A_47] :
      ( k4_relat_1(A_47) = k2_funct_1(A_47)
      | ~ v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_198,plain,(
    ! [A_20] :
      ( k4_relat_1(k6_relat_1(A_20)) = k2_funct_1(k6_relat_1(A_20))
      | ~ v1_funct_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_34,c_195])).

tff(c_204,plain,(
    ! [A_20] : k2_funct_1(k6_relat_1(A_20)) = k6_relat_1(A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_16,c_198])).

tff(c_558,plain,(
    ! [B_69,A_70] :
      ( k10_relat_1(k2_funct_1(B_69),A_70) = k9_relat_1(B_69,A_70)
      | ~ v2_funct_1(B_69)
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_571,plain,(
    ! [A_20,A_70] :
      ( k9_relat_1(k6_relat_1(A_20),A_70) = k10_relat_1(k6_relat_1(A_20),A_70)
      | ~ v2_funct_1(k6_relat_1(A_20))
      | ~ v1_funct_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_558])).

tff(c_575,plain,(
    ! [A_20,A_70] : k9_relat_1(k6_relat_1(A_20),A_70) = k10_relat_1(k6_relat_1(A_20),A_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_34,c_571])).

tff(c_14,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_208,plain,(
    ! [B_48,A_49] :
      ( k5_relat_1(B_48,k6_relat_1(A_49)) = B_48
      | ~ r1_tarski(k2_relat_1(B_48),A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_214,plain,(
    ! [A_9,A_49] :
      ( k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_49)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_49)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_208])).

tff(c_275,plain,(
    ! [A_54,A_55] :
      ( k5_relat_1(k6_relat_1(A_54),k6_relat_1(A_55)) = k6_relat_1(A_54)
      | ~ r1_tarski(A_54,A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_214])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_relat_1(A_16),B_17) = k7_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_285,plain,(
    ! [A_55,A_54] :
      ( k7_relat_1(k6_relat_1(A_55),A_54) = k6_relat_1(A_54)
      | ~ v1_relat_1(k6_relat_1(A_55))
      | ~ r1_tarski(A_54,A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_24])).

tff(c_334,plain,(
    ! [A_56,A_57] :
      ( k7_relat_1(k6_relat_1(A_56),A_57) = k6_relat_1(A_57)
      | ~ r1_tarski(A_57,A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_285])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_344,plain,(
    ! [A_56,A_57] :
      ( k9_relat_1(k6_relat_1(A_56),A_57) = k2_relat_1(k6_relat_1(A_57))
      | ~ v1_relat_1(k6_relat_1(A_56))
      | ~ r1_tarski(A_57,A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_8])).

tff(c_363,plain,(
    ! [A_56,A_57] :
      ( k9_relat_1(k6_relat_1(A_56),A_57) = A_57
      | ~ r1_tarski(A_57,A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14,c_344])).

tff(c_577,plain,(
    ! [A_56,A_57] :
      ( k10_relat_1(k6_relat_1(A_56),A_57) = A_57
      | ~ r1_tarski(A_57,A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_363])).

tff(c_317,plain,(
    ! [A_55,A_54] :
      ( k7_relat_1(k6_relat_1(A_55),A_54) = k6_relat_1(A_54)
      | ~ r1_tarski(A_54,A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_285])).

tff(c_673,plain,(
    ! [B_78,C_79,A_80] :
      ( k10_relat_1(k5_relat_1(B_78,C_79),A_80) = k10_relat_1(B_78,k10_relat_1(C_79,A_80))
      | ~ v1_relat_1(C_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_695,plain,(
    ! [A_16,B_17,A_80] :
      ( k10_relat_1(k6_relat_1(A_16),k10_relat_1(B_17,A_80)) = k10_relat_1(k7_relat_1(B_17,A_16),A_80)
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_673])).

tff(c_1053,plain,(
    ! [A_100,B_101,A_102] :
      ( k10_relat_1(k6_relat_1(A_100),k10_relat_1(B_101,A_102)) = k10_relat_1(k7_relat_1(B_101,A_100),A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_695])).

tff(c_12,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_95,plain,(
    ! [A_38] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_38)),A_38) = A_38
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_104,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_9)) = k6_relat_1(A_9)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_95])).

tff(c_108,plain,(
    ! [A_9] : k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_9)) = k6_relat_1(A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_104])).

tff(c_698,plain,(
    ! [A_9,A_80] :
      ( k10_relat_1(k6_relat_1(A_9),k10_relat_1(k6_relat_1(A_9),A_80)) = k10_relat_1(k6_relat_1(A_9),A_80)
      | ~ v1_relat_1(k6_relat_1(A_9))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_673])).

tff(c_713,plain,(
    ! [A_9,A_80] : k10_relat_1(k6_relat_1(A_9),k10_relat_1(k6_relat_1(A_9),A_80)) = k10_relat_1(k6_relat_1(A_9),A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_698])).

tff(c_578,plain,(
    ! [A_71,A_72] : k9_relat_1(k6_relat_1(A_71),A_72) = k10_relat_1(k6_relat_1(A_71),A_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_34,c_571])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k10_relat_1(B_22,k9_relat_1(B_22,A_21)),A_21)
      | ~ v2_funct_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_584,plain,(
    ! [A_71,A_72] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_71),k10_relat_1(k6_relat_1(A_71),A_72)),A_72)
      | ~ v2_funct_1(k6_relat_1(A_71))
      | ~ v1_funct_1(k6_relat_1(A_71))
      | ~ v1_relat_1(k6_relat_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_36])).

tff(c_597,plain,(
    ! [A_71,A_72] : r1_tarski(k10_relat_1(k6_relat_1(A_71),k10_relat_1(k6_relat_1(A_71),A_72)),A_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_34,c_584])).

tff(c_937,plain,(
    ! [A_71,A_72] : r1_tarski(k10_relat_1(k6_relat_1(A_71),A_72),A_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_597])).

tff(c_1202,plain,(
    ! [B_105,A_106,A_107] :
      ( r1_tarski(k10_relat_1(k7_relat_1(B_105,A_106),A_107),k10_relat_1(B_105,A_107))
      | ~ v1_relat_1(B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_937])).

tff(c_1242,plain,(
    ! [A_54,A_107,A_55] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_54),A_107),k10_relat_1(k6_relat_1(A_55),A_107))
      | ~ v1_relat_1(k6_relat_1(A_55))
      | ~ r1_tarski(A_54,A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_1202])).

tff(c_1940,plain,(
    ! [A_129,A_130,A_131] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_129),A_130),k10_relat_1(k6_relat_1(A_131),A_130))
      | ~ r1_tarski(A_129,A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1242])).

tff(c_2532,plain,(
    ! [A_146,A_147,A_148] :
      ( r1_tarski(A_146,k10_relat_1(k6_relat_1(A_147),A_146))
      | ~ r1_tarski(A_148,A_147)
      | ~ r1_tarski(A_146,A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_1940])).

tff(c_2584,plain,(
    ! [A_149] :
      ( r1_tarski(A_149,k10_relat_1(k6_relat_1(k1_relat_1('#skF_2')),A_149))
      | ~ r1_tarski(A_149,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_2532])).

tff(c_1005,plain,(
    ! [A_96,A_97] : r1_tarski(k10_relat_1(k6_relat_1(A_96),A_97),A_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_597])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1026,plain,(
    ! [A_96,A_97] :
      ( k10_relat_1(k6_relat_1(A_96),A_97) = A_97
      | ~ r1_tarski(A_97,k10_relat_1(k6_relat_1(A_96),A_97)) ) ),
    inference(resolution,[status(thm)],[c_1005,c_2])).

tff(c_2709,plain,(
    ! [A_152] :
      ( k10_relat_1(k6_relat_1(k1_relat_1('#skF_2')),A_152) = A_152
      | ~ r1_tarski(A_152,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2584,c_1026])).

tff(c_20,plain,(
    ! [A_13] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_13)),A_13) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_753,plain,(
    ! [B_85,A_86,C_87] :
      ( r1_tarski(k10_relat_1(B_85,A_86),k10_relat_1(k5_relat_1(B_85,C_87),k9_relat_1(C_87,A_86)))
      | ~ r1_tarski(k2_relat_1(B_85),k1_relat_1(C_87))
      | ~ v1_relat_1(C_87)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_798,plain,(
    ! [A_13,A_86] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_13)),A_86),k10_relat_1(A_13,k9_relat_1(A_13,A_86)))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(A_13))),k1_relat_1(A_13))
      | ~ v1_relat_1(A_13)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(A_13)))
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_753])).

tff(c_821,plain,(
    ! [A_13,A_86] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_13)),A_86),k10_relat_1(A_13,k9_relat_1(A_13,A_86)))
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6,c_14,c_798])).

tff(c_2761,plain,(
    ! [A_152] :
      ( r1_tarski(A_152,k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_152)))
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_152,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2709,c_821])).

tff(c_2905,plain,(
    ! [A_153] :
      ( r1_tarski(A_153,k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_153)))
      | ~ r1_tarski(A_153,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2761])).

tff(c_460,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(k10_relat_1(B_62,k9_relat_1(B_62,A_63)),A_63)
      | ~ v2_funct_1(B_62)
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_469,plain,(
    ! [B_62,A_63] :
      ( k10_relat_1(B_62,k9_relat_1(B_62,A_63)) = A_63
      | ~ r1_tarski(A_63,k10_relat_1(B_62,k9_relat_1(B_62,A_63)))
      | ~ v2_funct_1(B_62)
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_460,c_2])).

tff(c_2908,plain,(
    ! [A_153] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_153)) = A_153
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_153,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2905,c_469])).

tff(c_2967,plain,(
    ! [A_155] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_155)) = A_155
      | ~ r1_tarski(A_155,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_2908])).

tff(c_42,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3012,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2967,c_42])).

tff(c_3047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3012])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:06:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.74  
% 3.93/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.75  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.93/1.75  
% 3.93/1.75  %Foreground sorts:
% 3.93/1.75  
% 3.93/1.75  
% 3.93/1.75  %Background operators:
% 3.93/1.75  
% 3.93/1.75  
% 3.93/1.75  %Foreground operators:
% 3.93/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.93/1.75  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.93/1.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.93/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.93/1.75  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.93/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.93/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.93/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.93/1.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.93/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.93/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.75  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.93/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.93/1.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.93/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.93/1.75  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.93/1.75  
% 4.29/1.78  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.29/1.78  tff(f_120, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 4.29/1.78  tff(f_84, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.29/1.78  tff(f_80, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.29/1.78  tff(f_48, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 4.29/1.78  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 4.29/1.78  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 4.29/1.78  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.29/1.78  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 4.29/1.78  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 4.29/1.78  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.29/1.78  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 4.29/1.78  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 4.29/1.78  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 4.29/1.78  tff(f_109, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(C)) => r1_tarski(k10_relat_1(B, A), k10_relat_1(k5_relat_1(B, C), k9_relat_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_funct_1)).
% 4.29/1.78  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.29/1.78  tff(c_50, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.29/1.78  tff(c_48, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.29/1.78  tff(c_44, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.29/1.78  tff(c_46, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.29/1.78  tff(c_32, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.29/1.78  tff(c_30, plain, (![A_19]: (v1_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.29/1.78  tff(c_34, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.29/1.78  tff(c_16, plain, (![A_10]: (k4_relat_1(k6_relat_1(A_10))=k6_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.29/1.78  tff(c_195, plain, (![A_47]: (k4_relat_1(A_47)=k2_funct_1(A_47) | ~v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.29/1.78  tff(c_198, plain, (![A_20]: (k4_relat_1(k6_relat_1(A_20))=k2_funct_1(k6_relat_1(A_20)) | ~v1_funct_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_20)))), inference(resolution, [status(thm)], [c_34, c_195])).
% 4.29/1.78  tff(c_204, plain, (![A_20]: (k2_funct_1(k6_relat_1(A_20))=k6_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_16, c_198])).
% 4.29/1.78  tff(c_558, plain, (![B_69, A_70]: (k10_relat_1(k2_funct_1(B_69), A_70)=k9_relat_1(B_69, A_70) | ~v2_funct_1(B_69) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.29/1.78  tff(c_571, plain, (![A_20, A_70]: (k9_relat_1(k6_relat_1(A_20), A_70)=k10_relat_1(k6_relat_1(A_20), A_70) | ~v2_funct_1(k6_relat_1(A_20)) | ~v1_funct_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_204, c_558])).
% 4.29/1.78  tff(c_575, plain, (![A_20, A_70]: (k9_relat_1(k6_relat_1(A_20), A_70)=k10_relat_1(k6_relat_1(A_20), A_70))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_34, c_571])).
% 4.29/1.78  tff(c_14, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.29/1.78  tff(c_208, plain, (![B_48, A_49]: (k5_relat_1(B_48, k6_relat_1(A_49))=B_48 | ~r1_tarski(k2_relat_1(B_48), A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.29/1.78  tff(c_214, plain, (![A_9, A_49]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_49))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_49) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_208])).
% 4.29/1.78  tff(c_275, plain, (![A_54, A_55]: (k5_relat_1(k6_relat_1(A_54), k6_relat_1(A_55))=k6_relat_1(A_54) | ~r1_tarski(A_54, A_55))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_214])).
% 4.29/1.78  tff(c_24, plain, (![A_16, B_17]: (k5_relat_1(k6_relat_1(A_16), B_17)=k7_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.29/1.78  tff(c_285, plain, (![A_55, A_54]: (k7_relat_1(k6_relat_1(A_55), A_54)=k6_relat_1(A_54) | ~v1_relat_1(k6_relat_1(A_55)) | ~r1_tarski(A_54, A_55))), inference(superposition, [status(thm), theory('equality')], [c_275, c_24])).
% 4.29/1.78  tff(c_334, plain, (![A_56, A_57]: (k7_relat_1(k6_relat_1(A_56), A_57)=k6_relat_1(A_57) | ~r1_tarski(A_57, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_285])).
% 4.29/1.78  tff(c_8, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.29/1.78  tff(c_344, plain, (![A_56, A_57]: (k9_relat_1(k6_relat_1(A_56), A_57)=k2_relat_1(k6_relat_1(A_57)) | ~v1_relat_1(k6_relat_1(A_56)) | ~r1_tarski(A_57, A_56))), inference(superposition, [status(thm), theory('equality')], [c_334, c_8])).
% 4.29/1.78  tff(c_363, plain, (![A_56, A_57]: (k9_relat_1(k6_relat_1(A_56), A_57)=A_57 | ~r1_tarski(A_57, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14, c_344])).
% 4.29/1.78  tff(c_577, plain, (![A_56, A_57]: (k10_relat_1(k6_relat_1(A_56), A_57)=A_57 | ~r1_tarski(A_57, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_575, c_363])).
% 4.29/1.78  tff(c_317, plain, (![A_55, A_54]: (k7_relat_1(k6_relat_1(A_55), A_54)=k6_relat_1(A_54) | ~r1_tarski(A_54, A_55))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_285])).
% 4.29/1.78  tff(c_673, plain, (![B_78, C_79, A_80]: (k10_relat_1(k5_relat_1(B_78, C_79), A_80)=k10_relat_1(B_78, k10_relat_1(C_79, A_80)) | ~v1_relat_1(C_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.29/1.78  tff(c_695, plain, (![A_16, B_17, A_80]: (k10_relat_1(k6_relat_1(A_16), k10_relat_1(B_17, A_80))=k10_relat_1(k7_relat_1(B_17, A_16), A_80) | ~v1_relat_1(B_17) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_24, c_673])).
% 4.29/1.78  tff(c_1053, plain, (![A_100, B_101, A_102]: (k10_relat_1(k6_relat_1(A_100), k10_relat_1(B_101, A_102))=k10_relat_1(k7_relat_1(B_101, A_100), A_102) | ~v1_relat_1(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_695])).
% 4.29/1.78  tff(c_12, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.29/1.78  tff(c_95, plain, (![A_38]: (k5_relat_1(k6_relat_1(k1_relat_1(A_38)), A_38)=A_38 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.29/1.78  tff(c_104, plain, (![A_9]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_9))=k6_relat_1(A_9) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_95])).
% 4.29/1.78  tff(c_108, plain, (![A_9]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_9))=k6_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_104])).
% 4.29/1.78  tff(c_698, plain, (![A_9, A_80]: (k10_relat_1(k6_relat_1(A_9), k10_relat_1(k6_relat_1(A_9), A_80))=k10_relat_1(k6_relat_1(A_9), A_80) | ~v1_relat_1(k6_relat_1(A_9)) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_673])).
% 4.29/1.78  tff(c_713, plain, (![A_9, A_80]: (k10_relat_1(k6_relat_1(A_9), k10_relat_1(k6_relat_1(A_9), A_80))=k10_relat_1(k6_relat_1(A_9), A_80))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_698])).
% 4.29/1.78  tff(c_578, plain, (![A_71, A_72]: (k9_relat_1(k6_relat_1(A_71), A_72)=k10_relat_1(k6_relat_1(A_71), A_72))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_34, c_571])).
% 4.29/1.78  tff(c_36, plain, (![B_22, A_21]: (r1_tarski(k10_relat_1(B_22, k9_relat_1(B_22, A_21)), A_21) | ~v2_funct_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.29/1.78  tff(c_584, plain, (![A_71, A_72]: (r1_tarski(k10_relat_1(k6_relat_1(A_71), k10_relat_1(k6_relat_1(A_71), A_72)), A_72) | ~v2_funct_1(k6_relat_1(A_71)) | ~v1_funct_1(k6_relat_1(A_71)) | ~v1_relat_1(k6_relat_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_578, c_36])).
% 4.29/1.78  tff(c_597, plain, (![A_71, A_72]: (r1_tarski(k10_relat_1(k6_relat_1(A_71), k10_relat_1(k6_relat_1(A_71), A_72)), A_72))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_34, c_584])).
% 4.29/1.78  tff(c_937, plain, (![A_71, A_72]: (r1_tarski(k10_relat_1(k6_relat_1(A_71), A_72), A_72))), inference(demodulation, [status(thm), theory('equality')], [c_713, c_597])).
% 4.29/1.78  tff(c_1202, plain, (![B_105, A_106, A_107]: (r1_tarski(k10_relat_1(k7_relat_1(B_105, A_106), A_107), k10_relat_1(B_105, A_107)) | ~v1_relat_1(B_105))), inference(superposition, [status(thm), theory('equality')], [c_1053, c_937])).
% 4.29/1.78  tff(c_1242, plain, (![A_54, A_107, A_55]: (r1_tarski(k10_relat_1(k6_relat_1(A_54), A_107), k10_relat_1(k6_relat_1(A_55), A_107)) | ~v1_relat_1(k6_relat_1(A_55)) | ~r1_tarski(A_54, A_55))), inference(superposition, [status(thm), theory('equality')], [c_317, c_1202])).
% 4.29/1.78  tff(c_1940, plain, (![A_129, A_130, A_131]: (r1_tarski(k10_relat_1(k6_relat_1(A_129), A_130), k10_relat_1(k6_relat_1(A_131), A_130)) | ~r1_tarski(A_129, A_131))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1242])).
% 4.29/1.78  tff(c_2532, plain, (![A_146, A_147, A_148]: (r1_tarski(A_146, k10_relat_1(k6_relat_1(A_147), A_146)) | ~r1_tarski(A_148, A_147) | ~r1_tarski(A_146, A_148))), inference(superposition, [status(thm), theory('equality')], [c_577, c_1940])).
% 4.29/1.78  tff(c_2584, plain, (![A_149]: (r1_tarski(A_149, k10_relat_1(k6_relat_1(k1_relat_1('#skF_2')), A_149)) | ~r1_tarski(A_149, '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_2532])).
% 4.29/1.78  tff(c_1005, plain, (![A_96, A_97]: (r1_tarski(k10_relat_1(k6_relat_1(A_96), A_97), A_97))), inference(demodulation, [status(thm), theory('equality')], [c_713, c_597])).
% 4.29/1.78  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.29/1.78  tff(c_1026, plain, (![A_96, A_97]: (k10_relat_1(k6_relat_1(A_96), A_97)=A_97 | ~r1_tarski(A_97, k10_relat_1(k6_relat_1(A_96), A_97)))), inference(resolution, [status(thm)], [c_1005, c_2])).
% 4.29/1.78  tff(c_2709, plain, (![A_152]: (k10_relat_1(k6_relat_1(k1_relat_1('#skF_2')), A_152)=A_152 | ~r1_tarski(A_152, '#skF_1'))), inference(resolution, [status(thm)], [c_2584, c_1026])).
% 4.29/1.78  tff(c_20, plain, (![A_13]: (k5_relat_1(k6_relat_1(k1_relat_1(A_13)), A_13)=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.29/1.78  tff(c_753, plain, (![B_85, A_86, C_87]: (r1_tarski(k10_relat_1(B_85, A_86), k10_relat_1(k5_relat_1(B_85, C_87), k9_relat_1(C_87, A_86))) | ~r1_tarski(k2_relat_1(B_85), k1_relat_1(C_87)) | ~v1_relat_1(C_87) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.29/1.78  tff(c_798, plain, (![A_13, A_86]: (r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_13)), A_86), k10_relat_1(A_13, k9_relat_1(A_13, A_86))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(A_13))), k1_relat_1(A_13)) | ~v1_relat_1(A_13) | ~v1_relat_1(k6_relat_1(k1_relat_1(A_13))) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_20, c_753])).
% 4.29/1.78  tff(c_821, plain, (![A_13, A_86]: (r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_13)), A_86), k10_relat_1(A_13, k9_relat_1(A_13, A_86))) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6, c_14, c_798])).
% 4.29/1.78  tff(c_2761, plain, (![A_152]: (r1_tarski(A_152, k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_152))) | ~v1_relat_1('#skF_2') | ~r1_tarski(A_152, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2709, c_821])).
% 4.29/1.78  tff(c_2905, plain, (![A_153]: (r1_tarski(A_153, k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_153))) | ~r1_tarski(A_153, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2761])).
% 4.29/1.78  tff(c_460, plain, (![B_62, A_63]: (r1_tarski(k10_relat_1(B_62, k9_relat_1(B_62, A_63)), A_63) | ~v2_funct_1(B_62) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.29/1.78  tff(c_469, plain, (![B_62, A_63]: (k10_relat_1(B_62, k9_relat_1(B_62, A_63))=A_63 | ~r1_tarski(A_63, k10_relat_1(B_62, k9_relat_1(B_62, A_63))) | ~v2_funct_1(B_62) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_460, c_2])).
% 4.29/1.78  tff(c_2908, plain, (![A_153]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_153))=A_153 | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~r1_tarski(A_153, '#skF_1'))), inference(resolution, [status(thm)], [c_2905, c_469])).
% 4.29/1.78  tff(c_2967, plain, (![A_155]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_155))=A_155 | ~r1_tarski(A_155, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_2908])).
% 4.29/1.78  tff(c_42, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.29/1.78  tff(c_3012, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2967, c_42])).
% 4.29/1.78  tff(c_3047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3012])).
% 4.29/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.29/1.78  
% 4.29/1.78  Inference rules
% 4.29/1.78  ----------------------
% 4.29/1.78  #Ref     : 0
% 4.29/1.78  #Sup     : 673
% 4.29/1.78  #Fact    : 0
% 4.29/1.78  #Define  : 0
% 4.29/1.78  #Split   : 1
% 4.29/1.78  #Chain   : 0
% 4.29/1.78  #Close   : 0
% 4.29/1.78  
% 4.29/1.78  Ordering : KBO
% 4.29/1.78  
% 4.29/1.78  Simplification rules
% 4.29/1.78  ----------------------
% 4.29/1.78  #Subsume      : 75
% 4.29/1.78  #Demod        : 756
% 4.29/1.78  #Tautology    : 291
% 4.29/1.78  #SimpNegUnit  : 0
% 4.29/1.78  #BackRed      : 4
% 4.29/1.78  
% 4.29/1.78  #Partial instantiations: 0
% 4.29/1.78  #Strategies tried      : 1
% 4.29/1.78  
% 4.29/1.78  Timing (in seconds)
% 4.29/1.78  ----------------------
% 4.29/1.78  Preprocessing        : 0.32
% 4.29/1.78  Parsing              : 0.17
% 4.29/1.78  CNF conversion       : 0.02
% 4.29/1.78  Main loop            : 0.63
% 4.29/1.78  Inferencing          : 0.22
% 4.29/1.78  Reduction            : 0.22
% 4.29/1.78  Demodulation         : 0.17
% 4.29/1.78  BG Simplification    : 0.03
% 4.29/1.78  Subsumption          : 0.12
% 4.29/1.78  Abstraction          : 0.04
% 4.29/1.78  MUC search           : 0.00
% 4.29/1.78  Cooper               : 0.00
% 4.29/1.78  Total                : 1.00
% 4.29/1.78  Index Insertion      : 0.00
% 4.29/1.78  Index Deletion       : 0.00
% 4.29/1.78  Index Matching       : 0.00
% 4.29/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
