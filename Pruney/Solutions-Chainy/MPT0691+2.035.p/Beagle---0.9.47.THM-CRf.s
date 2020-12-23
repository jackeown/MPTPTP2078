%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:44 EST 2020

% Result     : Theorem 27.04s
% Output     : CNFRefutation 27.30s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 747 expanded)
%              Number of leaves         :   25 ( 258 expanded)
%              Depth                    :   20
%              Number of atoms          :  142 (1433 expanded)
%              Number of equality atoms :   35 ( 371 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_16] :
      ( k10_relat_1(A_16,k2_relat_1(A_16)) = k1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_917,plain,(
    ! [C_69,A_70,B_71] :
      ( r1_tarski(k10_relat_1(C_69,A_70),k10_relat_1(C_69,B_71))
      | ~ r1_tarski(A_70,B_71)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4378,plain,(
    ! [A_138,B_139] :
      ( r1_tarski(k1_relat_1(A_138),k10_relat_1(A_138,B_139))
      | ~ r1_tarski(k2_relat_1(A_138),B_139)
      | ~ v1_relat_1(A_138)
      | ~ v1_relat_1(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_917])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_86,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_86])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_158,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(k3_xboole_0(A_40,C_41),B_42)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_234,plain,(
    ! [B_45,A_46,B_47] :
      ( r1_tarski(k3_xboole_0(B_45,A_46),B_47)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_158])).

tff(c_245,plain,(
    ! [B_47] :
      ( r1_tarski('#skF_1',B_47)
      | ~ r1_tarski(k1_relat_1('#skF_2'),B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_234])).

tff(c_4395,plain,(
    ! [B_139] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_2',B_139))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_139)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4378,c_245])).

tff(c_5238,plain,(
    ! [B_154] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_2',B_154))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4395])).

tff(c_5259,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_5238])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5272,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5259,c_14])).

tff(c_26,plain,(
    ! [A_22,C_24,B_23] :
      ( k3_xboole_0(A_22,k10_relat_1(C_24,B_23)) = k10_relat_1(k7_relat_1(C_24,A_22),B_23)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5350,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5272,c_26])).

tff(c_5419,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5350])).

tff(c_588,plain,(
    ! [B_59,A_60] :
      ( k7_relat_1(B_59,A_60) = B_59
      | ~ r1_tarski(k1_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_593,plain,(
    ! [B_59] :
      ( k7_relat_1(B_59,k1_relat_1(B_59)) = B_59
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_8,c_588])).

tff(c_707,plain,(
    ! [A_64,C_65,B_66] :
      ( k3_xboole_0(A_64,k10_relat_1(C_65,B_66)) = k10_relat_1(k7_relat_1(C_65,A_64),B_66)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_936,plain,(
    ! [C_72,A_73,B_74] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_72,A_73),B_74),A_73)
      | ~ v1_relat_1(C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_12])).

tff(c_2005,plain,(
    ! [B_95,B_96] :
      ( r1_tarski(k10_relat_1(B_95,B_96),k1_relat_1(B_95))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_936])).

tff(c_2010,plain,(
    ! [B_95,B_96] :
      ( k3_xboole_0(k10_relat_1(B_95,B_96),k1_relat_1(B_95)) = k10_relat_1(B_95,B_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_2005,c_14])).

tff(c_33644,plain,(
    ! [B_462,B_463] :
      ( k3_xboole_0(k1_relat_1(B_462),k10_relat_1(B_462,B_463)) = k10_relat_1(B_462,B_463)
      | ~ v1_relat_1(B_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2010])).

tff(c_33982,plain,(
    ! [B_464,B_465] :
      ( r1_tarski(k10_relat_1(B_464,B_465),k1_relat_1(B_464))
      | ~ v1_relat_1(B_464) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33644,c_12])).

tff(c_34022,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5419,c_33982])).

tff(c_34992,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_34022])).

tff(c_34995,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_34992])).

tff(c_34999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34995])).

tff(c_35001,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_34022])).

tff(c_102,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_86])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k3_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2632,plain,(
    ! [C_104,A_105,B_106,B_107] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_104,A_105),B_106),B_107)
      | ~ r1_tarski(A_105,B_107)
      | ~ v1_relat_1(C_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_10])).

tff(c_2660,plain,(
    ! [C_104,A_105,B_107] :
      ( r1_tarski(k1_relat_1(k7_relat_1(C_104,A_105)),B_107)
      | ~ r1_tarski(A_105,B_107)
      | ~ v1_relat_1(C_104)
      | ~ v1_relat_1(k7_relat_1(C_104,A_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2632])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89374,plain,(
    ! [B_901,B_902] :
      ( k10_relat_1(B_901,B_902) = k1_relat_1(B_901)
      | ~ r1_tarski(k1_relat_1(B_901),k10_relat_1(B_901,B_902))
      | ~ v1_relat_1(B_901) ) ),
    inference(resolution,[status(thm)],[c_2005,c_4])).

tff(c_89445,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),'#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5419,c_89374])).

tff(c_89463,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35001,c_5419,c_89445])).

tff(c_89929,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_89463])).

tff(c_89932,plain,
    ( ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2660,c_89929])).

tff(c_89939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35001,c_32,c_8,c_89932])).

tff(c_89940,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_89463])).

tff(c_90052,plain,
    ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_89940,c_593])).

tff(c_90117,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35001,c_90052])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3964,plain,(
    ! [A_127,A_128] :
      ( k10_relat_1(k7_relat_1(A_127,A_128),k2_relat_1(A_127)) = k3_xboole_0(A_128,k1_relat_1(A_127))
      | ~ v1_relat_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_707])).

tff(c_3997,plain,(
    ! [B_15,A_14,A_128] :
      ( k10_relat_1(k7_relat_1(k7_relat_1(B_15,A_14),A_128),k9_relat_1(B_15,A_14)) = k3_xboole_0(A_128,k1_relat_1(k7_relat_1(B_15,A_14)))
      | ~ v1_relat_1(k7_relat_1(B_15,A_14))
      | ~ v1_relat_1(k7_relat_1(B_15,A_14))
      | ~ v1_relat_1(B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3964])).

tff(c_90263,plain,
    ( k3_xboole_0('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90117,c_3997])).

tff(c_90414,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_35001,c_35001,c_102,c_89940,c_90263])).

tff(c_1860,plain,(
    ! [C_91,B_92,A_93] :
      ( k3_xboole_0(k10_relat_1(C_91,B_92),A_93) = k10_relat_1(k7_relat_1(C_91,A_93),B_92)
      | ~ v1_relat_1(C_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_2])).

tff(c_1950,plain,(
    ! [C_91,A_93,B_92] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_91,A_93),B_92),k10_relat_1(C_91,B_92))
      | ~ v1_relat_1(C_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1860,c_12])).

tff(c_90682,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90414,c_1950])).

tff(c_90849,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_90682])).

tff(c_90851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_90849])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.04/18.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.04/18.07  
% 27.04/18.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.04/18.07  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 27.04/18.07  
% 27.04/18.07  %Foreground sorts:
% 27.04/18.07  
% 27.04/18.07  
% 27.04/18.07  %Background operators:
% 27.04/18.07  
% 27.04/18.07  
% 27.04/18.07  %Foreground operators:
% 27.04/18.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.04/18.07  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 27.04/18.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.04/18.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 27.04/18.07  tff('#skF_2', type, '#skF_2': $i).
% 27.04/18.07  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 27.04/18.07  tff('#skF_1', type, '#skF_1': $i).
% 27.04/18.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.04/18.07  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 27.04/18.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 27.04/18.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.04/18.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.04/18.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 27.04/18.07  
% 27.30/18.09  tff(f_78, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 27.30/18.09  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 27.30/18.09  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.30/18.09  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 27.30/18.09  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 27.30/18.09  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 27.30/18.09  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 27.30/18.09  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 27.30/18.09  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 27.30/18.09  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 27.30/18.09  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 27.30/18.09  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 27.30/18.09  tff(c_28, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.30/18.09  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.30/18.09  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 27.30/18.09  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.30/18.09  tff(c_20, plain, (![A_16]: (k10_relat_1(A_16, k2_relat_1(A_16))=k1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 27.30/18.09  tff(c_917, plain, (![C_69, A_70, B_71]: (r1_tarski(k10_relat_1(C_69, A_70), k10_relat_1(C_69, B_71)) | ~r1_tarski(A_70, B_71) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_61])).
% 27.30/18.09  tff(c_4378, plain, (![A_138, B_139]: (r1_tarski(k1_relat_1(A_138), k10_relat_1(A_138, B_139)) | ~r1_tarski(k2_relat_1(A_138), B_139) | ~v1_relat_1(A_138) | ~v1_relat_1(A_138))), inference(superposition, [status(thm), theory('equality')], [c_20, c_917])).
% 27.30/18.09  tff(c_30, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.30/18.09  tff(c_86, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 27.30/18.09  tff(c_101, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_30, c_86])).
% 27.30/18.09  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.30/18.09  tff(c_158, plain, (![A_40, C_41, B_42]: (r1_tarski(k3_xboole_0(A_40, C_41), B_42) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.30/18.09  tff(c_234, plain, (![B_45, A_46, B_47]: (r1_tarski(k3_xboole_0(B_45, A_46), B_47) | ~r1_tarski(A_46, B_47))), inference(superposition, [status(thm), theory('equality')], [c_2, c_158])).
% 27.30/18.09  tff(c_245, plain, (![B_47]: (r1_tarski('#skF_1', B_47) | ~r1_tarski(k1_relat_1('#skF_2'), B_47))), inference(superposition, [status(thm), theory('equality')], [c_101, c_234])).
% 27.30/18.09  tff(c_4395, plain, (![B_139]: (r1_tarski('#skF_1', k10_relat_1('#skF_2', B_139)) | ~r1_tarski(k2_relat_1('#skF_2'), B_139) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_4378, c_245])).
% 27.30/18.09  tff(c_5238, plain, (![B_154]: (r1_tarski('#skF_1', k10_relat_1('#skF_2', B_154)) | ~r1_tarski(k2_relat_1('#skF_2'), B_154))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4395])).
% 27.30/18.09  tff(c_5259, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_5238])).
% 27.30/18.09  tff(c_14, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 27.30/18.09  tff(c_5272, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))='#skF_1'), inference(resolution, [status(thm)], [c_5259, c_14])).
% 27.30/18.09  tff(c_26, plain, (![A_22, C_24, B_23]: (k3_xboole_0(A_22, k10_relat_1(C_24, B_23))=k10_relat_1(k7_relat_1(C_24, A_22), B_23) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 27.30/18.09  tff(c_5350, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5272, c_26])).
% 27.30/18.09  tff(c_5419, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5350])).
% 27.30/18.09  tff(c_588, plain, (![B_59, A_60]: (k7_relat_1(B_59, A_60)=B_59 | ~r1_tarski(k1_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_67])).
% 27.30/18.09  tff(c_593, plain, (![B_59]: (k7_relat_1(B_59, k1_relat_1(B_59))=B_59 | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_8, c_588])).
% 27.30/18.09  tff(c_707, plain, (![A_64, C_65, B_66]: (k3_xboole_0(A_64, k10_relat_1(C_65, B_66))=k10_relat_1(k7_relat_1(C_65, A_64), B_66) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_71])).
% 27.30/18.09  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 27.30/18.09  tff(c_936, plain, (![C_72, A_73, B_74]: (r1_tarski(k10_relat_1(k7_relat_1(C_72, A_73), B_74), A_73) | ~v1_relat_1(C_72))), inference(superposition, [status(thm), theory('equality')], [c_707, c_12])).
% 27.30/18.09  tff(c_2005, plain, (![B_95, B_96]: (r1_tarski(k10_relat_1(B_95, B_96), k1_relat_1(B_95)) | ~v1_relat_1(B_95) | ~v1_relat_1(B_95))), inference(superposition, [status(thm), theory('equality')], [c_593, c_936])).
% 27.30/18.09  tff(c_2010, plain, (![B_95, B_96]: (k3_xboole_0(k10_relat_1(B_95, B_96), k1_relat_1(B_95))=k10_relat_1(B_95, B_96) | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_2005, c_14])).
% 27.30/18.09  tff(c_33644, plain, (![B_462, B_463]: (k3_xboole_0(k1_relat_1(B_462), k10_relat_1(B_462, B_463))=k10_relat_1(B_462, B_463) | ~v1_relat_1(B_462))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2010])).
% 27.30/18.09  tff(c_33982, plain, (![B_464, B_465]: (r1_tarski(k10_relat_1(B_464, B_465), k1_relat_1(B_464)) | ~v1_relat_1(B_464))), inference(superposition, [status(thm), theory('equality')], [c_33644, c_12])).
% 27.30/18.09  tff(c_34022, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5419, c_33982])).
% 27.30/18.09  tff(c_34992, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_34022])).
% 27.30/18.09  tff(c_34995, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_34992])).
% 27.30/18.09  tff(c_34999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_34995])).
% 27.30/18.09  tff(c_35001, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_34022])).
% 27.30/18.09  tff(c_102, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_86])).
% 27.30/18.09  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k3_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.30/18.09  tff(c_2632, plain, (![C_104, A_105, B_106, B_107]: (r1_tarski(k10_relat_1(k7_relat_1(C_104, A_105), B_106), B_107) | ~r1_tarski(A_105, B_107) | ~v1_relat_1(C_104))), inference(superposition, [status(thm), theory('equality')], [c_707, c_10])).
% 27.30/18.09  tff(c_2660, plain, (![C_104, A_105, B_107]: (r1_tarski(k1_relat_1(k7_relat_1(C_104, A_105)), B_107) | ~r1_tarski(A_105, B_107) | ~v1_relat_1(C_104) | ~v1_relat_1(k7_relat_1(C_104, A_105)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2632])).
% 27.30/18.09  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.30/18.09  tff(c_89374, plain, (![B_901, B_902]: (k10_relat_1(B_901, B_902)=k1_relat_1(B_901) | ~r1_tarski(k1_relat_1(B_901), k10_relat_1(B_901, B_902)) | ~v1_relat_1(B_901))), inference(resolution, [status(thm)], [c_2005, c_4])).
% 27.30/18.09  tff(c_89445, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5419, c_89374])).
% 27.30/18.09  tff(c_89463, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_35001, c_5419, c_89445])).
% 27.30/18.09  tff(c_89929, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(splitLeft, [status(thm)], [c_89463])).
% 27.30/18.09  tff(c_89932, plain, (~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_2660, c_89929])).
% 27.30/18.09  tff(c_89939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35001, c_32, c_8, c_89932])).
% 27.30/18.09  tff(c_89940, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(splitRight, [status(thm)], [c_89463])).
% 27.30/18.09  tff(c_90052, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_89940, c_593])).
% 27.30/18.09  tff(c_90117, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_35001, c_90052])).
% 27.30/18.09  tff(c_18, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 27.30/18.09  tff(c_3964, plain, (![A_127, A_128]: (k10_relat_1(k7_relat_1(A_127, A_128), k2_relat_1(A_127))=k3_xboole_0(A_128, k1_relat_1(A_127)) | ~v1_relat_1(A_127) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_20, c_707])).
% 27.30/18.09  tff(c_3997, plain, (![B_15, A_14, A_128]: (k10_relat_1(k7_relat_1(k7_relat_1(B_15, A_14), A_128), k9_relat_1(B_15, A_14))=k3_xboole_0(A_128, k1_relat_1(k7_relat_1(B_15, A_14))) | ~v1_relat_1(k7_relat_1(B_15, A_14)) | ~v1_relat_1(k7_relat_1(B_15, A_14)) | ~v1_relat_1(B_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3964])).
% 27.30/18.09  tff(c_90263, plain, (k3_xboole_0('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90117, c_3997])).
% 27.30/18.09  tff(c_90414, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_35001, c_35001, c_102, c_89940, c_90263])).
% 27.30/18.09  tff(c_1860, plain, (![C_91, B_92, A_93]: (k3_xboole_0(k10_relat_1(C_91, B_92), A_93)=k10_relat_1(k7_relat_1(C_91, A_93), B_92) | ~v1_relat_1(C_91))), inference(superposition, [status(thm), theory('equality')], [c_707, c_2])).
% 27.30/18.09  tff(c_1950, plain, (![C_91, A_93, B_92]: (r1_tarski(k10_relat_1(k7_relat_1(C_91, A_93), B_92), k10_relat_1(C_91, B_92)) | ~v1_relat_1(C_91))), inference(superposition, [status(thm), theory('equality')], [c_1860, c_12])).
% 27.30/18.09  tff(c_90682, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90414, c_1950])).
% 27.30/18.09  tff(c_90849, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_90682])).
% 27.30/18.09  tff(c_90851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_90849])).
% 27.30/18.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.30/18.09  
% 27.30/18.09  Inference rules
% 27.30/18.09  ----------------------
% 27.30/18.09  #Ref     : 0
% 27.30/18.09  #Sup     : 23333
% 27.30/18.09  #Fact    : 0
% 27.30/18.09  #Define  : 0
% 27.30/18.09  #Split   : 5
% 27.30/18.09  #Chain   : 0
% 27.30/18.09  #Close   : 0
% 27.30/18.09  
% 27.30/18.09  Ordering : KBO
% 27.30/18.09  
% 27.30/18.09  Simplification rules
% 27.30/18.09  ----------------------
% 27.30/18.09  #Subsume      : 4597
% 27.30/18.09  #Demod        : 14439
% 27.30/18.09  #Tautology    : 7134
% 27.30/18.09  #SimpNegUnit  : 1
% 27.30/18.09  #BackRed      : 12
% 27.30/18.09  
% 27.30/18.09  #Partial instantiations: 0
% 27.30/18.09  #Strategies tried      : 1
% 27.30/18.09  
% 27.30/18.09  Timing (in seconds)
% 27.30/18.09  ----------------------
% 27.30/18.09  Preprocessing        : 0.32
% 27.30/18.09  Parsing              : 0.17
% 27.30/18.09  CNF conversion       : 0.02
% 27.30/18.09  Main loop            : 16.95
% 27.30/18.09  Inferencing          : 1.88
% 27.30/18.09  Reduction            : 7.82
% 27.30/18.09  Demodulation         : 7.03
% 27.30/18.09  BG Simplification    : 0.32
% 27.30/18.09  Subsumption          : 6.16
% 27.30/18.09  Abstraction          : 0.48
% 27.30/18.09  MUC search           : 0.00
% 27.30/18.09  Cooper               : 0.00
% 27.30/18.09  Total                : 17.31
% 27.30/18.09  Index Insertion      : 0.00
% 27.30/18.09  Index Deletion       : 0.00
% 27.30/18.09  Index Matching       : 0.00
% 27.30/18.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
