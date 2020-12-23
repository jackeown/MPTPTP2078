%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:45 EST 2020

% Result     : Theorem 18.56s
% Output     : CNFRefutation 18.59s
% Verified   : 
% Statistics : Number of formulae       :  135 (1034 expanded)
%              Number of leaves         :   28 ( 367 expanded)
%              Depth                    :   28
%              Number of atoms          :  276 (2058 expanded)
%              Number of equality atoms :   47 ( 444 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_86,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    ! [A_25] : k2_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [A_25] : k1_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_97,plain,(
    ! [A_38] :
      ( k9_relat_1(A_38,k1_relat_1(A_38)) = k2_relat_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,(
    ! [A_25] :
      ( k9_relat_1(k6_relat_1(A_25),A_25) = k2_relat_1(k6_relat_1(A_25))
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_97])).

tff(c_110,plain,(
    ! [A_25] : k9_relat_1(k6_relat_1(A_25),A_25) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_106])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_63,plain,(
    ! [A_34] :
      ( k10_relat_1(A_34,k2_relat_1(A_34)) = k1_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    ! [A_25] :
      ( k10_relat_1(k6_relat_1(A_25),A_25) = k1_relat_1(k6_relat_1(A_25))
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_63])).

tff(c_76,plain,(
    ! [A_25] : k10_relat_1(k6_relat_1(A_25),A_25) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_72])).

tff(c_393,plain,(
    ! [C_73,A_74,B_75] :
      ( r1_tarski(k10_relat_1(C_73,A_74),k10_relat_1(C_73,B_75))
      | ~ r1_tarski(A_74,B_75)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_409,plain,(
    ! [A_25,B_75] :
      ( r1_tarski(A_25,k10_relat_1(k6_relat_1(A_25),B_75))
      | ~ r1_tarski(A_25,B_75)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_393])).

tff(c_430,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(A_76,k10_relat_1(k6_relat_1(A_76),B_77))
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_409])).

tff(c_120,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(k10_relat_1(B_40,A_41),k1_relat_1(B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_131,plain,(
    ! [A_25,A_41] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_25),A_41),A_25)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_120])).

tff(c_138,plain,(
    ! [A_42,A_43] : r1_tarski(k10_relat_1(k6_relat_1(A_42),A_43),A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_131])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    ! [A_42,A_43] :
      ( k10_relat_1(k6_relat_1(A_42),A_43) = A_42
      | ~ r1_tarski(A_42,k10_relat_1(k6_relat_1(A_42),A_43)) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_473,plain,(
    ! [A_78,B_79] :
      ( k10_relat_1(k6_relat_1(A_78),B_79) = A_78
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_430,c_148])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( r1_tarski(k10_relat_1(C_17,A_15),k10_relat_1(C_17,B_16))
      | ~ r1_tarski(A_15,B_16)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_482,plain,(
    ! [A_78,B_16,B_79] :
      ( r1_tarski(A_78,k10_relat_1(k6_relat_1(A_78),B_16))
      | ~ r1_tarski(B_79,B_16)
      | ~ v1_relat_1(k6_relat_1(A_78))
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_20])).

tff(c_1390,plain,(
    ! [A_117,B_118,B_119] :
      ( r1_tarski(A_117,k10_relat_1(k6_relat_1(A_117),B_118))
      | ~ r1_tarski(B_119,B_118)
      | ~ r1_tarski(A_117,B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_482])).

tff(c_1443,plain,(
    ! [A_117] :
      ( r1_tarski(A_117,k10_relat_1(k6_relat_1(A_117),k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_117,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_1390])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k10_relat_1(B_13,A_12),k1_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_153,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(A_46,C_47)
      | ~ r1_tarski(B_48,C_47)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_166,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_49,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_153])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_227,plain,(
    ! [A_56,A_57] :
      ( r1_tarski(A_56,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_56,A_57)
      | ~ r1_tarski(A_57,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_166,c_8])).

tff(c_243,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k10_relat_1(B_13,A_12),k1_relat_1('#skF_2'))
      | ~ r1_tarski(k1_relat_1(B_13),'#skF_1')
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_227])).

tff(c_137,plain,(
    ! [A_25,A_41] : r1_tarski(k10_relat_1(k6_relat_1(A_25),A_41),A_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_131])).

tff(c_173,plain,(
    ! [A_50,A_51,A_52] :
      ( r1_tarski(A_50,A_51)
      | ~ r1_tarski(A_50,k10_relat_1(k6_relat_1(A_51),A_52)) ) ),
    inference(resolution,[status(thm)],[c_137,c_153])).

tff(c_189,plain,(
    ! [A_51,A_52,A_41] : r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(A_51),A_52)),A_41),A_51) ),
    inference(resolution,[status(thm)],[c_137,c_173])).

tff(c_171,plain,(
    ! [A_3,A_49] :
      ( r1_tarski(A_3,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_3,A_49)
      | ~ r1_tarski(A_49,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_166,c_8])).

tff(c_769,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(A_90,k1_relat_1('#skF_2'))
      | ~ r1_tarski(k10_relat_1(k6_relat_1(A_90),B_91),'#skF_1')
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_430,c_171])).

tff(c_2776,plain,(
    ! [A_153,A_154] :
      ( r1_tarski(k10_relat_1(k6_relat_1('#skF_1'),A_153),k1_relat_1('#skF_2'))
      | ~ r1_tarski(k10_relat_1(k6_relat_1('#skF_1'),A_153),A_154) ) ),
    inference(resolution,[status(thm)],[c_189,c_769])).

tff(c_2812,plain,(
    ! [A_12] :
      ( r1_tarski(k10_relat_1(k6_relat_1('#skF_1'),A_12),k1_relat_1('#skF_2'))
      | ~ r1_tarski(k1_relat_1(k6_relat_1('#skF_1')),'#skF_1')
      | ~ v1_relat_1(k6_relat_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_243,c_2776])).

tff(c_2869,plain,(
    ! [A_155] : r1_tarski(k10_relat_1(k6_relat_1('#skF_1'),A_155),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6,c_26,c_2812])).

tff(c_545,plain,(
    ! [A_78,B_16,B_79] :
      ( r1_tarski(A_78,k10_relat_1(k6_relat_1(A_78),B_16))
      | ~ r1_tarski(B_79,B_16)
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_482])).

tff(c_4312,plain,(
    ! [A_180,A_181] :
      ( r1_tarski(A_180,k10_relat_1(k6_relat_1(A_180),k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_180,k10_relat_1(k6_relat_1('#skF_1'),A_181)) ) ),
    inference(resolution,[status(thm)],[c_2869,c_545])).

tff(c_4339,plain,
    ( r1_tarski('#skF_1',k10_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1443,c_4312])).

tff(c_4400,plain,(
    r1_tarski('#skF_1',k10_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4339])).

tff(c_4473,plain,(
    k10_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4400,c_148])).

tff(c_24,plain,(
    ! [A_22,B_24] :
      ( k10_relat_1(A_22,k1_relat_1(B_24)) = k1_relat_1(k5_relat_1(A_22,B_24))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4559,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4473,c_24])).

tff(c_4646,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40,c_4559])).

tff(c_4739,plain,(
    ! [A_12] :
      ( r1_tarski(k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'),A_12),'#skF_1')
      | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4646,c_16])).

tff(c_10820,plain,(
    ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4739])).

tff(c_10823,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_10820])).

tff(c_10827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40,c_10823])).

tff(c_10828,plain,(
    ! [A_12] : r1_tarski(k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'),A_12),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_4739])).

tff(c_681,plain,(
    ! [B_82,A_83] :
      ( k9_relat_1(B_82,k2_relat_1(A_83)) = k2_relat_1(k5_relat_1(A_83,B_82))
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_698,plain,(
    ! [A_25,B_82] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_25),B_82)) = k9_relat_1(B_82,A_25)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_681])).

tff(c_706,plain,(
    ! [A_25,B_82] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_25),B_82)) = k9_relat_1(B_82,A_25)
      | ~ v1_relat_1(B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_698])).

tff(c_10829,plain,(
    v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4739])).

tff(c_18,plain,(
    ! [A_14] :
      ( k10_relat_1(A_14,k2_relat_1(A_14)) = k1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34182,plain,(
    ! [A_479,B_480,A_481] :
      ( r1_tarski(A_479,k10_relat_1(k6_relat_1(A_479),k1_relat_1(B_480)))
      | ~ r1_tarski(A_479,k10_relat_1(B_480,A_481))
      | ~ v1_relat_1(B_480) ) ),
    inference(resolution,[status(thm)],[c_16,c_1390])).

tff(c_34530,plain,(
    ! [B_482,A_483] :
      ( r1_tarski(k10_relat_1(B_482,A_483),k10_relat_1(k6_relat_1(k10_relat_1(B_482,A_483)),k1_relat_1(B_482)))
      | ~ v1_relat_1(B_482) ) ),
    inference(resolution,[status(thm)],[c_6,c_34182])).

tff(c_32,plain,(
    ! [A_26] : v1_funct_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_457,plain,(
    ! [A_76,B_77] :
      ( k10_relat_1(k6_relat_1(A_76),B_77) = A_76
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_430,c_148])).

tff(c_277,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k9_relat_1(B_61,k10_relat_1(B_61,A_62)),A_62)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3256,plain,(
    ! [A_163,A_164,B_165] :
      ( r1_tarski(A_163,A_164)
      | ~ r1_tarski(A_163,k9_relat_1(B_165,k10_relat_1(B_165,A_164)))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165) ) ),
    inference(resolution,[status(thm)],[c_277,c_8])).

tff(c_13652,plain,(
    ! [B_290,A_291,A_292] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k9_relat_1(B_290,k10_relat_1(B_290,A_291))),A_292),A_291)
      | ~ v1_funct_1(B_290)
      | ~ v1_relat_1(B_290) ) ),
    inference(resolution,[status(thm)],[c_137,c_3256])).

tff(c_13816,plain,(
    ! [A_76,A_292,B_77] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_76),A_76)),A_292),B_77)
      | ~ v1_funct_1(k6_relat_1(A_76))
      | ~ v1_relat_1(k6_relat_1(A_76))
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_13652])).

tff(c_13895,plain,(
    ! [A_293,A_294,B_295] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_293),A_294),B_295)
      | ~ r1_tarski(A_293,B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_110,c_13816])).

tff(c_14072,plain,(
    ! [A_293,A_294,B_295] :
      ( k10_relat_1(k6_relat_1(A_293),A_294) = B_295
      | ~ r1_tarski(B_295,k10_relat_1(k6_relat_1(A_293),A_294))
      | ~ r1_tarski(A_293,B_295) ) ),
    inference(resolution,[status(thm)],[c_13895,c_2])).

tff(c_34535,plain,(
    ! [B_482,A_483] :
      ( k10_relat_1(k6_relat_1(k10_relat_1(B_482,A_483)),k1_relat_1(B_482)) = k10_relat_1(B_482,A_483)
      | ~ r1_tarski(k10_relat_1(B_482,A_483),k10_relat_1(B_482,A_483))
      | ~ v1_relat_1(B_482) ) ),
    inference(resolution,[status(thm)],[c_34530,c_14072])).

tff(c_34976,plain,(
    ! [B_484,A_485] :
      ( k10_relat_1(k6_relat_1(k10_relat_1(B_484,A_485)),k1_relat_1(B_484)) = k10_relat_1(B_484,A_485)
      | ~ v1_relat_1(B_484) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_34535])).

tff(c_35298,plain,(
    ! [B_484,A_485] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(B_484,A_485)),B_484)) = k10_relat_1(B_484,A_485)
      | ~ v1_relat_1(B_484)
      | ~ v1_relat_1(k6_relat_1(k10_relat_1(B_484,A_485)))
      | ~ v1_relat_1(B_484) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34976,c_24])).

tff(c_35713,plain,(
    ! [B_486,A_487] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(B_486,A_487)),B_486)) = k10_relat_1(B_486,A_487)
      | ~ v1_relat_1(B_486) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_35298])).

tff(c_66646,plain,(
    ! [A_685] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(A_685)),A_685)) = k10_relat_1(A_685,k2_relat_1(A_685))
      | ~ v1_relat_1(A_685)
      | ~ v1_relat_1(A_685) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_35713])).

tff(c_574,plain,(
    ! [A_80,B_81] :
      ( k10_relat_1(A_80,k1_relat_1(B_81)) = k1_relat_1(k5_relat_1(A_80,B_81))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_427,plain,(
    ! [A_25,B_75] :
      ( r1_tarski(A_25,k10_relat_1(k6_relat_1(A_25),B_75))
      | ~ r1_tarski(A_25,B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_409])).

tff(c_585,plain,(
    ! [A_25,B_81] :
      ( r1_tarski(A_25,k1_relat_1(k5_relat_1(k6_relat_1(A_25),B_81)))
      | ~ r1_tarski(A_25,k1_relat_1(B_81))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_427])).

tff(c_657,plain,(
    ! [A_25,B_81] :
      ( r1_tarski(A_25,k1_relat_1(k5_relat_1(k6_relat_1(A_25),B_81)))
      | ~ r1_tarski(A_25,k1_relat_1(B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_585])).

tff(c_66856,plain,(
    ! [A_685] :
      ( r1_tarski(k1_relat_1(A_685),k10_relat_1(A_685,k2_relat_1(A_685)))
      | ~ r1_tarski(k1_relat_1(A_685),k1_relat_1(A_685))
      | ~ v1_relat_1(A_685)
      | ~ v1_relat_1(A_685)
      | ~ v1_relat_1(A_685) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66646,c_657])).

tff(c_67355,plain,(
    ! [A_688] :
      ( r1_tarski(k1_relat_1(A_688),k10_relat_1(A_688,k2_relat_1(A_688)))
      | ~ v1_relat_1(A_688) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_66856])).

tff(c_67563,plain,
    ( r1_tarski('#skF_1',k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'),k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'))))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4646,c_67355])).

tff(c_67733,plain,(
    r1_tarski('#skF_1',k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'),k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10829,c_67563])).

tff(c_67921,plain,
    ( r1_tarski('#skF_1',k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_67733])).

tff(c_67989,plain,(
    r1_tarski('#skF_1',k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_67921])).

tff(c_68420,plain,
    ( k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ r1_tarski(k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'),k9_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_67989,c_2])).

tff(c_68489,plain,(
    k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10828,c_68420])).

tff(c_22,plain,(
    ! [B_19,C_21,A_18] :
      ( k10_relat_1(k5_relat_1(B_19,C_21),A_18) = k10_relat_1(B_19,k10_relat_1(C_21,A_18))
      | ~ v1_relat_1(C_21)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_68666,plain,
    ( k10_relat_1(k6_relat_1('#skF_1'),k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = '#skF_1'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68489,c_22])).

tff(c_68807,plain,(
    k10_relat_1(k6_relat_1('#skF_1'),k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40,c_68666])).

tff(c_2141,plain,(
    ! [A_137,A_138,A_139] :
      ( r1_tarski(A_137,k10_relat_1(k6_relat_1(A_137),A_138))
      | ~ r1_tarski(A_137,k10_relat_1(k6_relat_1(A_138),A_139)) ) ),
    inference(resolution,[status(thm)],[c_137,c_1390])).

tff(c_2210,plain,(
    ! [A_140,A_141] : r1_tarski(k10_relat_1(k6_relat_1(A_140),A_141),k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(A_140),A_141)),A_140)) ),
    inference(resolution,[status(thm)],[c_6,c_2141])).

tff(c_2287,plain,(
    ! [A_140,A_141] : k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(A_140),A_141)),A_140) = k10_relat_1(k6_relat_1(A_140),A_141) ),
    inference(resolution,[status(thm)],[c_2210,c_148])).

tff(c_6258,plain,(
    ! [C_204,B_205,A_206] :
      ( k10_relat_1(C_204,B_205) = k10_relat_1(C_204,A_206)
      | ~ r1_tarski(k10_relat_1(C_204,B_205),k10_relat_1(C_204,A_206))
      | ~ r1_tarski(A_206,B_205)
      | ~ v1_relat_1(C_204) ) ),
    inference(resolution,[status(thm)],[c_393,c_2])).

tff(c_13434,plain,(
    ! [C_287,B_288,A_289] :
      ( k10_relat_1(C_287,B_288) = k10_relat_1(C_287,A_289)
      | ~ r1_tarski(B_288,A_289)
      | ~ r1_tarski(A_289,B_288)
      | ~ v1_relat_1(C_287) ) ),
    inference(resolution,[status(thm)],[c_20,c_6258])).

tff(c_13544,plain,(
    ! [C_287,A_25,B_75] :
      ( k10_relat_1(C_287,k10_relat_1(k6_relat_1(A_25),B_75)) = k10_relat_1(C_287,A_25)
      | ~ r1_tarski(k10_relat_1(k6_relat_1(A_25),B_75),A_25)
      | ~ v1_relat_1(C_287)
      | ~ r1_tarski(A_25,B_75) ) ),
    inference(resolution,[status(thm)],[c_427,c_13434])).

tff(c_21819,plain,(
    ! [C_393,A_394,B_395] :
      ( k10_relat_1(C_393,k10_relat_1(k6_relat_1(A_394),B_395)) = k10_relat_1(C_393,A_394)
      | ~ v1_relat_1(C_393)
      | ~ r1_tarski(A_394,B_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_13544])).

tff(c_22194,plain,(
    ! [A_140,A_394,B_395] :
      ( k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(A_140),A_394)),A_140) = k10_relat_1(k6_relat_1(A_140),k10_relat_1(k6_relat_1(A_394),B_395))
      | ~ v1_relat_1(k6_relat_1(A_140))
      | ~ r1_tarski(A_394,B_395) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21819,c_2287])).

tff(c_48908,plain,(
    ! [A_542,A_543,B_544] :
      ( k10_relat_1(k6_relat_1(A_542),k10_relat_1(k6_relat_1(A_543),B_544)) = k10_relat_1(k6_relat_1(A_542),A_543)
      | ~ r1_tarski(A_543,B_544) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2287,c_22194])).

tff(c_34,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k9_relat_1(B_28,k10_relat_1(B_28,A_27)),A_27)
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_300,plain,(
    ! [A_63,B_64,A_65] :
      ( r1_tarski(A_63,k1_relat_1(B_64))
      | ~ r1_tarski(A_63,k10_relat_1(B_64,A_65))
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_16,c_153])).

tff(c_323,plain,(
    ! [B_28,B_64,A_65] :
      ( r1_tarski(k9_relat_1(B_28,k10_relat_1(B_28,k10_relat_1(B_64,A_65))),k1_relat_1(B_64))
      | ~ v1_relat_1(B_64)
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(resolution,[status(thm)],[c_34,c_300])).

tff(c_49042,plain,(
    ! [A_542,A_543,B_544] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_542),k10_relat_1(k6_relat_1(A_542),A_543)),k1_relat_1(k6_relat_1(A_543)))
      | ~ v1_relat_1(k6_relat_1(A_543))
      | ~ v1_funct_1(k6_relat_1(A_542))
      | ~ v1_relat_1(k6_relat_1(A_542))
      | ~ r1_tarski(A_543,B_544) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48908,c_323])).

tff(c_49885,plain,(
    ! [A_545,A_546,B_547] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_545),k10_relat_1(k6_relat_1(A_545),A_546)),A_546)
      | ~ r1_tarski(A_546,B_547) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_30,c_26,c_49042])).

tff(c_50251,plain,(
    ! [A_545,B_2] : r1_tarski(k9_relat_1(k6_relat_1(A_545),k10_relat_1(k6_relat_1(A_545),B_2)),B_2) ),
    inference(resolution,[status(thm)],[c_6,c_49885])).

tff(c_69151,plain,(
    r1_tarski(k9_relat_1(k6_relat_1('#skF_1'),'#skF_1'),k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_68807,c_50251])).

tff(c_69546,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_69151])).

tff(c_69548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_69546])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:48:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.56/10.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.59/10.06  
% 18.59/10.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.59/10.06  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 18.59/10.06  
% 18.59/10.06  %Foreground sorts:
% 18.59/10.06  
% 18.59/10.06  
% 18.59/10.06  %Background operators:
% 18.59/10.06  
% 18.59/10.06  
% 18.59/10.06  %Foreground operators:
% 18.59/10.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.59/10.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.59/10.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 18.59/10.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.59/10.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.59/10.06  tff('#skF_2', type, '#skF_2': $i).
% 18.59/10.06  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.59/10.06  tff('#skF_1', type, '#skF_1': $i).
% 18.59/10.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.59/10.06  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 18.59/10.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.59/10.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 18.59/10.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.59/10.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.59/10.06  
% 18.59/10.08  tff(f_103, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 18.59/10.08  tff(f_90, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 18.59/10.08  tff(f_86, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 18.59/10.08  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 18.59/10.08  tff(f_43, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 18.59/10.08  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.59/10.08  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 18.59/10.08  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 18.59/10.08  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 18.59/10.08  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 18.59/10.08  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 18.59/10.08  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 18.59/10.08  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 18.59/10.08  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 18.59/10.08  tff(c_36, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.59/10.08  tff(c_30, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 18.59/10.08  tff(c_28, plain, (![A_25]: (k2_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_86])).
% 18.59/10.08  tff(c_26, plain, (![A_25]: (k1_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_86])).
% 18.59/10.08  tff(c_97, plain, (![A_38]: (k9_relat_1(A_38, k1_relat_1(A_38))=k2_relat_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.59/10.08  tff(c_106, plain, (![A_25]: (k9_relat_1(k6_relat_1(A_25), A_25)=k2_relat_1(k6_relat_1(A_25)) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_97])).
% 18.59/10.08  tff(c_110, plain, (![A_25]: (k9_relat_1(k6_relat_1(A_25), A_25)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_106])).
% 18.59/10.08  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.59/10.08  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.59/10.08  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.59/10.08  tff(c_38, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.59/10.08  tff(c_63, plain, (![A_34]: (k10_relat_1(A_34, k2_relat_1(A_34))=k1_relat_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.59/10.08  tff(c_72, plain, (![A_25]: (k10_relat_1(k6_relat_1(A_25), A_25)=k1_relat_1(k6_relat_1(A_25)) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_63])).
% 18.59/10.08  tff(c_76, plain, (![A_25]: (k10_relat_1(k6_relat_1(A_25), A_25)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_72])).
% 18.59/10.08  tff(c_393, plain, (![C_73, A_74, B_75]: (r1_tarski(k10_relat_1(C_73, A_74), k10_relat_1(C_73, B_75)) | ~r1_tarski(A_74, B_75) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_68])).
% 18.59/10.08  tff(c_409, plain, (![A_25, B_75]: (r1_tarski(A_25, k10_relat_1(k6_relat_1(A_25), B_75)) | ~r1_tarski(A_25, B_75) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_393])).
% 18.59/10.08  tff(c_430, plain, (![A_76, B_77]: (r1_tarski(A_76, k10_relat_1(k6_relat_1(A_76), B_77)) | ~r1_tarski(A_76, B_77))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_409])).
% 18.59/10.08  tff(c_120, plain, (![B_40, A_41]: (r1_tarski(k10_relat_1(B_40, A_41), k1_relat_1(B_40)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_58])).
% 18.59/10.08  tff(c_131, plain, (![A_25, A_41]: (r1_tarski(k10_relat_1(k6_relat_1(A_25), A_41), A_25) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_120])).
% 18.59/10.08  tff(c_138, plain, (![A_42, A_43]: (r1_tarski(k10_relat_1(k6_relat_1(A_42), A_43), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_131])).
% 18.59/10.08  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.59/10.08  tff(c_148, plain, (![A_42, A_43]: (k10_relat_1(k6_relat_1(A_42), A_43)=A_42 | ~r1_tarski(A_42, k10_relat_1(k6_relat_1(A_42), A_43)))), inference(resolution, [status(thm)], [c_138, c_2])).
% 18.59/10.08  tff(c_473, plain, (![A_78, B_79]: (k10_relat_1(k6_relat_1(A_78), B_79)=A_78 | ~r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_430, c_148])).
% 18.59/10.08  tff(c_20, plain, (![C_17, A_15, B_16]: (r1_tarski(k10_relat_1(C_17, A_15), k10_relat_1(C_17, B_16)) | ~r1_tarski(A_15, B_16) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 18.59/10.08  tff(c_482, plain, (![A_78, B_16, B_79]: (r1_tarski(A_78, k10_relat_1(k6_relat_1(A_78), B_16)) | ~r1_tarski(B_79, B_16) | ~v1_relat_1(k6_relat_1(A_78)) | ~r1_tarski(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_473, c_20])).
% 18.59/10.08  tff(c_1390, plain, (![A_117, B_118, B_119]: (r1_tarski(A_117, k10_relat_1(k6_relat_1(A_117), B_118)) | ~r1_tarski(B_119, B_118) | ~r1_tarski(A_117, B_119))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_482])).
% 18.59/10.08  tff(c_1443, plain, (![A_117]: (r1_tarski(A_117, k10_relat_1(k6_relat_1(A_117), k1_relat_1('#skF_2'))) | ~r1_tarski(A_117, '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_1390])).
% 18.59/10.08  tff(c_16, plain, (![B_13, A_12]: (r1_tarski(k10_relat_1(B_13, A_12), k1_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 18.59/10.08  tff(c_153, plain, (![A_46, C_47, B_48]: (r1_tarski(A_46, C_47) | ~r1_tarski(B_48, C_47) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.59/10.08  tff(c_166, plain, (![A_49]: (r1_tarski(A_49, k1_relat_1('#skF_2')) | ~r1_tarski(A_49, '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_153])).
% 18.59/10.08  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.59/10.08  tff(c_227, plain, (![A_56, A_57]: (r1_tarski(A_56, k1_relat_1('#skF_2')) | ~r1_tarski(A_56, A_57) | ~r1_tarski(A_57, '#skF_1'))), inference(resolution, [status(thm)], [c_166, c_8])).
% 18.59/10.08  tff(c_243, plain, (![B_13, A_12]: (r1_tarski(k10_relat_1(B_13, A_12), k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1(B_13), '#skF_1') | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_16, c_227])).
% 18.59/10.08  tff(c_137, plain, (![A_25, A_41]: (r1_tarski(k10_relat_1(k6_relat_1(A_25), A_41), A_25))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_131])).
% 18.59/10.08  tff(c_173, plain, (![A_50, A_51, A_52]: (r1_tarski(A_50, A_51) | ~r1_tarski(A_50, k10_relat_1(k6_relat_1(A_51), A_52)))), inference(resolution, [status(thm)], [c_137, c_153])).
% 18.59/10.08  tff(c_189, plain, (![A_51, A_52, A_41]: (r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(A_51), A_52)), A_41), A_51))), inference(resolution, [status(thm)], [c_137, c_173])).
% 18.59/10.08  tff(c_171, plain, (![A_3, A_49]: (r1_tarski(A_3, k1_relat_1('#skF_2')) | ~r1_tarski(A_3, A_49) | ~r1_tarski(A_49, '#skF_1'))), inference(resolution, [status(thm)], [c_166, c_8])).
% 18.59/10.08  tff(c_769, plain, (![A_90, B_91]: (r1_tarski(A_90, k1_relat_1('#skF_2')) | ~r1_tarski(k10_relat_1(k6_relat_1(A_90), B_91), '#skF_1') | ~r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_430, c_171])).
% 18.59/10.08  tff(c_2776, plain, (![A_153, A_154]: (r1_tarski(k10_relat_1(k6_relat_1('#skF_1'), A_153), k1_relat_1('#skF_2')) | ~r1_tarski(k10_relat_1(k6_relat_1('#skF_1'), A_153), A_154))), inference(resolution, [status(thm)], [c_189, c_769])).
% 18.59/10.08  tff(c_2812, plain, (![A_12]: (r1_tarski(k10_relat_1(k6_relat_1('#skF_1'), A_12), k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1(k6_relat_1('#skF_1')), '#skF_1') | ~v1_relat_1(k6_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_243, c_2776])).
% 18.59/10.08  tff(c_2869, plain, (![A_155]: (r1_tarski(k10_relat_1(k6_relat_1('#skF_1'), A_155), k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6, c_26, c_2812])).
% 18.59/10.08  tff(c_545, plain, (![A_78, B_16, B_79]: (r1_tarski(A_78, k10_relat_1(k6_relat_1(A_78), B_16)) | ~r1_tarski(B_79, B_16) | ~r1_tarski(A_78, B_79))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_482])).
% 18.59/10.08  tff(c_4312, plain, (![A_180, A_181]: (r1_tarski(A_180, k10_relat_1(k6_relat_1(A_180), k1_relat_1('#skF_2'))) | ~r1_tarski(A_180, k10_relat_1(k6_relat_1('#skF_1'), A_181)))), inference(resolution, [status(thm)], [c_2869, c_545])).
% 18.59/10.08  tff(c_4339, plain, (r1_tarski('#skF_1', k10_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1443, c_4312])).
% 18.59/10.08  tff(c_4400, plain, (r1_tarski('#skF_1', k10_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4339])).
% 18.59/10.08  tff(c_4473, plain, (k10_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_4400, c_148])).
% 18.59/10.08  tff(c_24, plain, (![A_22, B_24]: (k10_relat_1(A_22, k1_relat_1(B_24))=k1_relat_1(k5_relat_1(A_22, B_24)) | ~v1_relat_1(B_24) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 18.59/10.08  tff(c_4559, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4473, c_24])).
% 18.59/10.08  tff(c_4646, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40, c_4559])).
% 18.59/10.08  tff(c_4739, plain, (![A_12]: (r1_tarski(k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'), A_12), '#skF_1') | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4646, c_16])).
% 18.59/10.08  tff(c_10820, plain, (~v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_4739])).
% 18.59/10.08  tff(c_10823, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_10820])).
% 18.59/10.08  tff(c_10827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_40, c_10823])).
% 18.59/10.08  tff(c_10828, plain, (![A_12]: (r1_tarski(k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'), A_12), '#skF_1'))), inference(splitRight, [status(thm)], [c_4739])).
% 18.59/10.08  tff(c_681, plain, (![B_82, A_83]: (k9_relat_1(B_82, k2_relat_1(A_83))=k2_relat_1(k5_relat_1(A_83, B_82)) | ~v1_relat_1(B_82) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_54])).
% 18.59/10.08  tff(c_698, plain, (![A_25, B_82]: (k2_relat_1(k5_relat_1(k6_relat_1(A_25), B_82))=k9_relat_1(B_82, A_25) | ~v1_relat_1(B_82) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_681])).
% 18.59/10.08  tff(c_706, plain, (![A_25, B_82]: (k2_relat_1(k5_relat_1(k6_relat_1(A_25), B_82))=k9_relat_1(B_82, A_25) | ~v1_relat_1(B_82))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_698])).
% 18.59/10.08  tff(c_10829, plain, (v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_4739])).
% 18.59/10.08  tff(c_18, plain, (![A_14]: (k10_relat_1(A_14, k2_relat_1(A_14))=k1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.59/10.08  tff(c_34182, plain, (![A_479, B_480, A_481]: (r1_tarski(A_479, k10_relat_1(k6_relat_1(A_479), k1_relat_1(B_480))) | ~r1_tarski(A_479, k10_relat_1(B_480, A_481)) | ~v1_relat_1(B_480))), inference(resolution, [status(thm)], [c_16, c_1390])).
% 18.59/10.08  tff(c_34530, plain, (![B_482, A_483]: (r1_tarski(k10_relat_1(B_482, A_483), k10_relat_1(k6_relat_1(k10_relat_1(B_482, A_483)), k1_relat_1(B_482))) | ~v1_relat_1(B_482))), inference(resolution, [status(thm)], [c_6, c_34182])).
% 18.59/10.08  tff(c_32, plain, (![A_26]: (v1_funct_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 18.59/10.08  tff(c_457, plain, (![A_76, B_77]: (k10_relat_1(k6_relat_1(A_76), B_77)=A_76 | ~r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_430, c_148])).
% 18.59/10.08  tff(c_277, plain, (![B_61, A_62]: (r1_tarski(k9_relat_1(B_61, k10_relat_1(B_61, A_62)), A_62) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_96])).
% 18.59/10.08  tff(c_3256, plain, (![A_163, A_164, B_165]: (r1_tarski(A_163, A_164) | ~r1_tarski(A_163, k9_relat_1(B_165, k10_relat_1(B_165, A_164))) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165))), inference(resolution, [status(thm)], [c_277, c_8])).
% 18.59/10.08  tff(c_13652, plain, (![B_290, A_291, A_292]: (r1_tarski(k10_relat_1(k6_relat_1(k9_relat_1(B_290, k10_relat_1(B_290, A_291))), A_292), A_291) | ~v1_funct_1(B_290) | ~v1_relat_1(B_290))), inference(resolution, [status(thm)], [c_137, c_3256])).
% 18.59/10.08  tff(c_13816, plain, (![A_76, A_292, B_77]: (r1_tarski(k10_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_76), A_76)), A_292), B_77) | ~v1_funct_1(k6_relat_1(A_76)) | ~v1_relat_1(k6_relat_1(A_76)) | ~r1_tarski(A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_457, c_13652])).
% 18.59/10.08  tff(c_13895, plain, (![A_293, A_294, B_295]: (r1_tarski(k10_relat_1(k6_relat_1(A_293), A_294), B_295) | ~r1_tarski(A_293, B_295))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_110, c_13816])).
% 18.59/10.08  tff(c_14072, plain, (![A_293, A_294, B_295]: (k10_relat_1(k6_relat_1(A_293), A_294)=B_295 | ~r1_tarski(B_295, k10_relat_1(k6_relat_1(A_293), A_294)) | ~r1_tarski(A_293, B_295))), inference(resolution, [status(thm)], [c_13895, c_2])).
% 18.59/10.08  tff(c_34535, plain, (![B_482, A_483]: (k10_relat_1(k6_relat_1(k10_relat_1(B_482, A_483)), k1_relat_1(B_482))=k10_relat_1(B_482, A_483) | ~r1_tarski(k10_relat_1(B_482, A_483), k10_relat_1(B_482, A_483)) | ~v1_relat_1(B_482))), inference(resolution, [status(thm)], [c_34530, c_14072])).
% 18.59/10.08  tff(c_34976, plain, (![B_484, A_485]: (k10_relat_1(k6_relat_1(k10_relat_1(B_484, A_485)), k1_relat_1(B_484))=k10_relat_1(B_484, A_485) | ~v1_relat_1(B_484))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_34535])).
% 18.59/10.08  tff(c_35298, plain, (![B_484, A_485]: (k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(B_484, A_485)), B_484))=k10_relat_1(B_484, A_485) | ~v1_relat_1(B_484) | ~v1_relat_1(k6_relat_1(k10_relat_1(B_484, A_485))) | ~v1_relat_1(B_484))), inference(superposition, [status(thm), theory('equality')], [c_34976, c_24])).
% 18.59/10.08  tff(c_35713, plain, (![B_486, A_487]: (k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(B_486, A_487)), B_486))=k10_relat_1(B_486, A_487) | ~v1_relat_1(B_486))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_35298])).
% 18.59/10.08  tff(c_66646, plain, (![A_685]: (k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(A_685)), A_685))=k10_relat_1(A_685, k2_relat_1(A_685)) | ~v1_relat_1(A_685) | ~v1_relat_1(A_685))), inference(superposition, [status(thm), theory('equality')], [c_18, c_35713])).
% 18.59/10.08  tff(c_574, plain, (![A_80, B_81]: (k10_relat_1(A_80, k1_relat_1(B_81))=k1_relat_1(k5_relat_1(A_80, B_81)) | ~v1_relat_1(B_81) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_82])).
% 18.59/10.08  tff(c_427, plain, (![A_25, B_75]: (r1_tarski(A_25, k10_relat_1(k6_relat_1(A_25), B_75)) | ~r1_tarski(A_25, B_75))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_409])).
% 18.59/10.08  tff(c_585, plain, (![A_25, B_81]: (r1_tarski(A_25, k1_relat_1(k5_relat_1(k6_relat_1(A_25), B_81))) | ~r1_tarski(A_25, k1_relat_1(B_81)) | ~v1_relat_1(B_81) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_574, c_427])).
% 18.59/10.08  tff(c_657, plain, (![A_25, B_81]: (r1_tarski(A_25, k1_relat_1(k5_relat_1(k6_relat_1(A_25), B_81))) | ~r1_tarski(A_25, k1_relat_1(B_81)) | ~v1_relat_1(B_81))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_585])).
% 18.59/10.08  tff(c_66856, plain, (![A_685]: (r1_tarski(k1_relat_1(A_685), k10_relat_1(A_685, k2_relat_1(A_685))) | ~r1_tarski(k1_relat_1(A_685), k1_relat_1(A_685)) | ~v1_relat_1(A_685) | ~v1_relat_1(A_685) | ~v1_relat_1(A_685))), inference(superposition, [status(thm), theory('equality')], [c_66646, c_657])).
% 18.59/10.08  tff(c_67355, plain, (![A_688]: (r1_tarski(k1_relat_1(A_688), k10_relat_1(A_688, k2_relat_1(A_688))) | ~v1_relat_1(A_688))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_66856])).
% 18.59/10.08  tff(c_67563, plain, (r1_tarski('#skF_1', k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'), k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')))) | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4646, c_67355])).
% 18.59/10.08  tff(c_67733, plain, (r1_tarski('#skF_1', k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'), k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_10829, c_67563])).
% 18.59/10.08  tff(c_67921, plain, (r1_tarski('#skF_1', k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_706, c_67733])).
% 18.59/10.08  tff(c_67989, plain, (r1_tarski('#skF_1', k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_67921])).
% 18.59/10.08  tff(c_68420, plain, (k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~r1_tarski(k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'), k9_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(resolution, [status(thm)], [c_67989, c_2])).
% 18.59/10.08  tff(c_68489, plain, (k10_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10828, c_68420])).
% 18.59/10.08  tff(c_22, plain, (![B_19, C_21, A_18]: (k10_relat_1(k5_relat_1(B_19, C_21), A_18)=k10_relat_1(B_19, k10_relat_1(C_21, A_18)) | ~v1_relat_1(C_21) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.59/10.08  tff(c_68666, plain, (k10_relat_1(k6_relat_1('#skF_1'), k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))='#skF_1' | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68489, c_22])).
% 18.59/10.08  tff(c_68807, plain, (k10_relat_1(k6_relat_1('#skF_1'), k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40, c_68666])).
% 18.59/10.08  tff(c_2141, plain, (![A_137, A_138, A_139]: (r1_tarski(A_137, k10_relat_1(k6_relat_1(A_137), A_138)) | ~r1_tarski(A_137, k10_relat_1(k6_relat_1(A_138), A_139)))), inference(resolution, [status(thm)], [c_137, c_1390])).
% 18.59/10.08  tff(c_2210, plain, (![A_140, A_141]: (r1_tarski(k10_relat_1(k6_relat_1(A_140), A_141), k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(A_140), A_141)), A_140)))), inference(resolution, [status(thm)], [c_6, c_2141])).
% 18.59/10.08  tff(c_2287, plain, (![A_140, A_141]: (k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(A_140), A_141)), A_140)=k10_relat_1(k6_relat_1(A_140), A_141))), inference(resolution, [status(thm)], [c_2210, c_148])).
% 18.59/10.08  tff(c_6258, plain, (![C_204, B_205, A_206]: (k10_relat_1(C_204, B_205)=k10_relat_1(C_204, A_206) | ~r1_tarski(k10_relat_1(C_204, B_205), k10_relat_1(C_204, A_206)) | ~r1_tarski(A_206, B_205) | ~v1_relat_1(C_204))), inference(resolution, [status(thm)], [c_393, c_2])).
% 18.59/10.08  tff(c_13434, plain, (![C_287, B_288, A_289]: (k10_relat_1(C_287, B_288)=k10_relat_1(C_287, A_289) | ~r1_tarski(B_288, A_289) | ~r1_tarski(A_289, B_288) | ~v1_relat_1(C_287))), inference(resolution, [status(thm)], [c_20, c_6258])).
% 18.59/10.08  tff(c_13544, plain, (![C_287, A_25, B_75]: (k10_relat_1(C_287, k10_relat_1(k6_relat_1(A_25), B_75))=k10_relat_1(C_287, A_25) | ~r1_tarski(k10_relat_1(k6_relat_1(A_25), B_75), A_25) | ~v1_relat_1(C_287) | ~r1_tarski(A_25, B_75))), inference(resolution, [status(thm)], [c_427, c_13434])).
% 18.59/10.08  tff(c_21819, plain, (![C_393, A_394, B_395]: (k10_relat_1(C_393, k10_relat_1(k6_relat_1(A_394), B_395))=k10_relat_1(C_393, A_394) | ~v1_relat_1(C_393) | ~r1_tarski(A_394, B_395))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_13544])).
% 18.59/10.08  tff(c_22194, plain, (![A_140, A_394, B_395]: (k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(A_140), A_394)), A_140)=k10_relat_1(k6_relat_1(A_140), k10_relat_1(k6_relat_1(A_394), B_395)) | ~v1_relat_1(k6_relat_1(A_140)) | ~r1_tarski(A_394, B_395))), inference(superposition, [status(thm), theory('equality')], [c_21819, c_2287])).
% 18.59/10.08  tff(c_48908, plain, (![A_542, A_543, B_544]: (k10_relat_1(k6_relat_1(A_542), k10_relat_1(k6_relat_1(A_543), B_544))=k10_relat_1(k6_relat_1(A_542), A_543) | ~r1_tarski(A_543, B_544))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2287, c_22194])).
% 18.59/10.08  tff(c_34, plain, (![B_28, A_27]: (r1_tarski(k9_relat_1(B_28, k10_relat_1(B_28, A_27)), A_27) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_96])).
% 18.59/10.08  tff(c_300, plain, (![A_63, B_64, A_65]: (r1_tarski(A_63, k1_relat_1(B_64)) | ~r1_tarski(A_63, k10_relat_1(B_64, A_65)) | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_16, c_153])).
% 18.59/10.08  tff(c_323, plain, (![B_28, B_64, A_65]: (r1_tarski(k9_relat_1(B_28, k10_relat_1(B_28, k10_relat_1(B_64, A_65))), k1_relat_1(B_64)) | ~v1_relat_1(B_64) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(resolution, [status(thm)], [c_34, c_300])).
% 18.59/10.08  tff(c_49042, plain, (![A_542, A_543, B_544]: (r1_tarski(k9_relat_1(k6_relat_1(A_542), k10_relat_1(k6_relat_1(A_542), A_543)), k1_relat_1(k6_relat_1(A_543))) | ~v1_relat_1(k6_relat_1(A_543)) | ~v1_funct_1(k6_relat_1(A_542)) | ~v1_relat_1(k6_relat_1(A_542)) | ~r1_tarski(A_543, B_544))), inference(superposition, [status(thm), theory('equality')], [c_48908, c_323])).
% 18.59/10.08  tff(c_49885, plain, (![A_545, A_546, B_547]: (r1_tarski(k9_relat_1(k6_relat_1(A_545), k10_relat_1(k6_relat_1(A_545), A_546)), A_546) | ~r1_tarski(A_546, B_547))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_30, c_26, c_49042])).
% 18.59/10.08  tff(c_50251, plain, (![A_545, B_2]: (r1_tarski(k9_relat_1(k6_relat_1(A_545), k10_relat_1(k6_relat_1(A_545), B_2)), B_2))), inference(resolution, [status(thm)], [c_6, c_49885])).
% 18.59/10.08  tff(c_69151, plain, (r1_tarski(k9_relat_1(k6_relat_1('#skF_1'), '#skF_1'), k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_68807, c_50251])).
% 18.59/10.08  tff(c_69546, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_69151])).
% 18.59/10.08  tff(c_69548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_69546])).
% 18.59/10.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.59/10.08  
% 18.59/10.08  Inference rules
% 18.59/10.08  ----------------------
% 18.59/10.08  #Ref     : 0
% 18.59/10.08  #Sup     : 15867
% 18.59/10.08  #Fact    : 0
% 18.59/10.08  #Define  : 0
% 18.59/10.08  #Split   : 7
% 18.59/10.08  #Chain   : 0
% 18.59/10.08  #Close   : 0
% 18.59/10.09  
% 18.59/10.09  Ordering : KBO
% 18.59/10.09  
% 18.59/10.09  Simplification rules
% 18.59/10.09  ----------------------
% 18.59/10.09  #Subsume      : 5085
% 18.59/10.09  #Demod        : 14307
% 18.59/10.09  #Tautology    : 3618
% 18.59/10.09  #SimpNegUnit  : 1
% 18.59/10.09  #BackRed      : 4
% 18.59/10.09  
% 18.59/10.09  #Partial instantiations: 0
% 18.59/10.09  #Strategies tried      : 1
% 18.59/10.09  
% 18.59/10.09  Timing (in seconds)
% 18.59/10.09  ----------------------
% 18.59/10.09  Preprocessing        : 0.51
% 18.59/10.09  Parsing              : 0.27
% 18.59/10.09  CNF conversion       : 0.03
% 18.59/10.09  Main loop            : 8.72
% 18.59/10.09  Inferencing          : 1.44
% 18.59/10.09  Reduction            : 3.29
% 18.59/10.09  Demodulation         : 2.71
% 18.59/10.09  BG Simplification    : 0.18
% 18.59/10.09  Subsumption          : 3.36
% 18.59/10.09  Abstraction          : 0.33
% 18.59/10.09  MUC search           : 0.00
% 18.59/10.09  Cooper               : 0.00
% 18.59/10.09  Total                : 9.28
% 18.59/10.09  Index Insertion      : 0.00
% 18.59/10.09  Index Deletion       : 0.00
% 18.59/10.09  Index Matching       : 0.00
% 18.59/10.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
