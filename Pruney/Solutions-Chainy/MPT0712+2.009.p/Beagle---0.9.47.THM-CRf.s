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
% DateTime   : Thu Dec  3 10:05:32 EST 2020

% Result     : Theorem 9.66s
% Output     : CNFRefutation 9.72s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 318 expanded)
%              Number of leaves         :   36 ( 119 expanded)
%              Depth                    :   18
%              Number of atoms          :  198 ( 722 expanded)
%              Number of equality atoms :   48 ( 155 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(k1_tarski(A_14),B_15)
      | r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_132,plain,(
    ! [B_57,A_58] :
      ( v4_relat_1(B_57,A_58)
      | ~ r1_tarski(k1_relat_1(B_57),A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_141,plain,(
    ! [B_57] :
      ( v4_relat_1(B_57,k1_relat_1(B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k7_relat_1(A_18,B_19))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_282,plain,(
    ! [C_87,A_88,B_89] :
      ( k7_relat_1(k7_relat_1(C_87,A_88),B_89) = k1_xboole_0
      | ~ r1_xboole_0(A_88,B_89)
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_304,plain,(
    ! [C_87,A_88,B_89] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1(C_87,A_88))
      | ~ r1_xboole_0(A_88,B_89)
      | ~ v1_relat_1(C_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_24])).

tff(c_349,plain,(
    ! [C_97,A_98,B_99] :
      ( ~ v1_relat_1(k7_relat_1(C_97,A_98))
      | ~ r1_xboole_0(A_98,B_99)
      | ~ v1_relat_1(C_97) ) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_356,plain,(
    ! [B_19,B_99,A_18] :
      ( ~ r1_xboole_0(B_19,B_99)
      | ~ v1_relat_1(A_18) ) ),
    inference(resolution,[status(thm)],[c_24,c_349])).

tff(c_357,plain,(
    ! [A_18] : ~ v1_relat_1(A_18) ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_52])).

tff(c_361,plain,(
    ! [B_19,B_99] : ~ r1_xboole_0(B_19,B_99) ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_364,plain,(
    ! [A_14,B_15] : r2_hidden(A_14,B_15) ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_18])).

tff(c_46,plain,(
    ! [C_36,A_34,B_35] :
      ( k2_tarski(k1_funct_1(C_36,A_34),k1_funct_1(C_36,B_35)) = k9_relat_1(C_36,k2_tarski(A_34,B_35))
      | ~ r2_hidden(B_35,k1_relat_1(C_36))
      | ~ r2_hidden(A_34,k1_relat_1(C_36))
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_429,plain,(
    ! [C_114,A_115,B_116] :
      ( k2_tarski(k1_funct_1(C_114,A_115),k1_funct_1(C_114,B_116)) = k9_relat_1(C_114,k2_tarski(A_115,B_116))
      | ~ v1_funct_1(C_114)
      | ~ v1_relat_1(C_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_364,c_46])).

tff(c_443,plain,(
    ! [C_114,A_115] :
      ( k9_relat_1(C_114,k2_tarski(A_115,A_115)) = k1_tarski(k1_funct_1(C_114,A_115))
      | ~ v1_funct_1(C_114)
      | ~ v1_relat_1(C_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_429])).

tff(c_517,plain,(
    ! [C_125,A_126] :
      ( k9_relat_1(C_125,k1_tarski(A_126)) = k1_tarski(k1_funct_1(C_125,A_126))
      | ~ v1_funct_1(C_125)
      | ~ v1_relat_1(C_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_443])).

tff(c_99,plain,(
    ! [B_49,A_50] :
      ( k2_relat_1(k7_relat_1(B_49,A_50)) = k9_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_105,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_48])).

tff(c_111,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_105])).

tff(c_525,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_111])).

tff(c_532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_6,c_525])).

tff(c_533,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_143,plain,(
    ! [B_60,A_61] :
      ( k7_relat_1(B_60,A_61) = B_60
      | ~ r1_tarski(k1_relat_1(B_60),A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_152,plain,(
    ! [B_60] :
      ( k7_relat_1(B_60,k1_relat_1(B_60)) = B_60
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_143])).

tff(c_42,plain,(
    ! [B_31,A_30] :
      ( r1_xboole_0(k1_relat_1(B_31),A_30)
      | k7_relat_1(B_31,A_30) != k1_xboole_0
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_184,plain,(
    ! [B_71,A_72] :
      ( k9_relat_1(B_71,A_72) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_71),A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_192,plain,(
    ! [B_31,A_30] :
      ( k9_relat_1(B_31,A_30) = k1_xboole_0
      | k7_relat_1(B_31,A_30) != k1_xboole_0
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_42,c_184])).

tff(c_537,plain,(
    ! [A_127] :
      ( k9_relat_1(k1_xboole_0,A_127) = k1_xboole_0
      | k7_relat_1(k1_xboole_0,A_127) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_533,c_192])).

tff(c_154,plain,(
    ! [B_64] :
      ( k7_relat_1(B_64,k1_relat_1(B_64)) = B_64
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_143])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( k2_relat_1(k7_relat_1(B_24,A_23)) = k9_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_160,plain,(
    ! [B_64] :
      ( k9_relat_1(B_64,k1_relat_1(B_64)) = k2_relat_1(B_64)
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_32])).

tff(c_544,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_160])).

tff(c_556,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_533,c_544])).

tff(c_580,plain,(
    k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_556])).

tff(c_583,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_580])).

tff(c_587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_583])).

tff(c_588,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_556])).

tff(c_301,plain,(
    ! [C_87,A_88,B_89] :
      ( k9_relat_1(k7_relat_1(C_87,A_88),B_89) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1(C_87,A_88))
      | ~ r1_xboole_0(A_88,B_89)
      | ~ v1_relat_1(C_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_32])).

tff(c_2991,plain,(
    ! [C_286,A_287,B_288] :
      ( k9_relat_1(k7_relat_1(C_286,A_287),B_288) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(C_286,A_287))
      | ~ r1_xboole_0(A_287,B_288)
      | ~ v1_relat_1(C_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_301])).

tff(c_3004,plain,(
    ! [A_18,B_19,B_288] :
      ( k9_relat_1(k7_relat_1(A_18,B_19),B_288) = k1_xboole_0
      | ~ r1_xboole_0(B_19,B_288)
      | ~ v1_relat_1(A_18) ) ),
    inference(resolution,[status(thm)],[c_24,c_2991])).

tff(c_193,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(k7_relat_1(C_73,A_74),B_75)
      | ~ v4_relat_1(C_73,B_75)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_151,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(resolution,[status(thm)],[c_22,c_143])).

tff(c_4348,plain,(
    ! [C_336,A_337,B_338] :
      ( k7_relat_1(k7_relat_1(C_336,A_337),B_338) = k7_relat_1(C_336,A_337)
      | ~ v1_relat_1(k7_relat_1(C_336,A_337))
      | ~ v4_relat_1(C_336,B_338)
      | ~ v1_relat_1(C_336) ) ),
    inference(resolution,[status(thm)],[c_193,c_151])).

tff(c_4384,plain,(
    ! [A_339,B_340,B_341] :
      ( k7_relat_1(k7_relat_1(A_339,B_340),B_341) = k7_relat_1(A_339,B_340)
      | ~ v4_relat_1(A_339,B_341)
      | ~ v1_relat_1(A_339) ) ),
    inference(resolution,[status(thm)],[c_24,c_4348])).

tff(c_19403,plain,(
    ! [A_535,B_536,B_537] :
      ( k9_relat_1(k7_relat_1(A_535,B_536),B_537) = k2_relat_1(k7_relat_1(A_535,B_536))
      | ~ v1_relat_1(k7_relat_1(A_535,B_536))
      | ~ v4_relat_1(A_535,B_537)
      | ~ v1_relat_1(A_535) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4384,c_32])).

tff(c_19504,plain,(
    ! [A_538,B_539,B_540] :
      ( k9_relat_1(k7_relat_1(A_538,B_539),B_540) = k2_relat_1(k7_relat_1(A_538,B_539))
      | ~ v4_relat_1(A_538,B_540)
      | ~ v1_relat_1(A_538) ) ),
    inference(resolution,[status(thm)],[c_24,c_19403])).

tff(c_22686,plain,(
    ! [A_566,B_567,B_568] :
      ( k2_relat_1(k7_relat_1(A_566,B_567)) = k1_xboole_0
      | ~ v4_relat_1(A_566,B_568)
      | ~ v1_relat_1(A_566)
      | ~ r1_xboole_0(B_567,B_568)
      | ~ v1_relat_1(A_566) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3004,c_19504])).

tff(c_22713,plain,(
    ! [B_569,B_570] :
      ( k2_relat_1(k7_relat_1(B_569,B_570)) = k1_xboole_0
      | ~ r1_xboole_0(B_570,k1_relat_1(B_569))
      | ~ v1_relat_1(B_569) ) ),
    inference(resolution,[status(thm)],[c_141,c_22686])).

tff(c_22748,plain,(
    ! [B_571,A_572] :
      ( k2_relat_1(k7_relat_1(B_571,k1_tarski(A_572))) = k1_xboole_0
      | ~ v1_relat_1(B_571)
      | r2_hidden(A_572,k1_relat_1(B_571)) ) ),
    inference(resolution,[status(thm)],[c_18,c_22713])).

tff(c_22773,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22748,c_48])).

tff(c_22853,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8,c_22773])).

tff(c_329,plain,(
    ! [C_94,A_95,B_96] :
      ( k2_tarski(k1_funct_1(C_94,A_95),k1_funct_1(C_94,B_96)) = k9_relat_1(C_94,k2_tarski(A_95,B_96))
      | ~ r2_hidden(B_96,k1_relat_1(C_94))
      | ~ r2_hidden(A_95,k1_relat_1(C_94))
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_336,plain,(
    ! [C_94,B_96] :
      ( k9_relat_1(C_94,k2_tarski(B_96,B_96)) = k1_tarski(k1_funct_1(C_94,B_96))
      | ~ r2_hidden(B_96,k1_relat_1(C_94))
      | ~ r2_hidden(B_96,k1_relat_1(C_94))
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_10])).

tff(c_345,plain,(
    ! [C_94,B_96] :
      ( k9_relat_1(C_94,k1_tarski(B_96)) = k1_tarski(k1_funct_1(C_94,B_96))
      | ~ r2_hidden(B_96,k1_relat_1(C_94))
      | ~ r2_hidden(B_96,k1_relat_1(C_94))
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_336])).

tff(c_22868,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_2','#skF_1'))
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22853,c_345])).

tff(c_22871,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_22853,c_22868])).

tff(c_22872,plain,(
    ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22871,c_111])).

tff(c_22875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22872])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.66/3.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.72/3.67  
% 9.72/3.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.72/3.67  %$ v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.72/3.67  
% 9.72/3.67  %Foreground sorts:
% 9.72/3.67  
% 9.72/3.67  
% 9.72/3.67  %Background operators:
% 9.72/3.67  
% 9.72/3.67  
% 9.72/3.67  %Foreground operators:
% 9.72/3.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.72/3.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.72/3.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.72/3.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.72/3.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.72/3.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.72/3.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.72/3.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.72/3.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.72/3.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.72/3.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.72/3.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.72/3.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.72/3.67  tff('#skF_2', type, '#skF_2': $i).
% 9.72/3.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.72/3.67  tff('#skF_1', type, '#skF_1': $i).
% 9.72/3.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.72/3.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.72/3.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.72/3.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.72/3.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.72/3.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.72/3.67  
% 9.72/3.69  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.72/3.69  tff(f_111, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 9.72/3.69  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.72/3.69  tff(f_46, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.72/3.69  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.72/3.69  tff(f_56, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.72/3.69  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.72/3.69  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 9.72/3.69  tff(f_104, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 9.72/3.69  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 9.72/3.69  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 9.72/3.69  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 9.72/3.69  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 9.72/3.69  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 9.72/3.69  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.72/3.69  tff(c_52, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.72/3.69  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.72/3.69  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.72/3.69  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(k1_tarski(A_14), B_15) | r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.72/3.69  tff(c_132, plain, (![B_57, A_58]: (v4_relat_1(B_57, A_58) | ~r1_tarski(k1_relat_1(B_57), A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.72/3.69  tff(c_141, plain, (![B_57]: (v4_relat_1(B_57, k1_relat_1(B_57)) | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_6, c_132])).
% 9.72/3.69  tff(c_24, plain, (![A_18, B_19]: (v1_relat_1(k7_relat_1(A_18, B_19)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.72/3.69  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.72/3.69  tff(c_282, plain, (![C_87, A_88, B_89]: (k7_relat_1(k7_relat_1(C_87, A_88), B_89)=k1_xboole_0 | ~r1_xboole_0(A_88, B_89) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.72/3.69  tff(c_304, plain, (![C_87, A_88, B_89]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(k7_relat_1(C_87, A_88)) | ~r1_xboole_0(A_88, B_89) | ~v1_relat_1(C_87))), inference(superposition, [status(thm), theory('equality')], [c_282, c_24])).
% 9.72/3.69  tff(c_349, plain, (![C_97, A_98, B_99]: (~v1_relat_1(k7_relat_1(C_97, A_98)) | ~r1_xboole_0(A_98, B_99) | ~v1_relat_1(C_97))), inference(splitLeft, [status(thm)], [c_304])).
% 9.72/3.69  tff(c_356, plain, (![B_19, B_99, A_18]: (~r1_xboole_0(B_19, B_99) | ~v1_relat_1(A_18))), inference(resolution, [status(thm)], [c_24, c_349])).
% 9.72/3.69  tff(c_357, plain, (![A_18]: (~v1_relat_1(A_18))), inference(splitLeft, [status(thm)], [c_356])).
% 9.72/3.69  tff(c_360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_357, c_52])).
% 9.72/3.69  tff(c_361, plain, (![B_19, B_99]: (~r1_xboole_0(B_19, B_99))), inference(splitRight, [status(thm)], [c_356])).
% 9.72/3.69  tff(c_364, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15))), inference(negUnitSimplification, [status(thm)], [c_361, c_18])).
% 9.72/3.69  tff(c_46, plain, (![C_36, A_34, B_35]: (k2_tarski(k1_funct_1(C_36, A_34), k1_funct_1(C_36, B_35))=k9_relat_1(C_36, k2_tarski(A_34, B_35)) | ~r2_hidden(B_35, k1_relat_1(C_36)) | ~r2_hidden(A_34, k1_relat_1(C_36)) | ~v1_funct_1(C_36) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.72/3.69  tff(c_429, plain, (![C_114, A_115, B_116]: (k2_tarski(k1_funct_1(C_114, A_115), k1_funct_1(C_114, B_116))=k9_relat_1(C_114, k2_tarski(A_115, B_116)) | ~v1_funct_1(C_114) | ~v1_relat_1(C_114))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_364, c_46])).
% 9.72/3.69  tff(c_443, plain, (![C_114, A_115]: (k9_relat_1(C_114, k2_tarski(A_115, A_115))=k1_tarski(k1_funct_1(C_114, A_115)) | ~v1_funct_1(C_114) | ~v1_relat_1(C_114))), inference(superposition, [status(thm), theory('equality')], [c_10, c_429])).
% 9.72/3.69  tff(c_517, plain, (![C_125, A_126]: (k9_relat_1(C_125, k1_tarski(A_126))=k1_tarski(k1_funct_1(C_125, A_126)) | ~v1_funct_1(C_125) | ~v1_relat_1(C_125))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_443])).
% 9.72/3.69  tff(c_99, plain, (![B_49, A_50]: (k2_relat_1(k7_relat_1(B_49, A_50))=k9_relat_1(B_49, A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.72/3.69  tff(c_48, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.72/3.69  tff(c_105, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_99, c_48])).
% 9.72/3.69  tff(c_111, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_105])).
% 9.72/3.69  tff(c_525, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_517, c_111])).
% 9.72/3.69  tff(c_532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_6, c_525])).
% 9.72/3.69  tff(c_533, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_304])).
% 9.72/3.69  tff(c_143, plain, (![B_60, A_61]: (k7_relat_1(B_60, A_61)=B_60 | ~r1_tarski(k1_relat_1(B_60), A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.72/3.69  tff(c_152, plain, (![B_60]: (k7_relat_1(B_60, k1_relat_1(B_60))=B_60 | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_6, c_143])).
% 9.72/3.69  tff(c_42, plain, (![B_31, A_30]: (r1_xboole_0(k1_relat_1(B_31), A_30) | k7_relat_1(B_31, A_30)!=k1_xboole_0 | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.72/3.69  tff(c_184, plain, (![B_71, A_72]: (k9_relat_1(B_71, A_72)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_71), A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.72/3.69  tff(c_192, plain, (![B_31, A_30]: (k9_relat_1(B_31, A_30)=k1_xboole_0 | k7_relat_1(B_31, A_30)!=k1_xboole_0 | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_42, c_184])).
% 9.72/3.69  tff(c_537, plain, (![A_127]: (k9_relat_1(k1_xboole_0, A_127)=k1_xboole_0 | k7_relat_1(k1_xboole_0, A_127)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_533, c_192])).
% 9.72/3.69  tff(c_154, plain, (![B_64]: (k7_relat_1(B_64, k1_relat_1(B_64))=B_64 | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_6, c_143])).
% 9.72/3.69  tff(c_32, plain, (![B_24, A_23]: (k2_relat_1(k7_relat_1(B_24, A_23))=k9_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.72/3.69  tff(c_160, plain, (![B_64]: (k9_relat_1(B_64, k1_relat_1(B_64))=k2_relat_1(B_64) | ~v1_relat_1(B_64) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_154, c_32])).
% 9.72/3.69  tff(c_544, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k7_relat_1(k1_xboole_0, k1_relat_1(k1_xboole_0))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_537, c_160])).
% 9.72/3.69  tff(c_556, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, k1_relat_1(k1_xboole_0))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_533, c_533, c_544])).
% 9.72/3.69  tff(c_580, plain, (k7_relat_1(k1_xboole_0, k1_relat_1(k1_xboole_0))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_556])).
% 9.72/3.69  tff(c_583, plain, (~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_580])).
% 9.72/3.69  tff(c_587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_533, c_583])).
% 9.72/3.69  tff(c_588, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_556])).
% 9.72/3.69  tff(c_301, plain, (![C_87, A_88, B_89]: (k9_relat_1(k7_relat_1(C_87, A_88), B_89)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k7_relat_1(C_87, A_88)) | ~r1_xboole_0(A_88, B_89) | ~v1_relat_1(C_87))), inference(superposition, [status(thm), theory('equality')], [c_282, c_32])).
% 9.72/3.69  tff(c_2991, plain, (![C_286, A_287, B_288]: (k9_relat_1(k7_relat_1(C_286, A_287), B_288)=k1_xboole_0 | ~v1_relat_1(k7_relat_1(C_286, A_287)) | ~r1_xboole_0(A_287, B_288) | ~v1_relat_1(C_286))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_301])).
% 9.72/3.69  tff(c_3004, plain, (![A_18, B_19, B_288]: (k9_relat_1(k7_relat_1(A_18, B_19), B_288)=k1_xboole_0 | ~r1_xboole_0(B_19, B_288) | ~v1_relat_1(A_18))), inference(resolution, [status(thm)], [c_24, c_2991])).
% 9.72/3.69  tff(c_193, plain, (![C_73, A_74, B_75]: (v4_relat_1(k7_relat_1(C_73, A_74), B_75) | ~v4_relat_1(C_73, B_75) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.72/3.69  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.72/3.69  tff(c_151, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(resolution, [status(thm)], [c_22, c_143])).
% 9.72/3.69  tff(c_4348, plain, (![C_336, A_337, B_338]: (k7_relat_1(k7_relat_1(C_336, A_337), B_338)=k7_relat_1(C_336, A_337) | ~v1_relat_1(k7_relat_1(C_336, A_337)) | ~v4_relat_1(C_336, B_338) | ~v1_relat_1(C_336))), inference(resolution, [status(thm)], [c_193, c_151])).
% 9.72/3.69  tff(c_4384, plain, (![A_339, B_340, B_341]: (k7_relat_1(k7_relat_1(A_339, B_340), B_341)=k7_relat_1(A_339, B_340) | ~v4_relat_1(A_339, B_341) | ~v1_relat_1(A_339))), inference(resolution, [status(thm)], [c_24, c_4348])).
% 9.72/3.69  tff(c_19403, plain, (![A_535, B_536, B_537]: (k9_relat_1(k7_relat_1(A_535, B_536), B_537)=k2_relat_1(k7_relat_1(A_535, B_536)) | ~v1_relat_1(k7_relat_1(A_535, B_536)) | ~v4_relat_1(A_535, B_537) | ~v1_relat_1(A_535))), inference(superposition, [status(thm), theory('equality')], [c_4384, c_32])).
% 9.72/3.69  tff(c_19504, plain, (![A_538, B_539, B_540]: (k9_relat_1(k7_relat_1(A_538, B_539), B_540)=k2_relat_1(k7_relat_1(A_538, B_539)) | ~v4_relat_1(A_538, B_540) | ~v1_relat_1(A_538))), inference(resolution, [status(thm)], [c_24, c_19403])).
% 9.72/3.69  tff(c_22686, plain, (![A_566, B_567, B_568]: (k2_relat_1(k7_relat_1(A_566, B_567))=k1_xboole_0 | ~v4_relat_1(A_566, B_568) | ~v1_relat_1(A_566) | ~r1_xboole_0(B_567, B_568) | ~v1_relat_1(A_566))), inference(superposition, [status(thm), theory('equality')], [c_3004, c_19504])).
% 9.72/3.69  tff(c_22713, plain, (![B_569, B_570]: (k2_relat_1(k7_relat_1(B_569, B_570))=k1_xboole_0 | ~r1_xboole_0(B_570, k1_relat_1(B_569)) | ~v1_relat_1(B_569))), inference(resolution, [status(thm)], [c_141, c_22686])).
% 9.72/3.69  tff(c_22748, plain, (![B_571, A_572]: (k2_relat_1(k7_relat_1(B_571, k1_tarski(A_572)))=k1_xboole_0 | ~v1_relat_1(B_571) | r2_hidden(A_572, k1_relat_1(B_571)))), inference(resolution, [status(thm)], [c_18, c_22713])).
% 9.72/3.69  tff(c_22773, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2') | r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_22748, c_48])).
% 9.72/3.69  tff(c_22853, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8, c_22773])).
% 9.72/3.69  tff(c_329, plain, (![C_94, A_95, B_96]: (k2_tarski(k1_funct_1(C_94, A_95), k1_funct_1(C_94, B_96))=k9_relat_1(C_94, k2_tarski(A_95, B_96)) | ~r2_hidden(B_96, k1_relat_1(C_94)) | ~r2_hidden(A_95, k1_relat_1(C_94)) | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.72/3.69  tff(c_336, plain, (![C_94, B_96]: (k9_relat_1(C_94, k2_tarski(B_96, B_96))=k1_tarski(k1_funct_1(C_94, B_96)) | ~r2_hidden(B_96, k1_relat_1(C_94)) | ~r2_hidden(B_96, k1_relat_1(C_94)) | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(superposition, [status(thm), theory('equality')], [c_329, c_10])).
% 9.72/3.69  tff(c_345, plain, (![C_94, B_96]: (k9_relat_1(C_94, k1_tarski(B_96))=k1_tarski(k1_funct_1(C_94, B_96)) | ~r2_hidden(B_96, k1_relat_1(C_94)) | ~r2_hidden(B_96, k1_relat_1(C_94)) | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_336])).
% 9.72/3.69  tff(c_22868, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_2', '#skF_1')) | ~r2_hidden('#skF_1', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22853, c_345])).
% 9.72/3.69  tff(c_22871, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_22853, c_22868])).
% 9.72/3.69  tff(c_22872, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22871, c_111])).
% 9.72/3.69  tff(c_22875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_22872])).
% 9.72/3.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.72/3.69  
% 9.72/3.69  Inference rules
% 9.72/3.69  ----------------------
% 9.72/3.69  #Ref     : 0
% 9.72/3.69  #Sup     : 5028
% 9.72/3.69  #Fact    : 2
% 9.72/3.69  #Define  : 0
% 9.72/3.69  #Split   : 16
% 9.72/3.69  #Chain   : 0
% 9.72/3.69  #Close   : 0
% 9.72/3.69  
% 9.72/3.69  Ordering : KBO
% 9.72/3.69  
% 9.72/3.69  Simplification rules
% 9.72/3.69  ----------------------
% 9.72/3.69  #Subsume      : 2416
% 9.72/3.69  #Demod        : 4451
% 9.72/3.69  #Tautology    : 1952
% 9.72/3.69  #SimpNegUnit  : 215
% 9.72/3.69  #BackRed      : 36
% 9.72/3.69  
% 9.72/3.69  #Partial instantiations: 0
% 9.72/3.69  #Strategies tried      : 1
% 9.72/3.69  
% 9.72/3.69  Timing (in seconds)
% 9.72/3.69  ----------------------
% 9.72/3.69  Preprocessing        : 0.30
% 9.72/3.69  Parsing              : 0.16
% 9.72/3.69  CNF conversion       : 0.02
% 9.72/3.69  Main loop            : 2.55
% 9.72/3.69  Inferencing          : 0.73
% 9.72/3.69  Reduction            : 0.85
% 9.72/3.69  Demodulation         : 0.60
% 9.72/3.69  BG Simplification    : 0.09
% 9.72/3.69  Subsumption          : 0.75
% 9.72/3.69  Abstraction          : 0.12
% 9.72/3.69  MUC search           : 0.00
% 9.72/3.69  Cooper               : 0.00
% 9.72/3.70  Total                : 2.90
% 9.72/3.70  Index Insertion      : 0.00
% 9.72/3.70  Index Deletion       : 0.00
% 9.72/3.70  Index Matching       : 0.00
% 9.72/3.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
