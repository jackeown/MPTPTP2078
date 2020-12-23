%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:15 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 154 expanded)
%              Number of leaves         :   38 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  158 ( 281 expanded)
%              Number of equality atoms :   43 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_101,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_40,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_56,plain,
    ( k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_100,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_58,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_209,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_105,B_106)),k1_relat_1(A_105))
      | ~ v1_relat_1(B_106)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_214,plain,(
    ! [B_106] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_106)),k1_xboole_0)
      | ~ v1_relat_1(B_106)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_209])).

tff(c_216,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_2'(A_41),A_41)
      | v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_172,plain,(
    ! [C_95,B_96,A_97] :
      ( r2_hidden(C_95,B_96)
      | ~ r2_hidden(C_95,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    ! [A_41,B_96] :
      ( r2_hidden('#skF_2'(A_41),B_96)
      | ~ r1_tarski(A_41,B_96)
      | v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_42,c_172])).

tff(c_249,plain,(
    ! [A_120,B_121] :
      ( k4_tarski('#skF_3'(A_120,B_121),'#skF_4'(A_120,B_121)) = B_121
      | ~ r2_hidden(B_121,A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [C_54,D_55,A_41] :
      ( k4_tarski(C_54,D_55) != '#skF_2'(A_41)
      | v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_253,plain,(
    ! [B_121,A_41,A_120] :
      ( B_121 != '#skF_2'(A_41)
      | v1_relat_1(A_41)
      | ~ r2_hidden(B_121,A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_40])).

tff(c_264,plain,(
    ! [A_125,A_126] :
      ( v1_relat_1(A_125)
      | ~ r2_hidden('#skF_2'(A_125),A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_253])).

tff(c_286,plain,(
    ! [B_129,A_130] :
      ( ~ v1_relat_1(B_129)
      | ~ r1_tarski(A_130,B_129)
      | v1_relat_1(A_130) ) ),
    inference(resolution,[status(thm)],[c_178,c_264])).

tff(c_295,plain,(
    ! [A_9] :
      ( ~ v1_relat_1(A_9)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_286])).

tff(c_300,plain,(
    ! [A_9] : ~ v1_relat_1(A_9) ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_295])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_58])).

tff(c_313,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_44,plain,(
    ! [A_59,B_60] :
      ( v1_relat_1(k5_relat_1(A_59,B_60))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    ! [B_38] : k2_zfmisc_1(k1_xboole_0,B_38) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_323,plain,(
    ! [B_136] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_136)),k1_xboole_0)
      | ~ v1_relat_1(B_136) ) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_133,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_142,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_133])).

tff(c_333,plain,(
    ! [B_137] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_137)) = k1_xboole_0
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_323,c_142])).

tff(c_46,plain,(
    ! [A_61] :
      ( k3_xboole_0(A_61,k2_zfmisc_1(k1_relat_1(A_61),k2_relat_1(A_61))) = A_61
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_348,plain,(
    ! [B_137] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_137),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_137)))) = k5_relat_1(k1_xboole_0,B_137)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_137))
      | ~ v1_relat_1(B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_46])).

tff(c_358,plain,(
    ! [B_138] :
      ( k5_relat_1(k1_xboole_0,B_138) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_138))
      | ~ v1_relat_1(B_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_34,c_348])).

tff(c_362,plain,(
    ! [B_60] :
      ( k5_relat_1(k1_xboole_0,B_60) = k1_xboole_0
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_44,c_358])).

tff(c_366,plain,(
    ! [B_139] :
      ( k5_relat_1(k1_xboole_0,B_139) = k1_xboole_0
      | ~ v1_relat_1(B_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_362])).

tff(c_375,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_366])).

tff(c_381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_375])).

tff(c_382,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_501,plain,(
    ! [A_171,B_172] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_171,B_172)),k1_relat_1(A_171))
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_509,plain,(
    ! [B_172] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_172)),k1_xboole_0)
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_501])).

tff(c_513,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_455,plain,(
    ! [C_158,B_159,A_160] :
      ( r2_hidden(C_158,B_159)
      | ~ r2_hidden(C_158,A_160)
      | ~ r1_tarski(A_160,B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_461,plain,(
    ! [A_41,B_159] :
      ( r2_hidden('#skF_2'(A_41),B_159)
      | ~ r1_tarski(A_41,B_159)
      | v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_42,c_455])).

tff(c_546,plain,(
    ! [A_186,B_187] :
      ( k4_tarski('#skF_3'(A_186,B_187),'#skF_4'(A_186,B_187)) = B_187
      | ~ r2_hidden(B_187,A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_550,plain,(
    ! [B_187,A_41,A_186] :
      ( B_187 != '#skF_2'(A_41)
      | v1_relat_1(A_41)
      | ~ r2_hidden(B_187,A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_40])).

tff(c_570,plain,(
    ! [A_193,A_194] :
      ( v1_relat_1(A_193)
      | ~ r2_hidden('#skF_2'(A_193),A_194)
      | ~ v1_relat_1(A_194) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_550])).

tff(c_583,plain,(
    ! [B_195,A_196] :
      ( ~ v1_relat_1(B_195)
      | ~ r1_tarski(A_196,B_195)
      | v1_relat_1(A_196) ) ),
    inference(resolution,[status(thm)],[c_461,c_570])).

tff(c_592,plain,(
    ! [A_9] :
      ( ~ v1_relat_1(A_9)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_583])).

tff(c_597,plain,(
    ! [A_9] : ~ v1_relat_1(A_9) ),
    inference(negUnitSimplification,[status(thm)],[c_513,c_592])).

tff(c_608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_597,c_58])).

tff(c_610,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_509])).

tff(c_32,plain,(
    ! [A_37] : k2_zfmisc_1(A_37,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_732,plain,(
    ! [B_215,A_216] :
      ( k2_relat_1(k5_relat_1(B_215,A_216)) = k2_relat_1(A_216)
      | ~ r1_tarski(k1_relat_1(A_216),k2_relat_1(B_215))
      | ~ v1_relat_1(B_215)
      | ~ v1_relat_1(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_738,plain,(
    ! [B_215] :
      ( k2_relat_1(k5_relat_1(B_215,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_215))
      | ~ v1_relat_1(B_215)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_732])).

tff(c_795,plain,(
    ! [B_218] :
      ( k2_relat_1(k5_relat_1(B_218,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_16,c_52,c_738])).

tff(c_804,plain,(
    ! [B_218] :
      ( k3_xboole_0(k5_relat_1(B_218,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_218,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_218,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_218,k1_xboole_0))
      | ~ v1_relat_1(B_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_46])).

tff(c_878,plain,(
    ! [B_226] :
      ( k5_relat_1(B_226,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_226,k1_xboole_0))
      | ~ v1_relat_1(B_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_32,c_804])).

tff(c_885,plain,(
    ! [A_59] :
      ( k5_relat_1(A_59,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_59) ) ),
    inference(resolution,[status(thm)],[c_44,c_878])).

tff(c_891,plain,(
    ! [A_227] :
      ( k5_relat_1(A_227,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_885])).

tff(c_903,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_891])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_903])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.45  
% 3.00/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.46  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 3.00/1.46  
% 3.00/1.46  %Foreground sorts:
% 3.00/1.46  
% 3.00/1.46  
% 3.00/1.46  %Background operators:
% 3.00/1.46  
% 3.00/1.46  
% 3.00/1.46  %Foreground operators:
% 3.00/1.46  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.00/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.00/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.00/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.00/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.00/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.00/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.00/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.00/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.00/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.00/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.00/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.00/1.46  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.00/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.00/1.46  
% 3.08/1.47  tff(f_108, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.08/1.47  tff(f_101, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.08/1.47  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.08/1.47  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.08/1.47  tff(f_72, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.08/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.08/1.47  tff(f_78, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.08/1.47  tff(f_40, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.08/1.47  tff(f_60, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.08/1.47  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.08/1.47  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.08/1.47  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.08/1.47  tff(c_56, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.08/1.47  tff(c_100, plain, (k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 3.08/1.47  tff(c_58, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.08/1.47  tff(c_54, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.08/1.47  tff(c_209, plain, (![A_105, B_106]: (r1_tarski(k1_relat_1(k5_relat_1(A_105, B_106)), k1_relat_1(A_105)) | ~v1_relat_1(B_106) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.08/1.47  tff(c_214, plain, (![B_106]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_106)), k1_xboole_0) | ~v1_relat_1(B_106) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_209])).
% 3.08/1.47  tff(c_216, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_214])).
% 3.08/1.47  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.08/1.47  tff(c_42, plain, (![A_41]: (r2_hidden('#skF_2'(A_41), A_41) | v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.08/1.47  tff(c_172, plain, (![C_95, B_96, A_97]: (r2_hidden(C_95, B_96) | ~r2_hidden(C_95, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.08/1.47  tff(c_178, plain, (![A_41, B_96]: (r2_hidden('#skF_2'(A_41), B_96) | ~r1_tarski(A_41, B_96) | v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_42, c_172])).
% 3.08/1.47  tff(c_249, plain, (![A_120, B_121]: (k4_tarski('#skF_3'(A_120, B_121), '#skF_4'(A_120, B_121))=B_121 | ~r2_hidden(B_121, A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.08/1.47  tff(c_40, plain, (![C_54, D_55, A_41]: (k4_tarski(C_54, D_55)!='#skF_2'(A_41) | v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.08/1.47  tff(c_253, plain, (![B_121, A_41, A_120]: (B_121!='#skF_2'(A_41) | v1_relat_1(A_41) | ~r2_hidden(B_121, A_120) | ~v1_relat_1(A_120))), inference(superposition, [status(thm), theory('equality')], [c_249, c_40])).
% 3.08/1.47  tff(c_264, plain, (![A_125, A_126]: (v1_relat_1(A_125) | ~r2_hidden('#skF_2'(A_125), A_126) | ~v1_relat_1(A_126))), inference(reflexivity, [status(thm), theory('equality')], [c_253])).
% 3.08/1.47  tff(c_286, plain, (![B_129, A_130]: (~v1_relat_1(B_129) | ~r1_tarski(A_130, B_129) | v1_relat_1(A_130))), inference(resolution, [status(thm)], [c_178, c_264])).
% 3.08/1.47  tff(c_295, plain, (![A_9]: (~v1_relat_1(A_9) | v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_286])).
% 3.08/1.47  tff(c_300, plain, (![A_9]: (~v1_relat_1(A_9))), inference(negUnitSimplification, [status(thm)], [c_216, c_295])).
% 3.08/1.47  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_58])).
% 3.08/1.47  tff(c_313, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_214])).
% 3.08/1.47  tff(c_44, plain, (![A_59, B_60]: (v1_relat_1(k5_relat_1(A_59, B_60)) | ~v1_relat_1(B_60) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.08/1.47  tff(c_14, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.08/1.47  tff(c_34, plain, (![B_38]: (k2_zfmisc_1(k1_xboole_0, B_38)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.08/1.47  tff(c_323, plain, (![B_136]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_136)), k1_xboole_0) | ~v1_relat_1(B_136))), inference(splitRight, [status(thm)], [c_214])).
% 3.08/1.47  tff(c_133, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.08/1.47  tff(c_142, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_133])).
% 3.08/1.47  tff(c_333, plain, (![B_137]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_137))=k1_xboole_0 | ~v1_relat_1(B_137))), inference(resolution, [status(thm)], [c_323, c_142])).
% 3.08/1.47  tff(c_46, plain, (![A_61]: (k3_xboole_0(A_61, k2_zfmisc_1(k1_relat_1(A_61), k2_relat_1(A_61)))=A_61 | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.08/1.47  tff(c_348, plain, (![B_137]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_137), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_137))))=k5_relat_1(k1_xboole_0, B_137) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_137)) | ~v1_relat_1(B_137))), inference(superposition, [status(thm), theory('equality')], [c_333, c_46])).
% 3.08/1.47  tff(c_358, plain, (![B_138]: (k5_relat_1(k1_xboole_0, B_138)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_138)) | ~v1_relat_1(B_138))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_34, c_348])).
% 3.08/1.47  tff(c_362, plain, (![B_60]: (k5_relat_1(k1_xboole_0, B_60)=k1_xboole_0 | ~v1_relat_1(B_60) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_358])).
% 3.08/1.47  tff(c_366, plain, (![B_139]: (k5_relat_1(k1_xboole_0, B_139)=k1_xboole_0 | ~v1_relat_1(B_139))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_362])).
% 3.08/1.47  tff(c_375, plain, (k5_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_366])).
% 3.08/1.47  tff(c_381, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_375])).
% 3.08/1.47  tff(c_382, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 3.08/1.47  tff(c_501, plain, (![A_171, B_172]: (r1_tarski(k1_relat_1(k5_relat_1(A_171, B_172)), k1_relat_1(A_171)) | ~v1_relat_1(B_172) | ~v1_relat_1(A_171))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.08/1.47  tff(c_509, plain, (![B_172]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_172)), k1_xboole_0) | ~v1_relat_1(B_172) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_501])).
% 3.08/1.47  tff(c_513, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_509])).
% 3.08/1.47  tff(c_455, plain, (![C_158, B_159, A_160]: (r2_hidden(C_158, B_159) | ~r2_hidden(C_158, A_160) | ~r1_tarski(A_160, B_159))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.08/1.47  tff(c_461, plain, (![A_41, B_159]: (r2_hidden('#skF_2'(A_41), B_159) | ~r1_tarski(A_41, B_159) | v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_42, c_455])).
% 3.08/1.47  tff(c_546, plain, (![A_186, B_187]: (k4_tarski('#skF_3'(A_186, B_187), '#skF_4'(A_186, B_187))=B_187 | ~r2_hidden(B_187, A_186) | ~v1_relat_1(A_186))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.08/1.47  tff(c_550, plain, (![B_187, A_41, A_186]: (B_187!='#skF_2'(A_41) | v1_relat_1(A_41) | ~r2_hidden(B_187, A_186) | ~v1_relat_1(A_186))), inference(superposition, [status(thm), theory('equality')], [c_546, c_40])).
% 3.08/1.47  tff(c_570, plain, (![A_193, A_194]: (v1_relat_1(A_193) | ~r2_hidden('#skF_2'(A_193), A_194) | ~v1_relat_1(A_194))), inference(reflexivity, [status(thm), theory('equality')], [c_550])).
% 3.08/1.47  tff(c_583, plain, (![B_195, A_196]: (~v1_relat_1(B_195) | ~r1_tarski(A_196, B_195) | v1_relat_1(A_196))), inference(resolution, [status(thm)], [c_461, c_570])).
% 3.08/1.47  tff(c_592, plain, (![A_9]: (~v1_relat_1(A_9) | v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_583])).
% 3.08/1.47  tff(c_597, plain, (![A_9]: (~v1_relat_1(A_9))), inference(negUnitSimplification, [status(thm)], [c_513, c_592])).
% 3.08/1.47  tff(c_608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_597, c_58])).
% 3.08/1.47  tff(c_610, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_509])).
% 3.08/1.47  tff(c_32, plain, (![A_37]: (k2_zfmisc_1(A_37, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.08/1.47  tff(c_52, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.08/1.47  tff(c_732, plain, (![B_215, A_216]: (k2_relat_1(k5_relat_1(B_215, A_216))=k2_relat_1(A_216) | ~r1_tarski(k1_relat_1(A_216), k2_relat_1(B_215)) | ~v1_relat_1(B_215) | ~v1_relat_1(A_216))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.08/1.47  tff(c_738, plain, (![B_215]: (k2_relat_1(k5_relat_1(B_215, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_215)) | ~v1_relat_1(B_215) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_732])).
% 3.08/1.47  tff(c_795, plain, (![B_218]: (k2_relat_1(k5_relat_1(B_218, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_218))), inference(demodulation, [status(thm), theory('equality')], [c_610, c_16, c_52, c_738])).
% 3.08/1.47  tff(c_804, plain, (![B_218]: (k3_xboole_0(k5_relat_1(B_218, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_218, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_218, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_218, k1_xboole_0)) | ~v1_relat_1(B_218))), inference(superposition, [status(thm), theory('equality')], [c_795, c_46])).
% 3.08/1.47  tff(c_878, plain, (![B_226]: (k5_relat_1(B_226, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_226, k1_xboole_0)) | ~v1_relat_1(B_226))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_32, c_804])).
% 3.08/1.47  tff(c_885, plain, (![A_59]: (k5_relat_1(A_59, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_59))), inference(resolution, [status(thm)], [c_44, c_878])).
% 3.08/1.47  tff(c_891, plain, (![A_227]: (k5_relat_1(A_227, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_227))), inference(demodulation, [status(thm), theory('equality')], [c_610, c_885])).
% 3.08/1.47  tff(c_903, plain, (k5_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_891])).
% 3.08/1.47  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_382, c_903])).
% 3.08/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.47  
% 3.08/1.47  Inference rules
% 3.08/1.47  ----------------------
% 3.08/1.47  #Ref     : 3
% 3.08/1.47  #Sup     : 180
% 3.08/1.47  #Fact    : 0
% 3.08/1.47  #Define  : 0
% 3.08/1.47  #Split   : 3
% 3.08/1.47  #Chain   : 0
% 3.08/1.47  #Close   : 0
% 3.08/1.47  
% 3.08/1.47  Ordering : KBO
% 3.08/1.47  
% 3.08/1.47  Simplification rules
% 3.08/1.47  ----------------------
% 3.08/1.47  #Subsume      : 31
% 3.08/1.47  #Demod        : 101
% 3.08/1.47  #Tautology    : 116
% 3.08/1.47  #SimpNegUnit  : 24
% 3.08/1.47  #BackRed      : 12
% 3.08/1.47  
% 3.08/1.47  #Partial instantiations: 0
% 3.08/1.47  #Strategies tried      : 1
% 3.08/1.47  
% 3.08/1.47  Timing (in seconds)
% 3.08/1.47  ----------------------
% 3.08/1.48  Preprocessing        : 0.32
% 3.08/1.48  Parsing              : 0.16
% 3.08/1.48  CNF conversion       : 0.02
% 3.08/1.48  Main loop            : 0.33
% 3.08/1.48  Inferencing          : 0.13
% 3.08/1.48  Reduction            : 0.10
% 3.08/1.48  Demodulation         : 0.07
% 3.08/1.48  BG Simplification    : 0.02
% 3.08/1.48  Subsumption          : 0.06
% 3.08/1.48  Abstraction          : 0.02
% 3.08/1.48  MUC search           : 0.00
% 3.08/1.48  Cooper               : 0.00
% 3.08/1.48  Total                : 0.69
% 3.08/1.48  Index Insertion      : 0.00
% 3.08/1.48  Index Deletion       : 0.00
% 3.08/1.48  Index Matching       : 0.00
% 3.08/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
