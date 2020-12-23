%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:39 EST 2020

% Result     : Theorem 42.08s
% Output     : CNFRefutation 42.15s
% Verified   : 
% Statistics : Number of formulae       :  231 (47742 expanded)
%              Number of leaves         :   37 (16272 expanded)
%              Depth                    :   41
%              Number of atoms          :  414 (87048 expanded)
%              Number of equality atoms :  224 (40255 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

tff(f_90,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_97,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
        & r1_xboole_0(C,A)
        & r1_xboole_0(D,B) )
     => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_30,plain,(
    ! [A_28] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_146,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_150,plain,(
    ! [A_28] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_28) ) ),
    inference(resolution,[status(thm)],[c_30,c_146])).

tff(c_172,plain,(
    ! [A_28] : ~ v1_relat_1(A_28) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_52,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_52])).

tff(c_177,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_36,plain,(
    ! [A_35] : k7_relat_1(k1_xboole_0,A_35) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_353,plain,(
    ! [B_72,A_73] :
      ( r1_xboole_0(k1_relat_1(B_72),A_73)
      | k7_relat_1(B_72,A_73) != k1_xboole_0
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_364,plain,(
    ! [A_73] :
      ( r1_xboole_0(k1_xboole_0,A_73)
      | k7_relat_1(k1_xboole_0,A_73) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_353])).

tff(c_370,plain,(
    ! [A_74] : r1_xboole_0(k1_xboole_0,A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_36,c_364])).

tff(c_8,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_xboole_0(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_452,plain,(
    ! [A_82,A_83] :
      ( r1_xboole_0(A_82,A_83)
      | ~ r1_tarski(A_82,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_370,c_8])).

tff(c_48,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_473,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_452,c_48])).

tff(c_54,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    ! [A_36] :
      ( r1_tarski(A_36,k2_zfmisc_1(k1_relat_1(A_36),k2_relat_1(A_36)))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_369,plain,(
    ! [A_73] : r1_xboole_0(k1_xboole_0,A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_36,c_364])).

tff(c_10,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_956,plain,(
    ! [C_133,B_134,D_135,A_136] :
      ( C_133 = B_134
      | ~ r1_xboole_0(D_135,B_134)
      | ~ r1_xboole_0(C_133,A_136)
      | k2_xboole_0(C_133,D_135) != k2_xboole_0(A_136,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_964,plain,(
    ! [C_133,A_73,A_136] :
      ( C_133 = A_73
      | ~ r1_xboole_0(C_133,A_136)
      | k2_xboole_0(C_133,k1_xboole_0) != k2_xboole_0(A_136,A_73) ) ),
    inference(resolution,[status(thm)],[c_369,c_956])).

tff(c_1021,plain,(
    ! [C_142,A_143,A_144] :
      ( C_142 = A_143
      | ~ r1_xboole_0(C_142,A_144)
      | k2_xboole_0(A_144,A_143) != C_142 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_964])).

tff(c_1055,plain,(
    ! [A_143] : k2_xboole_0(k1_xboole_0,A_143) = A_143 ),
    inference(resolution,[status(thm)],[c_10,c_1021])).

tff(c_235,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(k2_xboole_0(A_61,B_62),B_62) = A_61
      | ~ r1_xboole_0(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2851,plain,(
    ! [A_217,B_218] :
      ( k4_xboole_0(k2_xboole_0(A_217,B_218),A_217) = k3_xboole_0(k2_xboole_0(A_217,B_218),B_218)
      | ~ r1_xboole_0(A_217,B_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_6])).

tff(c_108,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = A_48
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_120,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(resolution,[status(thm)],[c_10,c_108])).

tff(c_2905,plain,(
    ! [B_218] :
      ( k3_xboole_0(k2_xboole_0(k1_xboole_0,B_218),B_218) = k2_xboole_0(k1_xboole_0,B_218)
      | ~ r1_xboole_0(k1_xboole_0,B_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2851,c_120])).

tff(c_2943,plain,(
    ! [B_219] : k3_xboole_0(B_219,B_219) = B_219 ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_1055,c_1055,c_2905])).

tff(c_24,plain,(
    ! [A_22] : k2_zfmisc_1(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_715,plain,(
    ! [A_114,C_115,B_116,D_117] : k3_xboole_0(k2_zfmisc_1(A_114,C_115),k2_zfmisc_1(B_116,D_117)) = k2_zfmisc_1(k3_xboole_0(A_114,B_116),k3_xboole_0(C_115,D_117)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_749,plain,(
    ! [A_114,A_22,C_115] : k2_zfmisc_1(k3_xboole_0(A_114,A_22),k3_xboole_0(C_115,k1_xboole_0)) = k3_xboole_0(k2_zfmisc_1(A_114,C_115),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_715])).

tff(c_2957,plain,(
    ! [B_219,C_115] : k3_xboole_0(k2_zfmisc_1(B_219,C_115),k1_xboole_0) = k2_zfmisc_1(B_219,k3_xboole_0(C_115,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2943,c_749])).

tff(c_26,plain,(
    ! [B_23] : k2_zfmisc_1(k1_xboole_0,B_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_755,plain,(
    ! [A_114,C_115,B_23] : k2_zfmisc_1(k3_xboole_0(A_114,k1_xboole_0),k3_xboole_0(C_115,B_23)) = k3_xboole_0(k2_zfmisc_1(A_114,C_115),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_715])).

tff(c_2987,plain,(
    ! [A_114,B_219] : k3_xboole_0(k2_zfmisc_1(A_114,B_219),k1_xboole_0) = k2_zfmisc_1(k3_xboole_0(A_114,k1_xboole_0),B_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_2943,c_755])).

tff(c_4106,plain,(
    ! [A_114,B_219] : k2_zfmisc_1(k3_xboole_0(A_114,k1_xboole_0),B_219) = k2_zfmisc_1(A_114,k3_xboole_0(B_219,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_2987])).

tff(c_3997,plain,(
    ! [A_114,A_22,C_115] : k2_zfmisc_1(k3_xboole_0(A_114,A_22),k3_xboole_0(C_115,k1_xboole_0)) = k2_zfmisc_1(k3_xboole_0(A_114,k1_xboole_0),C_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2987,c_749])).

tff(c_5429,plain,(
    ! [A_312,A_313,C_314] : k2_zfmisc_1(k3_xboole_0(A_312,A_313),k3_xboole_0(C_314,k1_xboole_0)) = k2_zfmisc_1(A_312,k3_xboole_0(C_314,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4106,c_3997])).

tff(c_5490,plain,(
    ! [A_114,C_314] : k2_zfmisc_1(A_114,k3_xboole_0(k3_xboole_0(C_314,k1_xboole_0),k1_xboole_0)) = k2_zfmisc_1(A_114,k3_xboole_0(C_314,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4106,c_5429])).

tff(c_3999,plain,(
    ! [A_256,B_257] : k3_xboole_0(k2_zfmisc_1(A_256,B_257),k1_xboole_0) = k2_zfmisc_1(k3_xboole_0(A_256,k1_xboole_0),B_257) ),
    inference(superposition,[status(thm),theory(equality)],[c_2943,c_755])).

tff(c_151,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_169,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_151])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_974,plain,(
    ! [C_133,A_136,A_11] :
      ( k1_xboole_0 = C_133
      | ~ r1_xboole_0(C_133,A_136)
      | k2_xboole_0(C_133,A_11) != k2_xboole_0(A_136,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_956])).

tff(c_987,plain,(
    ! [C_137,A_138,A_139] :
      ( k1_xboole_0 = C_137
      | ~ r1_xboole_0(C_137,A_138)
      | k2_xboole_0(C_137,A_139) != A_138 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_974])).

tff(c_1348,plain,(
    ! [A_169,A_170,B_171] :
      ( k1_xboole_0 = A_169
      | k2_xboole_0(A_169,A_170) != B_171
      | k4_xboole_0(A_169,B_171) != A_169 ) ),
    inference(resolution,[status(thm)],[c_18,c_987])).

tff(c_1350,plain,(
    ! [B_171] :
      ( k1_xboole_0 = B_171
      | k4_xboole_0(B_171,B_171) != B_171 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1348])).

tff(c_1352,plain,(
    ! [B_171] :
      ( k1_xboole_0 = B_171
      | k3_xboole_0(B_171,k1_xboole_0) != B_171 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_1350])).

tff(c_4029,plain,(
    ! [A_256,B_257] :
      ( k2_zfmisc_1(A_256,B_257) = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0(A_256,k1_xboole_0),B_257) != k2_zfmisc_1(A_256,B_257) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3999,c_1352])).

tff(c_7754,plain,(
    ! [A_368,B_369] :
      ( k2_zfmisc_1(A_368,B_369) = k1_xboole_0
      | k2_zfmisc_1(A_368,k3_xboole_0(B_369,k1_xboole_0)) != k2_zfmisc_1(A_368,B_369) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4106,c_4029])).

tff(c_7811,plain,(
    ! [A_114,C_314] : k2_zfmisc_1(A_114,k3_xboole_0(C_314,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5490,c_7754])).

tff(c_4212,plain,(
    ! [A_261,B_262] : k2_zfmisc_1(k3_xboole_0(A_261,k1_xboole_0),B_262) = k2_zfmisc_1(A_261,k3_xboole_0(B_262,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_2987])).

tff(c_22,plain,(
    ! [B_23,A_22] :
      ( k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | k2_zfmisc_1(A_22,B_23) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4234,plain,(
    ! [B_262,A_261] :
      ( k1_xboole_0 = B_262
      | k3_xboole_0(A_261,k1_xboole_0) = k1_xboole_0
      | k2_zfmisc_1(A_261,k3_xboole_0(B_262,k1_xboole_0)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4212,c_22])).

tff(c_7834,plain,(
    ! [B_262,A_261] :
      ( k1_xboole_0 = B_262
      | k3_xboole_0(A_261,k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7811,c_4234])).

tff(c_8029,plain,(
    ! [A_374] : k3_xboole_0(A_374,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7834])).

tff(c_4,plain,(
    ! [A_2,C_4,B_3,D_5] :
      ( r1_tarski(k3_xboole_0(A_2,C_4),k3_xboole_0(B_3,D_5))
      | ~ r1_tarski(C_4,D_5)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8827,plain,(
    ! [A_404,C_405,A_406] :
      ( r1_tarski(k3_xboole_0(A_404,C_405),k1_xboole_0)
      | ~ r1_tarski(C_405,k1_xboole_0)
      | ~ r1_tarski(A_404,A_406) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8029,c_4])).

tff(c_8859,plain,(
    ! [A_409,C_410] :
      ( r1_tarski(k3_xboole_0(A_409,C_410),k1_xboole_0)
      | ~ r1_tarski(C_410,k1_xboole_0)
      | ~ v1_relat_1(A_409) ) ),
    inference(resolution,[status(thm)],[c_38,c_8827])).

tff(c_14,plain,(
    ! [A_16,B_17] :
      ( ~ r1_xboole_0(k3_xboole_0(A_16,B_17),B_17)
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_471,plain,(
    ! [A_16,A_83] :
      ( r1_xboole_0(A_16,A_83)
      | ~ r1_tarski(k3_xboole_0(A_16,A_83),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_452,c_14])).

tff(c_8943,plain,(
    ! [A_411,C_412] :
      ( r1_xboole_0(A_411,C_412)
      | ~ r1_tarski(C_412,k1_xboole_0)
      | ~ v1_relat_1(A_411) ) ),
    inference(resolution,[status(thm)],[c_8859,c_471])).

tff(c_8983,plain,
    ( ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8943,c_48])).

tff(c_9000,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8983])).

tff(c_273,plain,(
    ! [A_63] :
      ( r1_tarski(A_63,k2_zfmisc_1(k1_relat_1(A_63),k2_relat_1(A_63)))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_276,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_273])).

tff(c_281,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_26,c_276])).

tff(c_2932,plain,(
    ! [B_218] : k3_xboole_0(B_218,B_218) = B_218 ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_1055,c_1055,c_2905])).

tff(c_16,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_378,plain,(
    ! [A_75] : k4_xboole_0(k1_xboole_0,A_75) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_370,c_16])).

tff(c_391,plain,(
    ! [A_75] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_6])).

tff(c_421,plain,(
    ! [A_75] : k3_xboole_0(k1_xboole_0,A_75) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_391])).

tff(c_7982,plain,(
    ! [A_261] : k3_xboole_0(A_261,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7834])).

tff(c_121,plain,(
    ! [A_50,B_51] :
      ( ~ r1_xboole_0(k3_xboole_0(A_50,B_51),B_51)
      | r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_130,plain,(
    ! [A_50,B_19] :
      ( r1_xboole_0(A_50,B_19)
      | k4_xboole_0(k3_xboole_0(A_50,B_19),B_19) != k3_xboole_0(A_50,B_19) ) ),
    inference(resolution,[status(thm)],[c_18,c_121])).

tff(c_3027,plain,(
    ! [B_219] :
      ( r1_xboole_0(B_219,B_219)
      | k4_xboole_0(B_219,B_219) != k3_xboole_0(B_219,B_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2943,c_130])).

tff(c_3097,plain,(
    ! [B_219] :
      ( r1_xboole_0(B_219,B_219)
      | k3_xboole_0(B_219,k1_xboole_0) != B_219 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2932,c_169,c_3027])).

tff(c_8002,plain,(
    ! [B_219] :
      ( r1_xboole_0(B_219,B_219)
      | k1_xboole_0 != B_219 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7982,c_3097])).

tff(c_8012,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7982,c_169])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(k2_xboole_0(A_20,B_21),B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8335,plain,(
    ! [A_379,B_380] :
      ( ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(A_379,B_380),A_379),B_380)
      | r1_xboole_0(k2_xboole_0(A_379,B_380),B_380)
      | ~ r1_xboole_0(A_379,B_380) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2851,c_14])).

tff(c_21225,plain,(
    ! [B_847] :
      ( ~ r1_xboole_0(B_847,B_847)
      | r1_xboole_0(k2_xboole_0(B_847,B_847),B_847)
      | ~ r1_xboole_0(B_847,B_847)
      | ~ r1_xboole_0(B_847,B_847) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_8335])).

tff(c_21310,plain,(
    ! [B_851] :
      ( k4_xboole_0(k2_xboole_0(B_851,B_851),B_851) = k2_xboole_0(B_851,B_851)
      | ~ r1_xboole_0(B_851,B_851) ) ),
    inference(resolution,[status(thm)],[c_21225,c_16])).

tff(c_1046,plain,(
    ! [A_18,A_143,B_19] :
      ( A_18 = A_143
      | k2_xboole_0(B_19,A_143) != A_18
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(resolution,[status(thm)],[c_18,c_1021])).

tff(c_1387,plain,(
    ! [B_19,A_143] :
      ( k2_xboole_0(B_19,A_143) = A_143
      | k4_xboole_0(k2_xboole_0(B_19,A_143),B_19) != k2_xboole_0(B_19,A_143) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1046])).

tff(c_21544,plain,(
    ! [B_853] :
      ( k2_xboole_0(B_853,B_853) = B_853
      | ~ r1_xboole_0(B_853,B_853) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21310,c_1387])).

tff(c_21611,plain,(
    ! [B_19] :
      ( k2_xboole_0(B_19,B_19) = B_19
      | k4_xboole_0(B_19,B_19) != B_19 ) ),
    inference(resolution,[status(thm)],[c_18,c_21544])).

tff(c_21634,plain,(
    ! [B_19] :
      ( k2_xboole_0(B_19,B_19) = B_19
      | k1_xboole_0 != B_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8012,c_21611])).

tff(c_21384,plain,(
    ! [B_851] :
      ( k4_xboole_0(k2_xboole_0(B_851,B_851),k2_xboole_0(B_851,B_851)) = k3_xboole_0(k2_xboole_0(B_851,B_851),B_851)
      | ~ r1_xboole_0(B_851,B_851) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21310,c_6])).

tff(c_22310,plain,(
    ! [B_862] :
      ( k3_xboole_0(k2_xboole_0(B_862,B_862),B_862) = k1_xboole_0
      | ~ r1_xboole_0(B_862,B_862) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8012,c_21384])).

tff(c_740,plain,(
    ! [A_114,B_116,C_115,D_117] :
      ( ~ r1_xboole_0(k2_zfmisc_1(k3_xboole_0(A_114,B_116),k3_xboole_0(C_115,D_117)),k2_zfmisc_1(B_116,D_117))
      | r1_xboole_0(k2_zfmisc_1(A_114,C_115),k2_zfmisc_1(B_116,D_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_14])).

tff(c_22525,plain,(
    ! [A_114,B_116,B_862] :
      ( ~ r1_xboole_0(k2_zfmisc_1(k3_xboole_0(A_114,B_116),k1_xboole_0),k2_zfmisc_1(B_116,B_862))
      | r1_xboole_0(k2_zfmisc_1(A_114,k2_xboole_0(B_862,B_862)),k2_zfmisc_1(B_116,B_862))
      | ~ r1_xboole_0(B_862,B_862) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22310,c_740])).

tff(c_24313,plain,(
    ! [A_896,B_897,B_898] :
      ( r1_xboole_0(k2_zfmisc_1(A_896,k2_xboole_0(B_897,B_897)),k2_zfmisc_1(B_898,B_897))
      | ~ r1_xboole_0(B_897,B_897) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_24,c_22525])).

tff(c_24478,plain,(
    ! [A_902,B_903,B_904] :
      ( r1_xboole_0(k2_zfmisc_1(A_902,B_903),k2_zfmisc_1(B_904,B_903))
      | ~ r1_xboole_0(B_903,B_903)
      | k1_xboole_0 != B_903 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21634,c_24313])).

tff(c_3515,plain,(
    ! [C_227,B_228,A_229,A_230] :
      ( C_227 = B_228
      | ~ r1_xboole_0(C_227,A_229)
      | k2_xboole_0(C_227,A_230) != k2_xboole_0(A_229,B_228)
      | k4_xboole_0(A_230,B_228) != A_230 ) ),
    inference(resolution,[status(thm)],[c_18,c_956])).

tff(c_3525,plain,(
    ! [B_228,A_230,A_73] :
      ( k1_xboole_0 = B_228
      | k2_xboole_0(k1_xboole_0,A_230) != k2_xboole_0(A_73,B_228)
      | k4_xboole_0(A_230,B_228) != A_230 ) ),
    inference(resolution,[status(thm)],[c_369,c_3515])).

tff(c_3541,plain,(
    ! [B_228,A_73,A_230] :
      ( k1_xboole_0 = B_228
      | k2_xboole_0(A_73,B_228) != A_230
      | k4_xboole_0(A_230,B_228) != A_230 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_3525])).

tff(c_3579,plain,(
    ! [B_228,A_73] :
      ( k1_xboole_0 = B_228
      | k4_xboole_0(k2_xboole_0(A_73,B_228),B_228) != k2_xboole_0(A_73,B_228) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3541])).

tff(c_21436,plain,(
    ! [B_851] :
      ( k1_xboole_0 = B_851
      | ~ r1_xboole_0(B_851,B_851) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21310,c_3579])).

tff(c_24561,plain,(
    ! [B_905,B_906] :
      ( k2_zfmisc_1(B_905,B_906) = k1_xboole_0
      | ~ r1_xboole_0(B_906,B_906)
      | k1_xboole_0 != B_906 ) ),
    inference(resolution,[status(thm)],[c_24478,c_21436])).

tff(c_24642,plain,(
    ! [B_907,B_908] :
      ( k2_zfmisc_1(B_907,B_908) = k1_xboole_0
      | k1_xboole_0 != B_908 ) ),
    inference(resolution,[status(thm)],[c_8002,c_24561])).

tff(c_28,plain,(
    ! [A_24,C_26,B_25,D_27] : k3_xboole_0(k2_zfmisc_1(A_24,C_26),k2_zfmisc_1(B_25,D_27)) = k2_zfmisc_1(k3_xboole_0(A_24,B_25),k3_xboole_0(C_26,D_27)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_25186,plain,(
    ! [B_907,B_25,B_908,D_27] :
      ( k2_zfmisc_1(k3_xboole_0(B_907,B_25),k3_xboole_0(B_908,D_27)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_25,D_27))
      | k1_xboole_0 != B_908 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24642,c_28])).

tff(c_36046,plain,(
    ! [B_1084,B_1085,B_1086,D_1087] :
      ( k2_zfmisc_1(k3_xboole_0(B_1084,B_1085),k3_xboole_0(B_1086,D_1087)) = k1_xboole_0
      | k1_xboole_0 != B_1086 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_25186])).

tff(c_36446,plain,(
    ! [B_1088,B_1089,D_1090] :
      ( k2_zfmisc_1(B_1088,k3_xboole_0(B_1089,D_1090)) = k1_xboole_0
      | k1_xboole_0 != B_1089 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2932,c_36046])).

tff(c_36948,plain,(
    ! [B_1089,D_1090,B_1088] :
      ( k3_xboole_0(B_1089,D_1090) = k1_xboole_0
      | k1_xboole_0 = B_1088
      | k1_xboole_0 != B_1089 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36446,c_22])).

tff(c_37005,plain,(
    ! [B_1094,D_1095] :
      ( k3_xboole_0(B_1094,D_1095) = k1_xboole_0
      | k1_xboole_0 != B_1094 ) ),
    inference(splitLeft,[status(thm)],[c_36948])).

tff(c_37446,plain,(
    ! [B_1094,D_1095] :
      ( r1_xboole_0(B_1094,D_1095)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 != B_1094 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37005,c_471])).

tff(c_37677,plain,(
    ! [B_1096,D_1097] :
      ( r1_xboole_0(B_1096,D_1097)
      | k1_xboole_0 != B_1096 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_37446])).

tff(c_39121,plain,(
    ! [A_1104,D_1105] :
      ( r1_xboole_0(A_1104,D_1105)
      | k3_xboole_0(A_1104,D_1105) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_37677,c_14])).

tff(c_39215,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39121,c_48])).

tff(c_24640,plain,(
    ! [B_905] : k2_zfmisc_1(B_905,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8002,c_24561])).

tff(c_25189,plain,(
    ! [A_24,B_907,C_26,B_908] :
      ( k2_zfmisc_1(k3_xboole_0(A_24,B_907),k3_xboole_0(C_26,B_908)) = k3_xboole_0(k2_zfmisc_1(A_24,C_26),k1_xboole_0)
      | k1_xboole_0 != B_908 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24642,c_28])).

tff(c_27122,plain,(
    ! [A_954,B_955,C_956,B_957] :
      ( k2_zfmisc_1(k3_xboole_0(A_954,B_955),k3_xboole_0(C_956,B_957)) = k1_xboole_0
      | k1_xboole_0 != B_957 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7982,c_25189])).

tff(c_27456,plain,(
    ! [B_958,C_959,B_960] :
      ( k2_zfmisc_1(B_958,k3_xboole_0(C_959,B_960)) = k1_xboole_0
      | k1_xboole_0 != B_960 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2932,c_27122])).

tff(c_27897,plain,(
    ! [C_959,B_960,B_958] :
      ( k3_xboole_0(C_959,B_960) = k1_xboole_0
      | k1_xboole_0 = B_958
      | k1_xboole_0 != B_960 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27456,c_22])).

tff(c_27959,plain,(
    ! [C_965,B_966] :
      ( k3_xboole_0(C_965,B_966) = k1_xboole_0
      | k1_xboole_0 != B_966 ) ),
    inference(splitLeft,[status(thm)],[c_27897])).

tff(c_28345,plain,(
    ! [C_965,B_966] :
      ( r1_xboole_0(C_965,B_966)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 != B_966 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27959,c_471])).

tff(c_28536,plain,(
    ! [C_965,B_966] :
      ( r1_xboole_0(C_965,B_966)
      | k1_xboole_0 != B_966 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_28345])).

tff(c_28558,plain,(
    ! [C_967,B_968] :
      ( r1_xboole_0(C_967,B_968)
      | k1_xboole_0 != B_968 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_28345])).

tff(c_28645,plain,(
    ! [C_969,B_970] :
      ( k4_xboole_0(C_969,B_970) = C_969
      | k1_xboole_0 != B_970 ) ),
    inference(resolution,[status(thm)],[c_28558,c_16])).

tff(c_34855,plain,(
    ! [A_1048,B_1049] :
      ( k2_xboole_0(A_1048,B_1049) = A_1048
      | k1_xboole_0 != B_1049
      | ~ r1_xboole_0(A_1048,B_1049) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_28645])).

tff(c_34961,plain,(
    ! [C_965,B_966] :
      ( k2_xboole_0(C_965,B_966) = C_965
      | k1_xboole_0 != B_966 ) ),
    inference(resolution,[status(thm)],[c_28536,c_34855])).

tff(c_27716,plain,(
    ! [A_24,C_959,B_960,B_958,C_26] :
      ( k2_zfmisc_1(k3_xboole_0(A_24,B_958),k3_xboole_0(C_26,k3_xboole_0(C_959,B_960))) = k3_xboole_0(k2_zfmisc_1(A_24,C_26),k1_xboole_0)
      | k1_xboole_0 != B_960 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27456,c_28])).

tff(c_62586,plain,(
    ! [B_1485,C_1482,C_1483,B_1486,A_1484] :
      ( k2_zfmisc_1(k3_xboole_0(A_1484,B_1486),k3_xboole_0(C_1482,k3_xboole_0(C_1483,B_1485))) = k1_xboole_0
      | k1_xboole_0 != B_1485 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7982,c_27716])).

tff(c_63331,plain,(
    ! [B_1487,C_1488,C_1489,B_1490] :
      ( k2_zfmisc_1(B_1487,k3_xboole_0(C_1488,k3_xboole_0(C_1489,B_1490))) = k1_xboole_0
      | k1_xboole_0 != B_1490 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2932,c_62586])).

tff(c_64148,plain,(
    ! [C_1488,C_1489,B_1490,B_1487] :
      ( k3_xboole_0(C_1488,k3_xboole_0(C_1489,B_1490)) = k1_xboole_0
      | k1_xboole_0 = B_1487
      | k1_xboole_0 != B_1490 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63331,c_22])).

tff(c_64193,plain,(
    ! [C_1491,C_1492,B_1493] :
      ( k3_xboole_0(C_1491,k3_xboole_0(C_1492,B_1493)) = k1_xboole_0
      | k1_xboole_0 != B_1493 ) ),
    inference(splitLeft,[status(thm)],[c_64148])).

tff(c_64751,plain,(
    ! [C_1491,C_1492,B_1493] :
      ( r1_xboole_0(C_1491,k3_xboole_0(C_1492,B_1493))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 != B_1493 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64193,c_471])).

tff(c_65132,plain,(
    ! [C_1494,C_1495,B_1496] :
      ( r1_xboole_0(C_1494,k3_xboole_0(C_1495,B_1496))
      | k1_xboole_0 != B_1496 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_64751])).

tff(c_979,plain,(
    ! [C_133,A_73,A_136] :
      ( C_133 = A_73
      | ~ r1_xboole_0(C_133,A_136)
      | k2_xboole_0(A_136,A_73) != C_133 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_964])).

tff(c_68084,plain,(
    ! [C_1527,A_1528,C_1529,B_1530] :
      ( C_1527 = A_1528
      | k2_xboole_0(k3_xboole_0(C_1529,B_1530),A_1528) != C_1527
      | k1_xboole_0 != B_1530 ) ),
    inference(resolution,[status(thm)],[c_65132,c_979])).

tff(c_72085,plain,(
    ! [C_1529] : k3_xboole_0(C_1529,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34961,c_68084])).

tff(c_50,plain,(
    r1_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_119,plain,(
    k4_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_166,plain,(
    k4_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_1')) = k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_151])).

tff(c_264,plain,(
    k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) = k3_xboole_0(k2_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_166])).

tff(c_5084,plain,(
    ! [B_302,A_299,D_304,C_300,C_303,A_301] :
      ( r1_tarski(k3_xboole_0(A_299,C_300),k2_zfmisc_1(k3_xboole_0(A_301,B_302),k3_xboole_0(C_303,D_304)))
      | ~ r1_tarski(C_300,k2_zfmisc_1(B_302,D_304))
      | ~ r1_tarski(A_299,k2_zfmisc_1(A_301,C_303)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_4])).

tff(c_5208,plain,(
    ! [A_299,C_300,A_301,B_302] :
      ( r1_tarski(k3_xboole_0(A_299,C_300),k2_zfmisc_1(k3_xboole_0(A_301,B_302),k3_xboole_0(k2_relat_1('#skF_1'),k1_xboole_0)))
      | ~ r1_tarski(C_300,k2_zfmisc_1(B_302,k2_relat_1('#skF_2')))
      | ~ r1_tarski(A_299,k2_zfmisc_1(A_301,k2_relat_1('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_5084])).

tff(c_141569,plain,(
    ! [A_2040,C_2041,B_2042,A_2043] :
      ( r1_tarski(k3_xboole_0(A_2040,C_2041),k1_xboole_0)
      | ~ r1_tarski(C_2041,k2_zfmisc_1(B_2042,k2_relat_1('#skF_2')))
      | ~ r1_tarski(A_2040,k2_zfmisc_1(A_2043,k2_relat_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24640,c_72085,c_5208])).

tff(c_141592,plain,(
    ! [A_2040,A_2043] :
      ( r1_tarski(k3_xboole_0(A_2040,'#skF_2'),k1_xboole_0)
      | ~ r1_tarski(A_2040,k2_zfmisc_1(A_2043,k2_relat_1('#skF_1')))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_141569])).

tff(c_141599,plain,(
    ! [A_2044,A_2045] :
      ( r1_tarski(k3_xboole_0(A_2044,'#skF_2'),k1_xboole_0)
      | ~ r1_tarski(A_2044,k2_zfmisc_1(A_2045,k2_relat_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_141592])).

tff(c_141631,plain,
    ( r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_141599])).

tff(c_141637,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_141631])).

tff(c_376,plain,(
    ! [A_8,A_74] :
      ( r1_xboole_0(A_8,A_74)
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_370,c_8])).

tff(c_1147,plain,(
    ! [A_154,A_153,A_155] :
      ( A_154 = A_153
      | k2_xboole_0(A_155,A_154) != A_153
      | ~ r1_tarski(A_153,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_376,c_1021])).

tff(c_1150,plain,(
    ! [A_153] :
      ( k1_xboole_0 = A_153
      | ~ r1_tarski(A_153,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1147])).

tff(c_141700,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_141637,c_1150])).

tff(c_141791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39215,c_141700])).

tff(c_141793,plain,(
    ! [B_2046] : k1_xboole_0 = B_2046 ),
    inference(splitRight,[status(thm)],[c_64148])).

tff(c_143816,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_141793,c_39215])).

tff(c_143818,plain,(
    ! [B_6979] : k1_xboole_0 = B_6979 ),
    inference(splitRight,[status(thm)],[c_36948])).

tff(c_44,plain,(
    ! [B_38,A_37] :
      ( k7_relat_1(B_38,A_37) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_38),A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30011,plain,(
    ! [B_977,B_978] :
      ( k7_relat_1(B_977,B_978) = k1_xboole_0
      | ~ v1_relat_1(B_977)
      | k1_xboole_0 != B_978 ) ),
    inference(resolution,[status(thm)],[c_28558,c_44])).

tff(c_30024,plain,(
    ! [B_979] :
      ( k7_relat_1('#skF_2',B_979) = k1_xboole_0
      | k1_xboole_0 != B_979 ) ),
    inference(resolution,[status(thm)],[c_52,c_30011])).

tff(c_46,plain,(
    ! [B_38,A_37] :
      ( r1_xboole_0(k1_relat_1(B_38),A_37)
      | k7_relat_1(B_38,A_37) != k1_xboole_0
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6328,plain,(
    ! [B_333,A_334,A_335] :
      ( k1_relat_1(B_333) = k1_xboole_0
      | k2_xboole_0(k1_relat_1(B_333),A_334) != A_335
      | k7_relat_1(B_333,A_335) != k1_xboole_0
      | ~ v1_relat_1(B_333) ) ),
    inference(resolution,[status(thm)],[c_46,c_987])).

tff(c_6334,plain,(
    ! [B_333,A_335] :
      ( k1_relat_1(B_333) = k1_xboole_0
      | k1_relat_1(B_333) != A_335
      | k7_relat_1(B_333,A_335) != k1_xboole_0
      | ~ v1_relat_1(B_333) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6328])).

tff(c_30051,plain,(
    ! [B_979] :
      ( k1_relat_1('#skF_2') = k1_xboole_0
      | k1_relat_1('#skF_2') != B_979
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != B_979 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30024,c_6334])).

tff(c_30096,plain,(
    ! [B_979] :
      ( k1_relat_1('#skF_2') = k1_xboole_0
      | k1_relat_1('#skF_2') != B_979
      | k1_xboole_0 != B_979 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_30051])).

tff(c_32322,plain,(
    ! [B_979] :
      ( k1_relat_1('#skF_2') != B_979
      | k1_xboole_0 != B_979 ) ),
    inference(splitLeft,[status(thm)],[c_30096])).

tff(c_32326,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_32322])).

tff(c_145302,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_143818,c_32326])).

tff(c_145303,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30096])).

tff(c_145389,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_145303,c_38])).

tff(c_145459,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_26,c_145389])).

tff(c_145461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9000,c_145459])).

tff(c_145463,plain,(
    ! [B_10633] : k1_xboole_0 = B_10633 ),
    inference(splitRight,[status(thm)],[c_27897])).

tff(c_21638,plain,(
    ! [B_854] :
      ( k2_xboole_0(B_854,B_854) = B_854
      | k1_xboole_0 != B_854 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8012,c_21611])).

tff(c_21272,plain,(
    ! [B_847] :
      ( k4_xboole_0(k2_xboole_0(B_847,B_847),B_847) = k2_xboole_0(B_847,B_847)
      | ~ r1_xboole_0(B_847,B_847) ) ),
    inference(resolution,[status(thm)],[c_21225,c_16])).

tff(c_21644,plain,(
    ! [B_854] :
      ( k4_xboole_0(B_854,B_854) = k2_xboole_0(B_854,B_854)
      | ~ r1_xboole_0(B_854,B_854)
      | k1_xboole_0 != B_854 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21638,c_21272])).

tff(c_22766,plain,(
    ! [B_868] :
      ( k2_xboole_0(B_868,B_868) = k1_xboole_0
      | ~ r1_xboole_0(B_868,B_868)
      | k1_xboole_0 != B_868 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8012,c_21644])).

tff(c_22860,plain,(
    ! [B_869] :
      ( k2_xboole_0(B_869,B_869) = k1_xboole_0
      | k1_xboole_0 != B_869 ) ),
    inference(resolution,[status(thm)],[c_8002,c_22766])).

tff(c_285,plain,(
    ! [A_64,C_65,B_66] :
      ( r1_xboole_0(A_64,C_65)
      | ~ r1_xboole_0(B_66,C_65)
      | ~ r1_tarski(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_293,plain,(
    ! [A_64] :
      ( r1_xboole_0(A_64,k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_64,k2_relat_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_50,c_285])).

tff(c_3211,plain,(
    ! [C_221,A_222,A_223] :
      ( k2_relat_1('#skF_2') = C_221
      | ~ r1_xboole_0(C_221,A_222)
      | k2_xboole_0(C_221,A_223) != k2_xboole_0(A_222,k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_223,k2_relat_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_293,c_956])).

tff(c_3219,plain,(
    ! [A_223,A_73] :
      ( k2_relat_1('#skF_2') = k1_xboole_0
      | k2_xboole_0(k1_xboole_0,A_223) != k2_xboole_0(A_73,k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_223,k2_relat_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_369,c_3211])).

tff(c_3234,plain,(
    ! [A_73,A_223] :
      ( k2_relat_1('#skF_2') = k1_xboole_0
      | k2_xboole_0(A_73,k2_relat_1('#skF_2')) != A_223
      | ~ r1_tarski(A_223,k2_relat_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_3219])).

tff(c_5414,plain,(
    ! [A_73,A_223] :
      ( k2_xboole_0(A_73,k2_relat_1('#skF_2')) != A_223
      | ~ r1_tarski(A_223,k2_relat_1('#skF_1')) ) ),
    inference(splitLeft,[status(thm)],[c_3234])).

tff(c_5419,plain,(
    ! [A_73] : ~ r1_tarski(k2_xboole_0(A_73,k2_relat_1('#skF_2')),k2_relat_1('#skF_1')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5414])).

tff(c_23066,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1('#skF_1'))
    | k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22860,c_5419])).

tff(c_23524,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_23066])).

tff(c_146849,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_145463,c_23524])).

tff(c_146851,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_23066])).

tff(c_147083,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k1_xboole_0))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_146851,c_38])).

tff(c_147091,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_24,c_147083])).

tff(c_147093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9000,c_147091])).

tff(c_147530,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7834])).

tff(c_147531,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_147530,c_281])).

tff(c_147690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_473,c_147531])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:18:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 42.08/30.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.15/30.78  
% 42.15/30.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.15/30.78  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 42.15/30.78  
% 42.15/30.78  %Foreground sorts:
% 42.15/30.78  
% 42.15/30.78  
% 42.15/30.78  %Background operators:
% 42.15/30.78  
% 42.15/30.78  
% 42.15/30.78  %Foreground operators:
% 42.15/30.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 42.15/30.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 42.15/30.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 42.15/30.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 42.15/30.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 42.15/30.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 42.15/30.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 42.15/30.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 42.15/30.78  tff('#skF_2', type, '#skF_2': $i).
% 42.15/30.78  tff('#skF_1', type, '#skF_1': $i).
% 42.15/30.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 42.15/30.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 42.15/30.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 42.15/30.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 42.15/30.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 42.15/30.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 42.15/30.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 42.15/30.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 42.15/30.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 42.15/30.78  
% 42.15/30.82  tff(f_75, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 42.15/30.82  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 42.15/30.82  tff(f_113, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t215_relat_1)).
% 42.15/30.82  tff(f_90, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 42.15/30.82  tff(f_97, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 42.15/30.82  tff(f_103, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 42.15/30.82  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 42.15/30.82  tff(f_94, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 42.15/30.82  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 42.15/30.82  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 42.15/30.82  tff(f_51, axiom, (![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 42.15/30.82  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 42.15/30.82  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 42.15/30.82  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 42.15/30.82  tff(f_71, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 42.15/30.82  tff(f_73, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 42.15/30.82  tff(f_33, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_xboole_1)).
% 42.15/30.82  tff(f_57, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 42.15/30.82  tff(c_30, plain, (![A_28]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 42.15/30.82  tff(c_146, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_88])).
% 42.15/30.82  tff(c_150, plain, (![A_28]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_28))), inference(resolution, [status(thm)], [c_30, c_146])).
% 42.15/30.82  tff(c_172, plain, (![A_28]: (~v1_relat_1(A_28))), inference(splitLeft, [status(thm)], [c_150])).
% 42.15/30.82  tff(c_52, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 42.15/30.82  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_52])).
% 42.15/30.82  tff(c_177, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_150])).
% 42.15/30.82  tff(c_36, plain, (![A_35]: (k7_relat_1(k1_xboole_0, A_35)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_90])).
% 42.15/30.82  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 42.15/30.82  tff(c_353, plain, (![B_72, A_73]: (r1_xboole_0(k1_relat_1(B_72), A_73) | k7_relat_1(B_72, A_73)!=k1_xboole_0 | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_103])).
% 42.15/30.82  tff(c_364, plain, (![A_73]: (r1_xboole_0(k1_xboole_0, A_73) | k7_relat_1(k1_xboole_0, A_73)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_353])).
% 42.15/30.82  tff(c_370, plain, (![A_74]: (r1_xboole_0(k1_xboole_0, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_36, c_364])).
% 42.15/30.82  tff(c_8, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_xboole_0(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 42.15/30.82  tff(c_452, plain, (![A_82, A_83]: (r1_xboole_0(A_82, A_83) | ~r1_tarski(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_370, c_8])).
% 42.15/30.82  tff(c_48, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 42.15/30.82  tff(c_473, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_452, c_48])).
% 42.15/30.82  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 42.15/30.82  tff(c_38, plain, (![A_36]: (r1_tarski(A_36, k2_zfmisc_1(k1_relat_1(A_36), k2_relat_1(A_36))) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_94])).
% 42.15/30.82  tff(c_369, plain, (![A_73]: (r1_xboole_0(k1_xboole_0, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_36, c_364])).
% 42.15/30.82  tff(c_10, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 42.15/30.82  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 42.15/30.82  tff(c_956, plain, (![C_133, B_134, D_135, A_136]: (C_133=B_134 | ~r1_xboole_0(D_135, B_134) | ~r1_xboole_0(C_133, A_136) | k2_xboole_0(C_133, D_135)!=k2_xboole_0(A_136, B_134))), inference(cnfTransformation, [status(thm)], [f_51])).
% 42.15/30.82  tff(c_964, plain, (![C_133, A_73, A_136]: (C_133=A_73 | ~r1_xboole_0(C_133, A_136) | k2_xboole_0(C_133, k1_xboole_0)!=k2_xboole_0(A_136, A_73))), inference(resolution, [status(thm)], [c_369, c_956])).
% 42.15/30.82  tff(c_1021, plain, (![C_142, A_143, A_144]: (C_142=A_143 | ~r1_xboole_0(C_142, A_144) | k2_xboole_0(A_144, A_143)!=C_142)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_964])).
% 42.15/30.82  tff(c_1055, plain, (![A_143]: (k2_xboole_0(k1_xboole_0, A_143)=A_143)), inference(resolution, [status(thm)], [c_10, c_1021])).
% 42.15/30.82  tff(c_235, plain, (![A_61, B_62]: (k4_xboole_0(k2_xboole_0(A_61, B_62), B_62)=A_61 | ~r1_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 42.15/30.82  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 42.15/30.82  tff(c_2851, plain, (![A_217, B_218]: (k4_xboole_0(k2_xboole_0(A_217, B_218), A_217)=k3_xboole_0(k2_xboole_0(A_217, B_218), B_218) | ~r1_xboole_0(A_217, B_218))), inference(superposition, [status(thm), theory('equality')], [c_235, c_6])).
% 42.15/30.82  tff(c_108, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=A_48 | ~r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_61])).
% 42.15/30.82  tff(c_120, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(resolution, [status(thm)], [c_10, c_108])).
% 42.15/30.82  tff(c_2905, plain, (![B_218]: (k3_xboole_0(k2_xboole_0(k1_xboole_0, B_218), B_218)=k2_xboole_0(k1_xboole_0, B_218) | ~r1_xboole_0(k1_xboole_0, B_218))), inference(superposition, [status(thm), theory('equality')], [c_2851, c_120])).
% 42.15/30.82  tff(c_2943, plain, (![B_219]: (k3_xboole_0(B_219, B_219)=B_219)), inference(demodulation, [status(thm), theory('equality')], [c_369, c_1055, c_1055, c_2905])).
% 42.15/30.82  tff(c_24, plain, (![A_22]: (k2_zfmisc_1(A_22, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.15/30.82  tff(c_715, plain, (![A_114, C_115, B_116, D_117]: (k3_xboole_0(k2_zfmisc_1(A_114, C_115), k2_zfmisc_1(B_116, D_117))=k2_zfmisc_1(k3_xboole_0(A_114, B_116), k3_xboole_0(C_115, D_117)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 42.15/30.82  tff(c_749, plain, (![A_114, A_22, C_115]: (k2_zfmisc_1(k3_xboole_0(A_114, A_22), k3_xboole_0(C_115, k1_xboole_0))=k3_xboole_0(k2_zfmisc_1(A_114, C_115), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_715])).
% 42.15/30.82  tff(c_2957, plain, (![B_219, C_115]: (k3_xboole_0(k2_zfmisc_1(B_219, C_115), k1_xboole_0)=k2_zfmisc_1(B_219, k3_xboole_0(C_115, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_2943, c_749])).
% 42.15/30.82  tff(c_26, plain, (![B_23]: (k2_zfmisc_1(k1_xboole_0, B_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.15/30.82  tff(c_755, plain, (![A_114, C_115, B_23]: (k2_zfmisc_1(k3_xboole_0(A_114, k1_xboole_0), k3_xboole_0(C_115, B_23))=k3_xboole_0(k2_zfmisc_1(A_114, C_115), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_715])).
% 42.15/30.82  tff(c_2987, plain, (![A_114, B_219]: (k3_xboole_0(k2_zfmisc_1(A_114, B_219), k1_xboole_0)=k2_zfmisc_1(k3_xboole_0(A_114, k1_xboole_0), B_219))), inference(superposition, [status(thm), theory('equality')], [c_2943, c_755])).
% 42.15/30.82  tff(c_4106, plain, (![A_114, B_219]: (k2_zfmisc_1(k3_xboole_0(A_114, k1_xboole_0), B_219)=k2_zfmisc_1(A_114, k3_xboole_0(B_219, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_2987])).
% 42.15/30.82  tff(c_3997, plain, (![A_114, A_22, C_115]: (k2_zfmisc_1(k3_xboole_0(A_114, A_22), k3_xboole_0(C_115, k1_xboole_0))=k2_zfmisc_1(k3_xboole_0(A_114, k1_xboole_0), C_115))), inference(demodulation, [status(thm), theory('equality')], [c_2987, c_749])).
% 42.15/30.82  tff(c_5429, plain, (![A_312, A_313, C_314]: (k2_zfmisc_1(k3_xboole_0(A_312, A_313), k3_xboole_0(C_314, k1_xboole_0))=k2_zfmisc_1(A_312, k3_xboole_0(C_314, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_4106, c_3997])).
% 42.15/30.82  tff(c_5490, plain, (![A_114, C_314]: (k2_zfmisc_1(A_114, k3_xboole_0(k3_xboole_0(C_314, k1_xboole_0), k1_xboole_0))=k2_zfmisc_1(A_114, k3_xboole_0(C_314, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_4106, c_5429])).
% 42.15/30.82  tff(c_3999, plain, (![A_256, B_257]: (k3_xboole_0(k2_zfmisc_1(A_256, B_257), k1_xboole_0)=k2_zfmisc_1(k3_xboole_0(A_256, k1_xboole_0), B_257))), inference(superposition, [status(thm), theory('equality')], [c_2943, c_755])).
% 42.15/30.82  tff(c_151, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 42.15/30.82  tff(c_169, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_120, c_151])).
% 42.15/30.82  tff(c_18, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k4_xboole_0(A_18, B_19)!=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 42.15/30.82  tff(c_974, plain, (![C_133, A_136, A_11]: (k1_xboole_0=C_133 | ~r1_xboole_0(C_133, A_136) | k2_xboole_0(C_133, A_11)!=k2_xboole_0(A_136, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_956])).
% 42.15/30.82  tff(c_987, plain, (![C_137, A_138, A_139]: (k1_xboole_0=C_137 | ~r1_xboole_0(C_137, A_138) | k2_xboole_0(C_137, A_139)!=A_138)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_974])).
% 42.15/30.82  tff(c_1348, plain, (![A_169, A_170, B_171]: (k1_xboole_0=A_169 | k2_xboole_0(A_169, A_170)!=B_171 | k4_xboole_0(A_169, B_171)!=A_169)), inference(resolution, [status(thm)], [c_18, c_987])).
% 42.15/30.82  tff(c_1350, plain, (![B_171]: (k1_xboole_0=B_171 | k4_xboole_0(B_171, B_171)!=B_171)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1348])).
% 42.15/30.82  tff(c_1352, plain, (![B_171]: (k1_xboole_0=B_171 | k3_xboole_0(B_171, k1_xboole_0)!=B_171)), inference(demodulation, [status(thm), theory('equality')], [c_169, c_1350])).
% 42.15/30.82  tff(c_4029, plain, (![A_256, B_257]: (k2_zfmisc_1(A_256, B_257)=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0(A_256, k1_xboole_0), B_257)!=k2_zfmisc_1(A_256, B_257))), inference(superposition, [status(thm), theory('equality')], [c_3999, c_1352])).
% 42.15/30.82  tff(c_7754, plain, (![A_368, B_369]: (k2_zfmisc_1(A_368, B_369)=k1_xboole_0 | k2_zfmisc_1(A_368, k3_xboole_0(B_369, k1_xboole_0))!=k2_zfmisc_1(A_368, B_369))), inference(demodulation, [status(thm), theory('equality')], [c_4106, c_4029])).
% 42.15/30.82  tff(c_7811, plain, (![A_114, C_314]: (k2_zfmisc_1(A_114, k3_xboole_0(C_314, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5490, c_7754])).
% 42.15/30.82  tff(c_4212, plain, (![A_261, B_262]: (k2_zfmisc_1(k3_xboole_0(A_261, k1_xboole_0), B_262)=k2_zfmisc_1(A_261, k3_xboole_0(B_262, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_2987])).
% 42.15/30.82  tff(c_22, plain, (![B_23, A_22]: (k1_xboole_0=B_23 | k1_xboole_0=A_22 | k2_zfmisc_1(A_22, B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.15/30.82  tff(c_4234, plain, (![B_262, A_261]: (k1_xboole_0=B_262 | k3_xboole_0(A_261, k1_xboole_0)=k1_xboole_0 | k2_zfmisc_1(A_261, k3_xboole_0(B_262, k1_xboole_0))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4212, c_22])).
% 42.15/30.82  tff(c_7834, plain, (![B_262, A_261]: (k1_xboole_0=B_262 | k3_xboole_0(A_261, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7811, c_4234])).
% 42.15/30.82  tff(c_8029, plain, (![A_374]: (k3_xboole_0(A_374, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7834])).
% 42.15/30.82  tff(c_4, plain, (![A_2, C_4, B_3, D_5]: (r1_tarski(k3_xboole_0(A_2, C_4), k3_xboole_0(B_3, D_5)) | ~r1_tarski(C_4, D_5) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 42.15/30.82  tff(c_8827, plain, (![A_404, C_405, A_406]: (r1_tarski(k3_xboole_0(A_404, C_405), k1_xboole_0) | ~r1_tarski(C_405, k1_xboole_0) | ~r1_tarski(A_404, A_406))), inference(superposition, [status(thm), theory('equality')], [c_8029, c_4])).
% 42.15/30.82  tff(c_8859, plain, (![A_409, C_410]: (r1_tarski(k3_xboole_0(A_409, C_410), k1_xboole_0) | ~r1_tarski(C_410, k1_xboole_0) | ~v1_relat_1(A_409))), inference(resolution, [status(thm)], [c_38, c_8827])).
% 42.15/30.82  tff(c_14, plain, (![A_16, B_17]: (~r1_xboole_0(k3_xboole_0(A_16, B_17), B_17) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 42.15/30.82  tff(c_471, plain, (![A_16, A_83]: (r1_xboole_0(A_16, A_83) | ~r1_tarski(k3_xboole_0(A_16, A_83), k1_xboole_0))), inference(resolution, [status(thm)], [c_452, c_14])).
% 42.15/30.82  tff(c_8943, plain, (![A_411, C_412]: (r1_xboole_0(A_411, C_412) | ~r1_tarski(C_412, k1_xboole_0) | ~v1_relat_1(A_411))), inference(resolution, [status(thm)], [c_8859, c_471])).
% 42.15/30.82  tff(c_8983, plain, (~r1_tarski('#skF_2', k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8943, c_48])).
% 42.15/30.82  tff(c_9000, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8983])).
% 42.15/30.82  tff(c_273, plain, (![A_63]: (r1_tarski(A_63, k2_zfmisc_1(k1_relat_1(A_63), k2_relat_1(A_63))) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_94])).
% 42.15/30.82  tff(c_276, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1(k1_xboole_0, k2_relat_1(k1_xboole_0))) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_273])).
% 42.15/30.82  tff(c_281, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_177, c_26, c_276])).
% 42.15/30.82  tff(c_2932, plain, (![B_218]: (k3_xboole_0(B_218, B_218)=B_218)), inference(demodulation, [status(thm), theory('equality')], [c_369, c_1055, c_1055, c_2905])).
% 42.15/30.82  tff(c_16, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 42.15/30.82  tff(c_378, plain, (![A_75]: (k4_xboole_0(k1_xboole_0, A_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_370, c_16])).
% 42.15/30.82  tff(c_391, plain, (![A_75]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, A_75))), inference(superposition, [status(thm), theory('equality')], [c_378, c_6])).
% 42.15/30.82  tff(c_421, plain, (![A_75]: (k3_xboole_0(k1_xboole_0, A_75)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_391])).
% 42.15/30.82  tff(c_7982, plain, (![A_261]: (k3_xboole_0(A_261, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7834])).
% 42.15/30.82  tff(c_121, plain, (![A_50, B_51]: (~r1_xboole_0(k3_xboole_0(A_50, B_51), B_51) | r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 42.15/30.82  tff(c_130, plain, (![A_50, B_19]: (r1_xboole_0(A_50, B_19) | k4_xboole_0(k3_xboole_0(A_50, B_19), B_19)!=k3_xboole_0(A_50, B_19))), inference(resolution, [status(thm)], [c_18, c_121])).
% 42.15/30.82  tff(c_3027, plain, (![B_219]: (r1_xboole_0(B_219, B_219) | k4_xboole_0(B_219, B_219)!=k3_xboole_0(B_219, B_219))), inference(superposition, [status(thm), theory('equality')], [c_2943, c_130])).
% 42.15/30.82  tff(c_3097, plain, (![B_219]: (r1_xboole_0(B_219, B_219) | k3_xboole_0(B_219, k1_xboole_0)!=B_219)), inference(demodulation, [status(thm), theory('equality')], [c_2932, c_169, c_3027])).
% 42.15/30.82  tff(c_8002, plain, (![B_219]: (r1_xboole_0(B_219, B_219) | k1_xboole_0!=B_219)), inference(demodulation, [status(thm), theory('equality')], [c_7982, c_3097])).
% 42.15/30.82  tff(c_8012, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7982, c_169])).
% 42.15/30.82  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(k2_xboole_0(A_20, B_21), B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 42.15/30.82  tff(c_8335, plain, (![A_379, B_380]: (~r1_xboole_0(k4_xboole_0(k2_xboole_0(A_379, B_380), A_379), B_380) | r1_xboole_0(k2_xboole_0(A_379, B_380), B_380) | ~r1_xboole_0(A_379, B_380))), inference(superposition, [status(thm), theory('equality')], [c_2851, c_14])).
% 42.15/30.82  tff(c_21225, plain, (![B_847]: (~r1_xboole_0(B_847, B_847) | r1_xboole_0(k2_xboole_0(B_847, B_847), B_847) | ~r1_xboole_0(B_847, B_847) | ~r1_xboole_0(B_847, B_847))), inference(superposition, [status(thm), theory('equality')], [c_20, c_8335])).
% 42.15/30.82  tff(c_21310, plain, (![B_851]: (k4_xboole_0(k2_xboole_0(B_851, B_851), B_851)=k2_xboole_0(B_851, B_851) | ~r1_xboole_0(B_851, B_851))), inference(resolution, [status(thm)], [c_21225, c_16])).
% 42.15/30.82  tff(c_1046, plain, (![A_18, A_143, B_19]: (A_18=A_143 | k2_xboole_0(B_19, A_143)!=A_18 | k4_xboole_0(A_18, B_19)!=A_18)), inference(resolution, [status(thm)], [c_18, c_1021])).
% 42.15/30.82  tff(c_1387, plain, (![B_19, A_143]: (k2_xboole_0(B_19, A_143)=A_143 | k4_xboole_0(k2_xboole_0(B_19, A_143), B_19)!=k2_xboole_0(B_19, A_143))), inference(reflexivity, [status(thm), theory('equality')], [c_1046])).
% 42.15/30.82  tff(c_21544, plain, (![B_853]: (k2_xboole_0(B_853, B_853)=B_853 | ~r1_xboole_0(B_853, B_853))), inference(superposition, [status(thm), theory('equality')], [c_21310, c_1387])).
% 42.15/30.82  tff(c_21611, plain, (![B_19]: (k2_xboole_0(B_19, B_19)=B_19 | k4_xboole_0(B_19, B_19)!=B_19)), inference(resolution, [status(thm)], [c_18, c_21544])).
% 42.15/30.82  tff(c_21634, plain, (![B_19]: (k2_xboole_0(B_19, B_19)=B_19 | k1_xboole_0!=B_19)), inference(demodulation, [status(thm), theory('equality')], [c_8012, c_21611])).
% 42.15/30.82  tff(c_21384, plain, (![B_851]: (k4_xboole_0(k2_xboole_0(B_851, B_851), k2_xboole_0(B_851, B_851))=k3_xboole_0(k2_xboole_0(B_851, B_851), B_851) | ~r1_xboole_0(B_851, B_851))), inference(superposition, [status(thm), theory('equality')], [c_21310, c_6])).
% 42.15/30.82  tff(c_22310, plain, (![B_862]: (k3_xboole_0(k2_xboole_0(B_862, B_862), B_862)=k1_xboole_0 | ~r1_xboole_0(B_862, B_862))), inference(demodulation, [status(thm), theory('equality')], [c_8012, c_21384])).
% 42.15/30.82  tff(c_740, plain, (![A_114, B_116, C_115, D_117]: (~r1_xboole_0(k2_zfmisc_1(k3_xboole_0(A_114, B_116), k3_xboole_0(C_115, D_117)), k2_zfmisc_1(B_116, D_117)) | r1_xboole_0(k2_zfmisc_1(A_114, C_115), k2_zfmisc_1(B_116, D_117)))), inference(superposition, [status(thm), theory('equality')], [c_715, c_14])).
% 42.15/30.82  tff(c_22525, plain, (![A_114, B_116, B_862]: (~r1_xboole_0(k2_zfmisc_1(k3_xboole_0(A_114, B_116), k1_xboole_0), k2_zfmisc_1(B_116, B_862)) | r1_xboole_0(k2_zfmisc_1(A_114, k2_xboole_0(B_862, B_862)), k2_zfmisc_1(B_116, B_862)) | ~r1_xboole_0(B_862, B_862))), inference(superposition, [status(thm), theory('equality')], [c_22310, c_740])).
% 42.15/30.82  tff(c_24313, plain, (![A_896, B_897, B_898]: (r1_xboole_0(k2_zfmisc_1(A_896, k2_xboole_0(B_897, B_897)), k2_zfmisc_1(B_898, B_897)) | ~r1_xboole_0(B_897, B_897))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_24, c_22525])).
% 42.15/30.82  tff(c_24478, plain, (![A_902, B_903, B_904]: (r1_xboole_0(k2_zfmisc_1(A_902, B_903), k2_zfmisc_1(B_904, B_903)) | ~r1_xboole_0(B_903, B_903) | k1_xboole_0!=B_903)), inference(superposition, [status(thm), theory('equality')], [c_21634, c_24313])).
% 42.15/30.82  tff(c_3515, plain, (![C_227, B_228, A_229, A_230]: (C_227=B_228 | ~r1_xboole_0(C_227, A_229) | k2_xboole_0(C_227, A_230)!=k2_xboole_0(A_229, B_228) | k4_xboole_0(A_230, B_228)!=A_230)), inference(resolution, [status(thm)], [c_18, c_956])).
% 42.15/30.82  tff(c_3525, plain, (![B_228, A_230, A_73]: (k1_xboole_0=B_228 | k2_xboole_0(k1_xboole_0, A_230)!=k2_xboole_0(A_73, B_228) | k4_xboole_0(A_230, B_228)!=A_230)), inference(resolution, [status(thm)], [c_369, c_3515])).
% 42.15/30.82  tff(c_3541, plain, (![B_228, A_73, A_230]: (k1_xboole_0=B_228 | k2_xboole_0(A_73, B_228)!=A_230 | k4_xboole_0(A_230, B_228)!=A_230)), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_3525])).
% 42.15/30.82  tff(c_3579, plain, (![B_228, A_73]: (k1_xboole_0=B_228 | k4_xboole_0(k2_xboole_0(A_73, B_228), B_228)!=k2_xboole_0(A_73, B_228))), inference(reflexivity, [status(thm), theory('equality')], [c_3541])).
% 42.15/30.82  tff(c_21436, plain, (![B_851]: (k1_xboole_0=B_851 | ~r1_xboole_0(B_851, B_851))), inference(superposition, [status(thm), theory('equality')], [c_21310, c_3579])).
% 42.15/30.82  tff(c_24561, plain, (![B_905, B_906]: (k2_zfmisc_1(B_905, B_906)=k1_xboole_0 | ~r1_xboole_0(B_906, B_906) | k1_xboole_0!=B_906)), inference(resolution, [status(thm)], [c_24478, c_21436])).
% 42.15/30.82  tff(c_24642, plain, (![B_907, B_908]: (k2_zfmisc_1(B_907, B_908)=k1_xboole_0 | k1_xboole_0!=B_908)), inference(resolution, [status(thm)], [c_8002, c_24561])).
% 42.15/30.82  tff(c_28, plain, (![A_24, C_26, B_25, D_27]: (k3_xboole_0(k2_zfmisc_1(A_24, C_26), k2_zfmisc_1(B_25, D_27))=k2_zfmisc_1(k3_xboole_0(A_24, B_25), k3_xboole_0(C_26, D_27)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 42.15/30.82  tff(c_25186, plain, (![B_907, B_25, B_908, D_27]: (k2_zfmisc_1(k3_xboole_0(B_907, B_25), k3_xboole_0(B_908, D_27))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_25, D_27)) | k1_xboole_0!=B_908)), inference(superposition, [status(thm), theory('equality')], [c_24642, c_28])).
% 42.15/30.82  tff(c_36046, plain, (![B_1084, B_1085, B_1086, D_1087]: (k2_zfmisc_1(k3_xboole_0(B_1084, B_1085), k3_xboole_0(B_1086, D_1087))=k1_xboole_0 | k1_xboole_0!=B_1086)), inference(demodulation, [status(thm), theory('equality')], [c_421, c_25186])).
% 42.15/30.82  tff(c_36446, plain, (![B_1088, B_1089, D_1090]: (k2_zfmisc_1(B_1088, k3_xboole_0(B_1089, D_1090))=k1_xboole_0 | k1_xboole_0!=B_1089)), inference(superposition, [status(thm), theory('equality')], [c_2932, c_36046])).
% 42.15/30.82  tff(c_36948, plain, (![B_1089, D_1090, B_1088]: (k3_xboole_0(B_1089, D_1090)=k1_xboole_0 | k1_xboole_0=B_1088 | k1_xboole_0!=B_1089)), inference(superposition, [status(thm), theory('equality')], [c_36446, c_22])).
% 42.15/30.82  tff(c_37005, plain, (![B_1094, D_1095]: (k3_xboole_0(B_1094, D_1095)=k1_xboole_0 | k1_xboole_0!=B_1094)), inference(splitLeft, [status(thm)], [c_36948])).
% 42.15/30.82  tff(c_37446, plain, (![B_1094, D_1095]: (r1_xboole_0(B_1094, D_1095) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | k1_xboole_0!=B_1094)), inference(superposition, [status(thm), theory('equality')], [c_37005, c_471])).
% 42.15/30.82  tff(c_37677, plain, (![B_1096, D_1097]: (r1_xboole_0(B_1096, D_1097) | k1_xboole_0!=B_1096)), inference(demodulation, [status(thm), theory('equality')], [c_281, c_37446])).
% 42.15/30.82  tff(c_39121, plain, (![A_1104, D_1105]: (r1_xboole_0(A_1104, D_1105) | k3_xboole_0(A_1104, D_1105)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_37677, c_14])).
% 42.15/30.82  tff(c_39215, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_39121, c_48])).
% 42.15/30.82  tff(c_24640, plain, (![B_905]: (k2_zfmisc_1(B_905, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8002, c_24561])).
% 42.15/30.82  tff(c_25189, plain, (![A_24, B_907, C_26, B_908]: (k2_zfmisc_1(k3_xboole_0(A_24, B_907), k3_xboole_0(C_26, B_908))=k3_xboole_0(k2_zfmisc_1(A_24, C_26), k1_xboole_0) | k1_xboole_0!=B_908)), inference(superposition, [status(thm), theory('equality')], [c_24642, c_28])).
% 42.15/30.82  tff(c_27122, plain, (![A_954, B_955, C_956, B_957]: (k2_zfmisc_1(k3_xboole_0(A_954, B_955), k3_xboole_0(C_956, B_957))=k1_xboole_0 | k1_xboole_0!=B_957)), inference(demodulation, [status(thm), theory('equality')], [c_7982, c_25189])).
% 42.15/30.82  tff(c_27456, plain, (![B_958, C_959, B_960]: (k2_zfmisc_1(B_958, k3_xboole_0(C_959, B_960))=k1_xboole_0 | k1_xboole_0!=B_960)), inference(superposition, [status(thm), theory('equality')], [c_2932, c_27122])).
% 42.15/30.82  tff(c_27897, plain, (![C_959, B_960, B_958]: (k3_xboole_0(C_959, B_960)=k1_xboole_0 | k1_xboole_0=B_958 | k1_xboole_0!=B_960)), inference(superposition, [status(thm), theory('equality')], [c_27456, c_22])).
% 42.15/30.82  tff(c_27959, plain, (![C_965, B_966]: (k3_xboole_0(C_965, B_966)=k1_xboole_0 | k1_xboole_0!=B_966)), inference(splitLeft, [status(thm)], [c_27897])).
% 42.15/30.82  tff(c_28345, plain, (![C_965, B_966]: (r1_xboole_0(C_965, B_966) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | k1_xboole_0!=B_966)), inference(superposition, [status(thm), theory('equality')], [c_27959, c_471])).
% 42.15/30.82  tff(c_28536, plain, (![C_965, B_966]: (r1_xboole_0(C_965, B_966) | k1_xboole_0!=B_966)), inference(demodulation, [status(thm), theory('equality')], [c_281, c_28345])).
% 42.15/30.82  tff(c_28558, plain, (![C_967, B_968]: (r1_xboole_0(C_967, B_968) | k1_xboole_0!=B_968)), inference(demodulation, [status(thm), theory('equality')], [c_281, c_28345])).
% 42.15/30.82  tff(c_28645, plain, (![C_969, B_970]: (k4_xboole_0(C_969, B_970)=C_969 | k1_xboole_0!=B_970)), inference(resolution, [status(thm)], [c_28558, c_16])).
% 42.15/30.82  tff(c_34855, plain, (![A_1048, B_1049]: (k2_xboole_0(A_1048, B_1049)=A_1048 | k1_xboole_0!=B_1049 | ~r1_xboole_0(A_1048, B_1049))), inference(superposition, [status(thm), theory('equality')], [c_20, c_28645])).
% 42.15/30.82  tff(c_34961, plain, (![C_965, B_966]: (k2_xboole_0(C_965, B_966)=C_965 | k1_xboole_0!=B_966)), inference(resolution, [status(thm)], [c_28536, c_34855])).
% 42.15/30.82  tff(c_27716, plain, (![A_24, C_959, B_960, B_958, C_26]: (k2_zfmisc_1(k3_xboole_0(A_24, B_958), k3_xboole_0(C_26, k3_xboole_0(C_959, B_960)))=k3_xboole_0(k2_zfmisc_1(A_24, C_26), k1_xboole_0) | k1_xboole_0!=B_960)), inference(superposition, [status(thm), theory('equality')], [c_27456, c_28])).
% 42.15/30.82  tff(c_62586, plain, (![B_1485, C_1482, C_1483, B_1486, A_1484]: (k2_zfmisc_1(k3_xboole_0(A_1484, B_1486), k3_xboole_0(C_1482, k3_xboole_0(C_1483, B_1485)))=k1_xboole_0 | k1_xboole_0!=B_1485)), inference(demodulation, [status(thm), theory('equality')], [c_7982, c_27716])).
% 42.15/30.82  tff(c_63331, plain, (![B_1487, C_1488, C_1489, B_1490]: (k2_zfmisc_1(B_1487, k3_xboole_0(C_1488, k3_xboole_0(C_1489, B_1490)))=k1_xboole_0 | k1_xboole_0!=B_1490)), inference(superposition, [status(thm), theory('equality')], [c_2932, c_62586])).
% 42.15/30.82  tff(c_64148, plain, (![C_1488, C_1489, B_1490, B_1487]: (k3_xboole_0(C_1488, k3_xboole_0(C_1489, B_1490))=k1_xboole_0 | k1_xboole_0=B_1487 | k1_xboole_0!=B_1490)), inference(superposition, [status(thm), theory('equality')], [c_63331, c_22])).
% 42.15/30.82  tff(c_64193, plain, (![C_1491, C_1492, B_1493]: (k3_xboole_0(C_1491, k3_xboole_0(C_1492, B_1493))=k1_xboole_0 | k1_xboole_0!=B_1493)), inference(splitLeft, [status(thm)], [c_64148])).
% 42.15/30.82  tff(c_64751, plain, (![C_1491, C_1492, B_1493]: (r1_xboole_0(C_1491, k3_xboole_0(C_1492, B_1493)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | k1_xboole_0!=B_1493)), inference(superposition, [status(thm), theory('equality')], [c_64193, c_471])).
% 42.15/30.82  tff(c_65132, plain, (![C_1494, C_1495, B_1496]: (r1_xboole_0(C_1494, k3_xboole_0(C_1495, B_1496)) | k1_xboole_0!=B_1496)), inference(demodulation, [status(thm), theory('equality')], [c_281, c_64751])).
% 42.15/30.82  tff(c_979, plain, (![C_133, A_73, A_136]: (C_133=A_73 | ~r1_xboole_0(C_133, A_136) | k2_xboole_0(A_136, A_73)!=C_133)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_964])).
% 42.15/30.82  tff(c_68084, plain, (![C_1527, A_1528, C_1529, B_1530]: (C_1527=A_1528 | k2_xboole_0(k3_xboole_0(C_1529, B_1530), A_1528)!=C_1527 | k1_xboole_0!=B_1530)), inference(resolution, [status(thm)], [c_65132, c_979])).
% 42.15/30.82  tff(c_72085, plain, (![C_1529]: (k3_xboole_0(C_1529, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34961, c_68084])).
% 42.15/30.82  tff(c_50, plain, (r1_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 42.15/30.82  tff(c_119, plain, (k4_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))=k2_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_50, c_108])).
% 42.15/30.82  tff(c_166, plain, (k4_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_1'))=k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_151])).
% 42.15/30.82  tff(c_264, plain, (k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))=k3_xboole_0(k2_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_169, c_166])).
% 42.15/30.82  tff(c_5084, plain, (![B_302, A_299, D_304, C_300, C_303, A_301]: (r1_tarski(k3_xboole_0(A_299, C_300), k2_zfmisc_1(k3_xboole_0(A_301, B_302), k3_xboole_0(C_303, D_304))) | ~r1_tarski(C_300, k2_zfmisc_1(B_302, D_304)) | ~r1_tarski(A_299, k2_zfmisc_1(A_301, C_303)))), inference(superposition, [status(thm), theory('equality')], [c_715, c_4])).
% 42.15/30.82  tff(c_5208, plain, (![A_299, C_300, A_301, B_302]: (r1_tarski(k3_xboole_0(A_299, C_300), k2_zfmisc_1(k3_xboole_0(A_301, B_302), k3_xboole_0(k2_relat_1('#skF_1'), k1_xboole_0))) | ~r1_tarski(C_300, k2_zfmisc_1(B_302, k2_relat_1('#skF_2'))) | ~r1_tarski(A_299, k2_zfmisc_1(A_301, k2_relat_1('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_264, c_5084])).
% 42.15/30.82  tff(c_141569, plain, (![A_2040, C_2041, B_2042, A_2043]: (r1_tarski(k3_xboole_0(A_2040, C_2041), k1_xboole_0) | ~r1_tarski(C_2041, k2_zfmisc_1(B_2042, k2_relat_1('#skF_2'))) | ~r1_tarski(A_2040, k2_zfmisc_1(A_2043, k2_relat_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24640, c_72085, c_5208])).
% 42.15/30.82  tff(c_141592, plain, (![A_2040, A_2043]: (r1_tarski(k3_xboole_0(A_2040, '#skF_2'), k1_xboole_0) | ~r1_tarski(A_2040, k2_zfmisc_1(A_2043, k2_relat_1('#skF_1'))) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_141569])).
% 42.15/30.82  tff(c_141599, plain, (![A_2044, A_2045]: (r1_tarski(k3_xboole_0(A_2044, '#skF_2'), k1_xboole_0) | ~r1_tarski(A_2044, k2_zfmisc_1(A_2045, k2_relat_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_141592])).
% 42.15/30.82  tff(c_141631, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_38, c_141599])).
% 42.15/30.82  tff(c_141637, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_141631])).
% 42.15/30.82  tff(c_376, plain, (![A_8, A_74]: (r1_xboole_0(A_8, A_74) | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_370, c_8])).
% 42.15/30.82  tff(c_1147, plain, (![A_154, A_153, A_155]: (A_154=A_153 | k2_xboole_0(A_155, A_154)!=A_153 | ~r1_tarski(A_153, k1_xboole_0))), inference(resolution, [status(thm)], [c_376, c_1021])).
% 42.15/30.82  tff(c_1150, plain, (![A_153]: (k1_xboole_0=A_153 | ~r1_tarski(A_153, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1147])).
% 42.15/30.82  tff(c_141700, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_141637, c_1150])).
% 42.15/30.82  tff(c_141791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39215, c_141700])).
% 42.15/30.82  tff(c_141793, plain, (![B_2046]: (k1_xboole_0=B_2046)), inference(splitRight, [status(thm)], [c_64148])).
% 42.15/30.82  tff(c_143816, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_141793, c_39215])).
% 42.15/30.82  tff(c_143818, plain, (![B_6979]: (k1_xboole_0=B_6979)), inference(splitRight, [status(thm)], [c_36948])).
% 42.15/30.82  tff(c_44, plain, (![B_38, A_37]: (k7_relat_1(B_38, A_37)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_38), A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_103])).
% 42.15/30.82  tff(c_30011, plain, (![B_977, B_978]: (k7_relat_1(B_977, B_978)=k1_xboole_0 | ~v1_relat_1(B_977) | k1_xboole_0!=B_978)), inference(resolution, [status(thm)], [c_28558, c_44])).
% 42.15/30.82  tff(c_30024, plain, (![B_979]: (k7_relat_1('#skF_2', B_979)=k1_xboole_0 | k1_xboole_0!=B_979)), inference(resolution, [status(thm)], [c_52, c_30011])).
% 42.15/30.82  tff(c_46, plain, (![B_38, A_37]: (r1_xboole_0(k1_relat_1(B_38), A_37) | k7_relat_1(B_38, A_37)!=k1_xboole_0 | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_103])).
% 42.15/30.82  tff(c_6328, plain, (![B_333, A_334, A_335]: (k1_relat_1(B_333)=k1_xboole_0 | k2_xboole_0(k1_relat_1(B_333), A_334)!=A_335 | k7_relat_1(B_333, A_335)!=k1_xboole_0 | ~v1_relat_1(B_333))), inference(resolution, [status(thm)], [c_46, c_987])).
% 42.15/30.82  tff(c_6334, plain, (![B_333, A_335]: (k1_relat_1(B_333)=k1_xboole_0 | k1_relat_1(B_333)!=A_335 | k7_relat_1(B_333, A_335)!=k1_xboole_0 | ~v1_relat_1(B_333))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6328])).
% 42.15/30.82  tff(c_30051, plain, (![B_979]: (k1_relat_1('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_2')!=B_979 | ~v1_relat_1('#skF_2') | k1_xboole_0!=B_979)), inference(superposition, [status(thm), theory('equality')], [c_30024, c_6334])).
% 42.15/30.82  tff(c_30096, plain, (![B_979]: (k1_relat_1('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_2')!=B_979 | k1_xboole_0!=B_979)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_30051])).
% 42.15/30.82  tff(c_32322, plain, (![B_979]: (k1_relat_1('#skF_2')!=B_979 | k1_xboole_0!=B_979)), inference(splitLeft, [status(thm)], [c_30096])).
% 42.15/30.82  tff(c_32326, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_32322])).
% 42.15/30.82  tff(c_145302, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_143818, c_32326])).
% 42.15/30.82  tff(c_145303, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_30096])).
% 42.15/30.82  tff(c_145389, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_145303, c_38])).
% 42.15/30.82  tff(c_145459, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_26, c_145389])).
% 42.15/30.82  tff(c_145461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9000, c_145459])).
% 42.15/30.82  tff(c_145463, plain, (![B_10633]: (k1_xboole_0=B_10633)), inference(splitRight, [status(thm)], [c_27897])).
% 42.15/30.82  tff(c_21638, plain, (![B_854]: (k2_xboole_0(B_854, B_854)=B_854 | k1_xboole_0!=B_854)), inference(demodulation, [status(thm), theory('equality')], [c_8012, c_21611])).
% 42.15/30.82  tff(c_21272, plain, (![B_847]: (k4_xboole_0(k2_xboole_0(B_847, B_847), B_847)=k2_xboole_0(B_847, B_847) | ~r1_xboole_0(B_847, B_847))), inference(resolution, [status(thm)], [c_21225, c_16])).
% 42.15/30.82  tff(c_21644, plain, (![B_854]: (k4_xboole_0(B_854, B_854)=k2_xboole_0(B_854, B_854) | ~r1_xboole_0(B_854, B_854) | k1_xboole_0!=B_854)), inference(superposition, [status(thm), theory('equality')], [c_21638, c_21272])).
% 42.15/30.82  tff(c_22766, plain, (![B_868]: (k2_xboole_0(B_868, B_868)=k1_xboole_0 | ~r1_xboole_0(B_868, B_868) | k1_xboole_0!=B_868)), inference(demodulation, [status(thm), theory('equality')], [c_8012, c_21644])).
% 42.15/30.82  tff(c_22860, plain, (![B_869]: (k2_xboole_0(B_869, B_869)=k1_xboole_0 | k1_xboole_0!=B_869)), inference(resolution, [status(thm)], [c_8002, c_22766])).
% 42.15/30.82  tff(c_285, plain, (![A_64, C_65, B_66]: (r1_xboole_0(A_64, C_65) | ~r1_xboole_0(B_66, C_65) | ~r1_tarski(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_41])).
% 42.15/30.82  tff(c_293, plain, (![A_64]: (r1_xboole_0(A_64, k2_relat_1('#skF_2')) | ~r1_tarski(A_64, k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_50, c_285])).
% 42.15/30.82  tff(c_3211, plain, (![C_221, A_222, A_223]: (k2_relat_1('#skF_2')=C_221 | ~r1_xboole_0(C_221, A_222) | k2_xboole_0(C_221, A_223)!=k2_xboole_0(A_222, k2_relat_1('#skF_2')) | ~r1_tarski(A_223, k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_293, c_956])).
% 42.15/30.82  tff(c_3219, plain, (![A_223, A_73]: (k2_relat_1('#skF_2')=k1_xboole_0 | k2_xboole_0(k1_xboole_0, A_223)!=k2_xboole_0(A_73, k2_relat_1('#skF_2')) | ~r1_tarski(A_223, k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_369, c_3211])).
% 42.15/30.82  tff(c_3234, plain, (![A_73, A_223]: (k2_relat_1('#skF_2')=k1_xboole_0 | k2_xboole_0(A_73, k2_relat_1('#skF_2'))!=A_223 | ~r1_tarski(A_223, k2_relat_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_3219])).
% 42.15/30.82  tff(c_5414, plain, (![A_73, A_223]: (k2_xboole_0(A_73, k2_relat_1('#skF_2'))!=A_223 | ~r1_tarski(A_223, k2_relat_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_3234])).
% 42.15/30.82  tff(c_5419, plain, (![A_73]: (~r1_tarski(k2_xboole_0(A_73, k2_relat_1('#skF_2')), k2_relat_1('#skF_1')))), inference(reflexivity, [status(thm), theory('equality')], [c_5414])).
% 42.15/30.82  tff(c_23066, plain, (~r1_tarski(k1_xboole_0, k2_relat_1('#skF_1')) | k2_relat_1('#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22860, c_5419])).
% 42.15/30.82  tff(c_23524, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_23066])).
% 42.15/30.82  tff(c_146849, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_145463, c_23524])).
% 42.15/30.82  tff(c_146851, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_23066])).
% 42.15/30.82  tff(c_147083, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k1_xboole_0)) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_146851, c_38])).
% 42.15/30.82  tff(c_147091, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_24, c_147083])).
% 42.15/30.82  tff(c_147093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9000, c_147091])).
% 42.15/30.82  tff(c_147530, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_7834])).
% 42.15/30.82  tff(c_147531, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_147530, c_281])).
% 42.15/30.82  tff(c_147690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_473, c_147531])).
% 42.15/30.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.15/30.82  
% 42.15/30.82  Inference rules
% 42.15/30.82  ----------------------
% 42.15/30.82  #Ref     : 68
% 42.15/30.82  #Sup     : 41978
% 42.15/30.82  #Fact    : 0
% 42.15/30.82  #Define  : 0
% 42.15/30.82  #Split   : 33
% 42.15/30.82  #Chain   : 0
% 42.15/30.82  #Close   : 0
% 42.15/30.82  
% 42.15/30.82  Ordering : KBO
% 42.15/30.82  
% 42.15/30.82  Simplification rules
% 42.15/30.82  ----------------------
% 42.15/30.82  #Subsume      : 17996
% 42.15/30.82  #Demod        : 17998
% 42.15/30.82  #Tautology    : 7749
% 42.15/30.82  #SimpNegUnit  : 1070
% 42.15/30.82  #BackRed      : 559
% 42.15/30.82  
% 42.15/30.82  #Partial instantiations: 2066
% 42.15/30.82  #Strategies tried      : 1
% 42.15/30.82  
% 42.15/30.82  Timing (in seconds)
% 42.15/30.82  ----------------------
% 42.15/30.82  Preprocessing        : 0.32
% 42.15/30.82  Parsing              : 0.18
% 42.15/30.82  CNF conversion       : 0.02
% 42.15/30.82  Main loop            : 29.71
% 42.15/30.82  Inferencing          : 3.40
% 42.15/30.82  Reduction            : 11.29
% 42.15/30.82  Demodulation         : 9.26
% 42.15/30.82  BG Simplification    : 0.41
% 42.15/30.82  Subsumption          : 12.77
% 42.15/30.82  Abstraction          : 0.67
% 42.15/30.82  MUC search           : 0.00
% 42.15/30.82  Cooper               : 0.00
% 42.15/30.82  Total                : 30.11
% 42.15/30.82  Index Insertion      : 0.00
% 42.15/30.82  Index Deletion       : 0.00
% 42.15/30.82  Index Matching       : 0.00
% 42.15/30.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
