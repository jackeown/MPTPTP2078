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
% DateTime   : Thu Dec  3 10:03:32 EST 2020

% Result     : Theorem 13.98s
% Output     : CNFRefutation 14.17s
% Verified   : 
% Statistics : Number of formulae       :  149 (1811 expanded)
%              Number of leaves         :   41 ( 671 expanded)
%              Depth                    :   17
%              Number of atoms          :  259 (3053 expanded)
%              Number of equality atoms :   97 (1081 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_47,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_89,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_18,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,(
    ! [A_60,B_61] :
      ( k5_relat_1(k6_relat_1(A_60),B_61) = k7_relat_1(B_61,A_60)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_190,plain,(
    ! [B_81,A_82] :
      ( k5_relat_1(B_81,k6_relat_1(A_82)) = k8_relat_1(A_82,B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_218,plain,(
    ! [A_82,A_60] :
      ( k8_relat_1(A_82,k6_relat_1(A_60)) = k7_relat_1(k6_relat_1(A_82),A_60)
      | ~ v1_relat_1(k6_relat_1(A_60))
      | ~ v1_relat_1(k6_relat_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_190])).

tff(c_256,plain,(
    ! [A_86,A_87] : k8_relat_1(A_86,k6_relat_1(A_87)) = k7_relat_1(k6_relat_1(A_86),A_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_218])).

tff(c_16,plain,(
    ! [A_30,B_31] :
      ( v1_relat_1(k5_relat_1(A_30,B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_211,plain,(
    ! [A_82,B_81] :
      ( v1_relat_1(k8_relat_1(A_82,B_81))
      | ~ v1_relat_1(k6_relat_1(A_82))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_16])).

tff(c_233,plain,(
    ! [A_82,B_81] :
      ( v1_relat_1(k8_relat_1(A_82,B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_211])).

tff(c_266,plain,(
    ! [A_86,A_87] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_86),A_87))
      | ~ v1_relat_1(k6_relat_1(A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_233])).

tff(c_276,plain,(
    ! [A_86,A_87] : v1_relat_1(k7_relat_1(k6_relat_1(A_86),A_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_266])).

tff(c_236,plain,(
    ! [A_82,A_60] : k8_relat_1(A_82,k6_relat_1(A_60)) = k7_relat_1(k6_relat_1(A_82),A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_218])).

tff(c_22,plain,(
    ! [B_38,A_37] :
      ( k5_relat_1(B_38,k6_relat_1(A_37)) = k8_relat_1(A_37,B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [A_52] : k4_relat_1(k6_relat_1(A_52)) = k6_relat_1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_851,plain,(
    ! [B_139,A_140] :
      ( k5_relat_1(k4_relat_1(B_139),k4_relat_1(A_140)) = k4_relat_1(k5_relat_1(A_140,B_139))
      | ~ v1_relat_1(B_139)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_866,plain,(
    ! [A_52,A_140] :
      ( k5_relat_1(k6_relat_1(A_52),k4_relat_1(A_140)) = k4_relat_1(k5_relat_1(A_140,k6_relat_1(A_52)))
      | ~ v1_relat_1(k6_relat_1(A_52))
      | ~ v1_relat_1(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_851])).

tff(c_1872,plain,(
    ! [A_199,A_200] :
      ( k5_relat_1(k6_relat_1(A_199),k4_relat_1(A_200)) = k4_relat_1(k5_relat_1(A_200,k6_relat_1(A_199)))
      | ~ v1_relat_1(A_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_866])).

tff(c_1908,plain,(
    ! [A_52,A_199] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_52),k6_relat_1(A_199))) = k5_relat_1(k6_relat_1(A_199),k6_relat_1(A_52))
      | ~ v1_relat_1(k6_relat_1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1872])).

tff(c_1971,plain,(
    ! [A_205,A_206] : k4_relat_1(k5_relat_1(k6_relat_1(A_205),k6_relat_1(A_206))) = k5_relat_1(k6_relat_1(A_206),k6_relat_1(A_205)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1908])).

tff(c_2004,plain,(
    ! [A_206,A_60] :
      ( k5_relat_1(k6_relat_1(A_206),k6_relat_1(A_60)) = k4_relat_1(k7_relat_1(k6_relat_1(A_206),A_60))
      | ~ v1_relat_1(k6_relat_1(A_206)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1971])).

tff(c_2120,plain,(
    ! [A_211,A_212] : k5_relat_1(k6_relat_1(A_211),k6_relat_1(A_212)) = k4_relat_1(k7_relat_1(k6_relat_1(A_211),A_212)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2004])).

tff(c_2170,plain,(
    ! [A_211,A_37] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_211),A_37)) = k8_relat_1(A_37,k6_relat_1(A_211))
      | ~ v1_relat_1(k6_relat_1(A_211)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2120])).

tff(c_2208,plain,(
    ! [A_211,A_37] : k4_relat_1(k7_relat_1(k6_relat_1(A_211),A_37)) = k7_relat_1(k6_relat_1(A_37),A_211) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_236,c_2170])).

tff(c_34,plain,(
    ! [A_51] : k2_relat_1(k6_relat_1(A_51)) = A_51 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_98,plain,(
    ! [A_74] :
      ( k5_relat_1(A_74,k6_relat_1(k2_relat_1(A_74))) = A_74
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_110,plain,(
    ! [A_51] :
      ( k5_relat_1(k6_relat_1(A_51),k6_relat_1(A_51)) = k6_relat_1(A_51)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_98])).

tff(c_116,plain,(
    ! [A_51] : k5_relat_1(k6_relat_1(A_51),k6_relat_1(A_51)) = k6_relat_1(A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_110])).

tff(c_1429,plain,(
    ! [B_169,C_170,A_171] :
      ( k7_relat_1(k5_relat_1(B_169,C_170),A_171) = k5_relat_1(k7_relat_1(B_169,A_171),C_170)
      | ~ v1_relat_1(C_170)
      | ~ v1_relat_1(B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1480,plain,(
    ! [A_51,A_171] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_51),A_171),k6_relat_1(A_51)) = k7_relat_1(k6_relat_1(A_51),A_171)
      | ~ v1_relat_1(k6_relat_1(A_51))
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_1429])).

tff(c_1497,plain,(
    ! [A_51,A_171] : k5_relat_1(k7_relat_1(k6_relat_1(A_51),A_171),k6_relat_1(A_51)) = k7_relat_1(k6_relat_1(A_51),A_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_1480])).

tff(c_26,plain,(
    ! [B_44,A_43] :
      ( k2_relat_1(k7_relat_1(B_44,A_43)) = k9_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10058,plain,(
    ! [B_431,A_432,C_433] :
      ( k2_relat_1(k5_relat_1(k7_relat_1(B_431,A_432),C_433)) = k9_relat_1(k5_relat_1(B_431,C_433),A_432)
      | ~ v1_relat_1(k5_relat_1(B_431,C_433))
      | ~ v1_relat_1(C_433)
      | ~ v1_relat_1(B_431) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1429,c_26])).

tff(c_10131,plain,(
    ! [A_51,A_171] :
      ( k9_relat_1(k5_relat_1(k6_relat_1(A_51),k6_relat_1(A_51)),A_171) = k2_relat_1(k7_relat_1(k6_relat_1(A_51),A_171))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_51),k6_relat_1(A_51)))
      | ~ v1_relat_1(k6_relat_1(A_51))
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_10058])).

tff(c_10176,plain,(
    ! [A_51,A_171] : k2_relat_1(k7_relat_1(k6_relat_1(A_51),A_171)) = k9_relat_1(k6_relat_1(A_51),A_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_18,c_116,c_116,c_10131])).

tff(c_32,plain,(
    ! [A_51] : k1_relat_1(k6_relat_1(A_51)) = A_51 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42,plain,(
    ! [B_57,A_56] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_57,A_56)),k1_relat_1(B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_458,plain,(
    ! [A_111,B_112] :
      ( k5_relat_1(k6_relat_1(A_111),B_112) = B_112
      | ~ r1_tarski(k1_relat_1(B_112),A_111)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5950,plain,(
    ! [B_345,A_346] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_345)),k7_relat_1(B_345,A_346)) = k7_relat_1(B_345,A_346)
      | ~ v1_relat_1(k7_relat_1(B_345,A_346))
      | ~ v1_relat_1(B_345) ) ),
    inference(resolution,[status(thm)],[c_42,c_458])).

tff(c_6034,plain,(
    ! [A_51,A_346] :
      ( k5_relat_1(k6_relat_1(A_51),k7_relat_1(k6_relat_1(A_51),A_346)) = k7_relat_1(k6_relat_1(A_51),A_346)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_51),A_346))
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5950])).

tff(c_11204,plain,(
    ! [A_455,A_456] : k5_relat_1(k6_relat_1(A_455),k7_relat_1(k6_relat_1(A_455),A_456)) = k7_relat_1(k6_relat_1(A_455),A_456) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_276,c_6034])).

tff(c_28,plain,(
    ! [A_45,B_47] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_45,B_47)),k2_relat_1(B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_857,plain,(
    ! [A_140,B_139] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_140,B_139))),k2_relat_1(k4_relat_1(A_140)))
      | ~ v1_relat_1(k4_relat_1(A_140))
      | ~ v1_relat_1(k4_relat_1(B_139))
      | ~ v1_relat_1(B_139)
      | ~ v1_relat_1(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_28])).

tff(c_11213,plain,(
    ! [A_455,A_456] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_455),A_456))),k2_relat_1(k4_relat_1(k6_relat_1(A_455))))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(A_455)))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_455),A_456)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_455),A_456))
      | ~ v1_relat_1(k6_relat_1(A_455)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11204,c_857])).

tff(c_11333,plain,(
    ! [A_457,A_458] : r1_tarski(k9_relat_1(k6_relat_1(A_457),A_458),A_458) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_276,c_276,c_2208,c_18,c_36,c_10176,c_2208,c_34,c_36,c_11213])).

tff(c_412,plain,(
    ! [B_106,A_107] :
      ( k7_relat_1(B_106,A_107) = B_106
      | ~ r1_tarski(k1_relat_1(B_106),A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_425,plain,(
    ! [A_51,A_107] :
      ( k7_relat_1(k6_relat_1(A_51),A_107) = k6_relat_1(A_51)
      | ~ r1_tarski(A_51,A_107)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_412])).

tff(c_562,plain,(
    ! [A_115,A_116] :
      ( k7_relat_1(k6_relat_1(A_115),A_116) = k6_relat_1(A_115)
      | ~ r1_tarski(A_115,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_425])).

tff(c_369,plain,(
    ! [B_102,A_103] :
      ( k3_xboole_0(k1_relat_1(B_102),A_103) = k1_relat_1(k7_relat_1(B_102,A_103))
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_378,plain,(
    ! [A_51,A_103] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_51),A_103)) = k3_xboole_0(A_51,A_103)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_369])).

tff(c_382,plain,(
    ! [A_51,A_103] : k1_relat_1(k7_relat_1(k6_relat_1(A_51),A_103)) = k3_xboole_0(A_51,A_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_378])).

tff(c_572,plain,(
    ! [A_115,A_116] :
      ( k3_xboole_0(A_115,A_116) = k1_relat_1(k6_relat_1(A_115))
      | ~ r1_tarski(A_115,A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_382])).

tff(c_605,plain,(
    ! [A_115,A_116] :
      ( k3_xboole_0(A_115,A_116) = A_115
      | ~ r1_tarski(A_115,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_572])).

tff(c_11401,plain,(
    ! [A_457,A_458] : k3_xboole_0(k9_relat_1(k6_relat_1(A_457),A_458),A_458) = k9_relat_1(k6_relat_1(A_457),A_458) ),
    inference(resolution,[status(thm)],[c_11333,c_605])).

tff(c_697,plain,(
    ! [A_127,B_128] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_127,B_128)),k2_relat_1(B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_709,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_37,B_38)),k2_relat_1(k6_relat_1(A_37)))
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_697])).

tff(c_735,plain,(
    ! [A_129,B_130] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_129,B_130)),A_129)
      | ~ v1_relat_1(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_34,c_709])).

tff(c_744,plain,(
    ! [A_82,A_60] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_82),A_60)),A_82)
      | ~ v1_relat_1(k6_relat_1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_735])).

tff(c_754,plain,(
    ! [A_131,A_132] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_131),A_132)),A_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_744])).

tff(c_768,plain,(
    ! [A_131,A_43] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_131),A_43),A_131)
      | ~ v1_relat_1(k6_relat_1(A_131)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_754])).

tff(c_779,plain,(
    ! [A_133,A_134] : r1_tarski(k9_relat_1(k6_relat_1(A_133),A_134),A_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_768])).

tff(c_789,plain,(
    ! [A_133,A_134] : k3_xboole_0(k9_relat_1(k6_relat_1(A_133),A_134),A_133) = k9_relat_1(k6_relat_1(A_133),A_134) ),
    inference(resolution,[status(thm)],[c_779,c_605])).

tff(c_1477,plain,(
    ! [A_60,A_171,B_61] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_60),A_171),B_61) = k7_relat_1(k7_relat_1(B_61,A_60),A_171)
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(k6_relat_1(A_60))
      | ~ v1_relat_1(B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1429])).

tff(c_1495,plain,(
    ! [A_60,A_171,B_61] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_60),A_171),B_61) = k7_relat_1(k7_relat_1(B_61,A_60),A_171)
      | ~ v1_relat_1(B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1477])).

tff(c_302,plain,(
    ! [B_95,A_96] :
      ( k2_relat_1(k7_relat_1(B_95,A_96)) = k9_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    ! [A_55] :
      ( k5_relat_1(A_55,k6_relat_1(k2_relat_1(A_55))) = A_55
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6597,plain,(
    ! [B_359,A_360] :
      ( k5_relat_1(k7_relat_1(B_359,A_360),k6_relat_1(k9_relat_1(B_359,A_360))) = k7_relat_1(B_359,A_360)
      | ~ v1_relat_1(k7_relat_1(B_359,A_360))
      | ~ v1_relat_1(B_359) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_40])).

tff(c_6657,plain,(
    ! [A_60,A_171] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_60),A_171)),A_60),A_171) = k7_relat_1(k6_relat_1(A_60),A_171)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_60),A_171))
      | ~ v1_relat_1(k6_relat_1(A_60))
      | ~ v1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_60),A_171))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1495,c_6597])).

tff(c_26778,plain,(
    ! [A_654,A_655] : k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_654),A_655)),A_654),A_655) = k7_relat_1(k6_relat_1(A_654),A_655) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_276,c_6657])).

tff(c_384,plain,(
    ! [A_104,A_105] : k1_relat_1(k7_relat_1(k6_relat_1(A_104),A_105)) = k3_xboole_0(A_104,A_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_378])).

tff(c_44,plain,(
    ! [B_59,A_58] :
      ( k3_xboole_0(k1_relat_1(B_59),A_58) = k1_relat_1(k7_relat_1(B_59,A_58))
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_390,plain,(
    ! [A_104,A_105,A_58] :
      ( k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_104),A_105),A_58)) = k3_xboole_0(k3_xboole_0(A_104,A_105),A_58)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_104),A_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_44])).

tff(c_405,plain,(
    ! [A_104,A_105,A_58] : k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_104),A_105),A_58)) = k3_xboole_0(k3_xboole_0(A_104,A_105),A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_390])).

tff(c_26806,plain,(
    ! [A_654,A_655] : k3_xboole_0(k3_xboole_0(k9_relat_1(k6_relat_1(A_654),A_655),A_654),A_655) = k1_relat_1(k7_relat_1(k6_relat_1(A_654),A_655)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26778,c_405])).

tff(c_27018,plain,(
    ! [A_654,A_655] : k9_relat_1(k6_relat_1(A_654),A_655) = k3_xboole_0(A_654,A_655) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11401,c_789,c_382,c_26806])).

tff(c_11297,plain,(
    ! [A_456,A_455] : r1_tarski(k9_relat_1(k6_relat_1(A_456),A_455),A_455) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_276,c_276,c_2208,c_18,c_36,c_10176,c_2208,c_34,c_36,c_11213])).

tff(c_27141,plain,(
    ! [A_456,A_455] : r1_tarski(k3_xboole_0(A_456,A_455),A_455) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27018,c_11297])).

tff(c_285,plain,(
    ! [B_90,A_91] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_90,A_91)),k1_relat_1(B_90))
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_291,plain,(
    ! [A_51,A_91] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_51),A_91)),A_51)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_285])).

tff(c_295,plain,(
    ! [A_51,A_91] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_51),A_91)),A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_291])).

tff(c_383,plain,(
    ! [A_51,A_91] : r1_tarski(k3_xboole_0(A_51,A_91),A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_295])).

tff(c_27143,plain,(
    ! [A_51,A_171] : k2_relat_1(k7_relat_1(k6_relat_1(A_51),A_171)) = k3_xboole_0(A_51,A_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27018,c_10176])).

tff(c_1227,plain,(
    ! [A_160,B_161,C_162] :
      ( k8_relat_1(A_160,k5_relat_1(B_161,C_162)) = k5_relat_1(B_161,k8_relat_1(A_160,C_162))
      | ~ v1_relat_1(C_162)
      | ~ v1_relat_1(B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1259,plain,(
    ! [B_38,A_160,A_37] :
      ( k5_relat_1(B_38,k8_relat_1(A_160,k6_relat_1(A_37))) = k8_relat_1(A_160,k8_relat_1(A_37,B_38))
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1227])).

tff(c_1276,plain,(
    ! [B_38,A_160,A_37] :
      ( k5_relat_1(B_38,k7_relat_1(k6_relat_1(A_160),A_37)) = k8_relat_1(A_160,k8_relat_1(A_37,B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_236,c_1259])).

tff(c_5960,plain,(
    ! [A_160,A_346] :
      ( k8_relat_1(A_160,k8_relat_1(A_346,k6_relat_1(k1_relat_1(k6_relat_1(A_160))))) = k7_relat_1(k6_relat_1(A_160),A_346)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_160))))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_160),A_346))
      | ~ v1_relat_1(k6_relat_1(A_160)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5950,c_1276])).

tff(c_6039,plain,(
    ! [A_160,A_346] : k8_relat_1(A_160,k7_relat_1(k6_relat_1(A_346),A_160)) = k7_relat_1(k6_relat_1(A_160),A_346) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_276,c_18,c_236,c_32,c_5960])).

tff(c_6072,plain,(
    ! [A_51,A_346] : k5_relat_1(k6_relat_1(A_51),k7_relat_1(k6_relat_1(A_51),A_346)) = k7_relat_1(k6_relat_1(A_51),A_346) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_276,c_6034])).

tff(c_869,plain,(
    ! [B_139,A_52] :
      ( k5_relat_1(k4_relat_1(B_139),k6_relat_1(A_52)) = k4_relat_1(k5_relat_1(k6_relat_1(A_52),B_139))
      | ~ v1_relat_1(B_139)
      | ~ v1_relat_1(k6_relat_1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_851])).

tff(c_2026,plain,(
    ! [B_207,A_208] :
      ( k5_relat_1(k4_relat_1(B_207),k6_relat_1(A_208)) = k4_relat_1(k5_relat_1(k6_relat_1(A_208),B_207))
      | ~ v1_relat_1(B_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_869])).

tff(c_36418,plain,(
    ! [A_772,B_773] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_772),B_773)) = k8_relat_1(A_772,k4_relat_1(B_773))
      | ~ v1_relat_1(k4_relat_1(B_773))
      | ~ v1_relat_1(B_773) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2026,c_22])).

tff(c_36488,plain,(
    ! [A_51,A_346] :
      ( k8_relat_1(A_51,k4_relat_1(k7_relat_1(k6_relat_1(A_51),A_346))) = k4_relat_1(k7_relat_1(k6_relat_1(A_51),A_346))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_51),A_346)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_51),A_346)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6072,c_36418])).

tff(c_36543,plain,(
    ! [A_51,A_346] : k7_relat_1(k6_relat_1(A_51),A_346) = k7_relat_1(k6_relat_1(A_346),A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_276,c_2208,c_6039,c_2208,c_2208,c_36488])).

tff(c_471,plain,(
    ! [A_111,A_51] :
      ( k5_relat_1(k6_relat_1(A_111),k6_relat_1(A_51)) = k6_relat_1(A_51)
      | ~ r1_tarski(A_51,A_111)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_458])).

tff(c_477,plain,(
    ! [A_111,A_51] :
      ( k5_relat_1(k6_relat_1(A_111),k6_relat_1(A_51)) = k6_relat_1(A_51)
      | ~ r1_tarski(A_51,A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_471])).

tff(c_1461,plain,(
    ! [A_111,A_171,A_51] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_111),A_171),k6_relat_1(A_51)) = k7_relat_1(k6_relat_1(A_51),A_171)
      | ~ v1_relat_1(k6_relat_1(A_51))
      | ~ v1_relat_1(k6_relat_1(A_111))
      | ~ r1_tarski(A_51,A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_1429])).

tff(c_43511,plain,(
    ! [A_848,A_849,A_850] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_848),A_849),k6_relat_1(A_850)) = k7_relat_1(k6_relat_1(A_850),A_849)
      | ~ r1_tarski(A_850,A_848) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_1461])).

tff(c_43585,plain,(
    ! [A_848,A_849] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_848),A_849))),A_849) = k7_relat_1(k6_relat_1(A_848),A_849)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_848),A_849))
      | ~ r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_848),A_849)),A_848) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43511,c_40])).

tff(c_44585,plain,(
    ! [A_860,A_861] : k7_relat_1(k6_relat_1(A_860),k3_xboole_0(A_861,A_860)) = k7_relat_1(k6_relat_1(A_861),A_860) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_27143,c_276,c_36543,c_27143,c_43585])).

tff(c_431,plain,(
    ! [A_51,A_107] :
      ( k7_relat_1(k6_relat_1(A_51),A_107) = k6_relat_1(A_51)
      | ~ r1_tarski(A_51,A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_425])).

tff(c_2259,plain,(
    ! [A_217,A_218] : k4_relat_1(k7_relat_1(k6_relat_1(A_217),A_218)) = k7_relat_1(k6_relat_1(A_218),A_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_236,c_2170])).

tff(c_2280,plain,(
    ! [A_107,A_51] :
      ( k7_relat_1(k6_relat_1(A_107),A_51) = k4_relat_1(k6_relat_1(A_51))
      | ~ r1_tarski(A_51,A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_2259])).

tff(c_2298,plain,(
    ! [A_107,A_51] :
      ( k7_relat_1(k6_relat_1(A_107),A_51) = k6_relat_1(A_51)
      | ~ r1_tarski(A_51,A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2280])).

tff(c_44797,plain,(
    ! [A_861,A_860] :
      ( k7_relat_1(k6_relat_1(A_861),A_860) = k6_relat_1(k3_xboole_0(A_861,A_860))
      | ~ r1_tarski(k3_xboole_0(A_861,A_860),A_860) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44585,c_2298])).

tff(c_45058,plain,(
    ! [A_861,A_860] : k7_relat_1(k6_relat_1(A_861),A_860) = k6_relat_1(k3_xboole_0(A_861,A_860)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27141,c_44797])).

tff(c_131,plain,(
    ! [A_76,B_77] :
      ( k5_relat_1(k6_relat_1(A_76),B_77) = k7_relat_1(B_77,A_76)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_137,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_50])).

tff(c_161,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_137])).

tff(c_45174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45058,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:58:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.98/6.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.98/6.72  
% 13.98/6.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.98/6.72  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 13.98/6.72  
% 13.98/6.72  %Foreground sorts:
% 13.98/6.72  
% 13.98/6.72  
% 13.98/6.72  %Background operators:
% 13.98/6.72  
% 13.98/6.72  
% 13.98/6.72  %Foreground operators:
% 13.98/6.72  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 13.98/6.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.98/6.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.98/6.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.98/6.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.98/6.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.98/6.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.98/6.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.98/6.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.98/6.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.98/6.72  tff('#skF_2', type, '#skF_2': $i).
% 13.98/6.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.98/6.72  tff('#skF_1', type, '#skF_1': $i).
% 13.98/6.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.98/6.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.98/6.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.98/6.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.98/6.72  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.98/6.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.98/6.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.98/6.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.98/6.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.98/6.72  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 13.98/6.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.98/6.72  
% 14.17/6.75  tff(f_47, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 14.17/6.75  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 14.17/6.75  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 14.17/6.75  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 14.17/6.75  tff(f_89, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 14.17/6.75  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 14.17/6.75  tff(f_87, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 14.17/6.75  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 14.17/6.75  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 14.17/6.75  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 14.17/6.75  tff(f_103, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 14.17/6.75  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 14.17/6.75  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 14.17/6.75  tff(f_117, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 14.17/6.75  tff(f_107, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 14.17/6.75  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_relat_1)).
% 14.17/6.75  tff(f_120, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 14.17/6.75  tff(c_18, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.17/6.75  tff(c_46, plain, (![A_60, B_61]: (k5_relat_1(k6_relat_1(A_60), B_61)=k7_relat_1(B_61, A_60) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.17/6.75  tff(c_190, plain, (![B_81, A_82]: (k5_relat_1(B_81, k6_relat_1(A_82))=k8_relat_1(A_82, B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.17/6.75  tff(c_218, plain, (![A_82, A_60]: (k8_relat_1(A_82, k6_relat_1(A_60))=k7_relat_1(k6_relat_1(A_82), A_60) | ~v1_relat_1(k6_relat_1(A_60)) | ~v1_relat_1(k6_relat_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_190])).
% 14.17/6.75  tff(c_256, plain, (![A_86, A_87]: (k8_relat_1(A_86, k6_relat_1(A_87))=k7_relat_1(k6_relat_1(A_86), A_87))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_218])).
% 14.17/6.75  tff(c_16, plain, (![A_30, B_31]: (v1_relat_1(k5_relat_1(A_30, B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.17/6.75  tff(c_211, plain, (![A_82, B_81]: (v1_relat_1(k8_relat_1(A_82, B_81)) | ~v1_relat_1(k6_relat_1(A_82)) | ~v1_relat_1(B_81) | ~v1_relat_1(B_81))), inference(superposition, [status(thm), theory('equality')], [c_190, c_16])).
% 14.17/6.75  tff(c_233, plain, (![A_82, B_81]: (v1_relat_1(k8_relat_1(A_82, B_81)) | ~v1_relat_1(B_81))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_211])).
% 14.17/6.75  tff(c_266, plain, (![A_86, A_87]: (v1_relat_1(k7_relat_1(k6_relat_1(A_86), A_87)) | ~v1_relat_1(k6_relat_1(A_87)))), inference(superposition, [status(thm), theory('equality')], [c_256, c_233])).
% 14.17/6.75  tff(c_276, plain, (![A_86, A_87]: (v1_relat_1(k7_relat_1(k6_relat_1(A_86), A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_266])).
% 14.17/6.75  tff(c_236, plain, (![A_82, A_60]: (k8_relat_1(A_82, k6_relat_1(A_60))=k7_relat_1(k6_relat_1(A_82), A_60))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_218])).
% 14.17/6.75  tff(c_22, plain, (![B_38, A_37]: (k5_relat_1(B_38, k6_relat_1(A_37))=k8_relat_1(A_37, B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.17/6.75  tff(c_36, plain, (![A_52]: (k4_relat_1(k6_relat_1(A_52))=k6_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.17/6.75  tff(c_851, plain, (![B_139, A_140]: (k5_relat_1(k4_relat_1(B_139), k4_relat_1(A_140))=k4_relat_1(k5_relat_1(A_140, B_139)) | ~v1_relat_1(B_139) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.17/6.75  tff(c_866, plain, (![A_52, A_140]: (k5_relat_1(k6_relat_1(A_52), k4_relat_1(A_140))=k4_relat_1(k5_relat_1(A_140, k6_relat_1(A_52))) | ~v1_relat_1(k6_relat_1(A_52)) | ~v1_relat_1(A_140))), inference(superposition, [status(thm), theory('equality')], [c_36, c_851])).
% 14.17/6.75  tff(c_1872, plain, (![A_199, A_200]: (k5_relat_1(k6_relat_1(A_199), k4_relat_1(A_200))=k4_relat_1(k5_relat_1(A_200, k6_relat_1(A_199))) | ~v1_relat_1(A_200))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_866])).
% 14.17/6.75  tff(c_1908, plain, (![A_52, A_199]: (k4_relat_1(k5_relat_1(k6_relat_1(A_52), k6_relat_1(A_199)))=k5_relat_1(k6_relat_1(A_199), k6_relat_1(A_52)) | ~v1_relat_1(k6_relat_1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1872])).
% 14.17/6.75  tff(c_1971, plain, (![A_205, A_206]: (k4_relat_1(k5_relat_1(k6_relat_1(A_205), k6_relat_1(A_206)))=k5_relat_1(k6_relat_1(A_206), k6_relat_1(A_205)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1908])).
% 14.17/6.75  tff(c_2004, plain, (![A_206, A_60]: (k5_relat_1(k6_relat_1(A_206), k6_relat_1(A_60))=k4_relat_1(k7_relat_1(k6_relat_1(A_206), A_60)) | ~v1_relat_1(k6_relat_1(A_206)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1971])).
% 14.17/6.75  tff(c_2120, plain, (![A_211, A_212]: (k5_relat_1(k6_relat_1(A_211), k6_relat_1(A_212))=k4_relat_1(k7_relat_1(k6_relat_1(A_211), A_212)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2004])).
% 14.17/6.75  tff(c_2170, plain, (![A_211, A_37]: (k4_relat_1(k7_relat_1(k6_relat_1(A_211), A_37))=k8_relat_1(A_37, k6_relat_1(A_211)) | ~v1_relat_1(k6_relat_1(A_211)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2120])).
% 14.17/6.75  tff(c_2208, plain, (![A_211, A_37]: (k4_relat_1(k7_relat_1(k6_relat_1(A_211), A_37))=k7_relat_1(k6_relat_1(A_37), A_211))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_236, c_2170])).
% 14.17/6.75  tff(c_34, plain, (![A_51]: (k2_relat_1(k6_relat_1(A_51))=A_51)), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.17/6.75  tff(c_98, plain, (![A_74]: (k5_relat_1(A_74, k6_relat_1(k2_relat_1(A_74)))=A_74 | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.17/6.75  tff(c_110, plain, (![A_51]: (k5_relat_1(k6_relat_1(A_51), k6_relat_1(A_51))=k6_relat_1(A_51) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_98])).
% 14.17/6.75  tff(c_116, plain, (![A_51]: (k5_relat_1(k6_relat_1(A_51), k6_relat_1(A_51))=k6_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_110])).
% 14.17/6.75  tff(c_1429, plain, (![B_169, C_170, A_171]: (k7_relat_1(k5_relat_1(B_169, C_170), A_171)=k5_relat_1(k7_relat_1(B_169, A_171), C_170) | ~v1_relat_1(C_170) | ~v1_relat_1(B_169))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.17/6.75  tff(c_1480, plain, (![A_51, A_171]: (k5_relat_1(k7_relat_1(k6_relat_1(A_51), A_171), k6_relat_1(A_51))=k7_relat_1(k6_relat_1(A_51), A_171) | ~v1_relat_1(k6_relat_1(A_51)) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_1429])).
% 14.17/6.75  tff(c_1497, plain, (![A_51, A_171]: (k5_relat_1(k7_relat_1(k6_relat_1(A_51), A_171), k6_relat_1(A_51))=k7_relat_1(k6_relat_1(A_51), A_171))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_1480])).
% 14.17/6.75  tff(c_26, plain, (![B_44, A_43]: (k2_relat_1(k7_relat_1(B_44, A_43))=k9_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.17/6.75  tff(c_10058, plain, (![B_431, A_432, C_433]: (k2_relat_1(k5_relat_1(k7_relat_1(B_431, A_432), C_433))=k9_relat_1(k5_relat_1(B_431, C_433), A_432) | ~v1_relat_1(k5_relat_1(B_431, C_433)) | ~v1_relat_1(C_433) | ~v1_relat_1(B_431))), inference(superposition, [status(thm), theory('equality')], [c_1429, c_26])).
% 14.17/6.75  tff(c_10131, plain, (![A_51, A_171]: (k9_relat_1(k5_relat_1(k6_relat_1(A_51), k6_relat_1(A_51)), A_171)=k2_relat_1(k7_relat_1(k6_relat_1(A_51), A_171)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_51), k6_relat_1(A_51))) | ~v1_relat_1(k6_relat_1(A_51)) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_10058])).
% 14.17/6.75  tff(c_10176, plain, (![A_51, A_171]: (k2_relat_1(k7_relat_1(k6_relat_1(A_51), A_171))=k9_relat_1(k6_relat_1(A_51), A_171))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_18, c_116, c_116, c_10131])).
% 14.17/6.75  tff(c_32, plain, (![A_51]: (k1_relat_1(k6_relat_1(A_51))=A_51)), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.17/6.75  tff(c_42, plain, (![B_57, A_56]: (r1_tarski(k1_relat_1(k7_relat_1(B_57, A_56)), k1_relat_1(B_57)) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_103])).
% 14.17/6.75  tff(c_458, plain, (![A_111, B_112]: (k5_relat_1(k6_relat_1(A_111), B_112)=B_112 | ~r1_tarski(k1_relat_1(B_112), A_111) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.17/6.75  tff(c_5950, plain, (![B_345, A_346]: (k5_relat_1(k6_relat_1(k1_relat_1(B_345)), k7_relat_1(B_345, A_346))=k7_relat_1(B_345, A_346) | ~v1_relat_1(k7_relat_1(B_345, A_346)) | ~v1_relat_1(B_345))), inference(resolution, [status(thm)], [c_42, c_458])).
% 14.17/6.75  tff(c_6034, plain, (![A_51, A_346]: (k5_relat_1(k6_relat_1(A_51), k7_relat_1(k6_relat_1(A_51), A_346))=k7_relat_1(k6_relat_1(A_51), A_346) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_51), A_346)) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_5950])).
% 14.17/6.75  tff(c_11204, plain, (![A_455, A_456]: (k5_relat_1(k6_relat_1(A_455), k7_relat_1(k6_relat_1(A_455), A_456))=k7_relat_1(k6_relat_1(A_455), A_456))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_276, c_6034])).
% 14.17/6.75  tff(c_28, plain, (![A_45, B_47]: (r1_tarski(k2_relat_1(k5_relat_1(A_45, B_47)), k2_relat_1(B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.17/6.75  tff(c_857, plain, (![A_140, B_139]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_140, B_139))), k2_relat_1(k4_relat_1(A_140))) | ~v1_relat_1(k4_relat_1(A_140)) | ~v1_relat_1(k4_relat_1(B_139)) | ~v1_relat_1(B_139) | ~v1_relat_1(A_140))), inference(superposition, [status(thm), theory('equality')], [c_851, c_28])).
% 14.17/6.75  tff(c_11213, plain, (![A_455, A_456]: (r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_455), A_456))), k2_relat_1(k4_relat_1(k6_relat_1(A_455)))) | ~v1_relat_1(k4_relat_1(k6_relat_1(A_455))) | ~v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_455), A_456))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_455), A_456)) | ~v1_relat_1(k6_relat_1(A_455)))), inference(superposition, [status(thm), theory('equality')], [c_11204, c_857])).
% 14.17/6.75  tff(c_11333, plain, (![A_457, A_458]: (r1_tarski(k9_relat_1(k6_relat_1(A_457), A_458), A_458))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_276, c_276, c_2208, c_18, c_36, c_10176, c_2208, c_34, c_36, c_11213])).
% 14.17/6.75  tff(c_412, plain, (![B_106, A_107]: (k7_relat_1(B_106, A_107)=B_106 | ~r1_tarski(k1_relat_1(B_106), A_107) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_117])).
% 14.17/6.75  tff(c_425, plain, (![A_51, A_107]: (k7_relat_1(k6_relat_1(A_51), A_107)=k6_relat_1(A_51) | ~r1_tarski(A_51, A_107) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_412])).
% 14.17/6.75  tff(c_562, plain, (![A_115, A_116]: (k7_relat_1(k6_relat_1(A_115), A_116)=k6_relat_1(A_115) | ~r1_tarski(A_115, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_425])).
% 14.17/6.75  tff(c_369, plain, (![B_102, A_103]: (k3_xboole_0(k1_relat_1(B_102), A_103)=k1_relat_1(k7_relat_1(B_102, A_103)) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_107])).
% 14.17/6.75  tff(c_378, plain, (![A_51, A_103]: (k1_relat_1(k7_relat_1(k6_relat_1(A_51), A_103))=k3_xboole_0(A_51, A_103) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_369])).
% 14.17/6.75  tff(c_382, plain, (![A_51, A_103]: (k1_relat_1(k7_relat_1(k6_relat_1(A_51), A_103))=k3_xboole_0(A_51, A_103))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_378])).
% 14.17/6.75  tff(c_572, plain, (![A_115, A_116]: (k3_xboole_0(A_115, A_116)=k1_relat_1(k6_relat_1(A_115)) | ~r1_tarski(A_115, A_116))), inference(superposition, [status(thm), theory('equality')], [c_562, c_382])).
% 14.17/6.75  tff(c_605, plain, (![A_115, A_116]: (k3_xboole_0(A_115, A_116)=A_115 | ~r1_tarski(A_115, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_572])).
% 14.17/6.75  tff(c_11401, plain, (![A_457, A_458]: (k3_xboole_0(k9_relat_1(k6_relat_1(A_457), A_458), A_458)=k9_relat_1(k6_relat_1(A_457), A_458))), inference(resolution, [status(thm)], [c_11333, c_605])).
% 14.17/6.75  tff(c_697, plain, (![A_127, B_128]: (r1_tarski(k2_relat_1(k5_relat_1(A_127, B_128)), k2_relat_1(B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.17/6.75  tff(c_709, plain, (![A_37, B_38]: (r1_tarski(k2_relat_1(k8_relat_1(A_37, B_38)), k2_relat_1(k6_relat_1(A_37))) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(B_38) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_22, c_697])).
% 14.17/6.75  tff(c_735, plain, (![A_129, B_130]: (r1_tarski(k2_relat_1(k8_relat_1(A_129, B_130)), A_129) | ~v1_relat_1(B_130))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_34, c_709])).
% 14.17/6.75  tff(c_744, plain, (![A_82, A_60]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_82), A_60)), A_82) | ~v1_relat_1(k6_relat_1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_236, c_735])).
% 14.17/6.75  tff(c_754, plain, (![A_131, A_132]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_131), A_132)), A_131))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_744])).
% 14.17/6.75  tff(c_768, plain, (![A_131, A_43]: (r1_tarski(k9_relat_1(k6_relat_1(A_131), A_43), A_131) | ~v1_relat_1(k6_relat_1(A_131)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_754])).
% 14.17/6.75  tff(c_779, plain, (![A_133, A_134]: (r1_tarski(k9_relat_1(k6_relat_1(A_133), A_134), A_133))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_768])).
% 14.17/6.75  tff(c_789, plain, (![A_133, A_134]: (k3_xboole_0(k9_relat_1(k6_relat_1(A_133), A_134), A_133)=k9_relat_1(k6_relat_1(A_133), A_134))), inference(resolution, [status(thm)], [c_779, c_605])).
% 14.17/6.75  tff(c_1477, plain, (![A_60, A_171, B_61]: (k5_relat_1(k7_relat_1(k6_relat_1(A_60), A_171), B_61)=k7_relat_1(k7_relat_1(B_61, A_60), A_171) | ~v1_relat_1(B_61) | ~v1_relat_1(k6_relat_1(A_60)) | ~v1_relat_1(B_61))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1429])).
% 14.17/6.75  tff(c_1495, plain, (![A_60, A_171, B_61]: (k5_relat_1(k7_relat_1(k6_relat_1(A_60), A_171), B_61)=k7_relat_1(k7_relat_1(B_61, A_60), A_171) | ~v1_relat_1(B_61))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1477])).
% 14.17/6.75  tff(c_302, plain, (![B_95, A_96]: (k2_relat_1(k7_relat_1(B_95, A_96))=k9_relat_1(B_95, A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.17/6.75  tff(c_40, plain, (![A_55]: (k5_relat_1(A_55, k6_relat_1(k2_relat_1(A_55)))=A_55 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.17/6.75  tff(c_6597, plain, (![B_359, A_360]: (k5_relat_1(k7_relat_1(B_359, A_360), k6_relat_1(k9_relat_1(B_359, A_360)))=k7_relat_1(B_359, A_360) | ~v1_relat_1(k7_relat_1(B_359, A_360)) | ~v1_relat_1(B_359))), inference(superposition, [status(thm), theory('equality')], [c_302, c_40])).
% 14.17/6.75  tff(c_6657, plain, (![A_60, A_171]: (k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_60), A_171)), A_60), A_171)=k7_relat_1(k6_relat_1(A_60), A_171) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_60), A_171)) | ~v1_relat_1(k6_relat_1(A_60)) | ~v1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_60), A_171))))), inference(superposition, [status(thm), theory('equality')], [c_1495, c_6597])).
% 14.17/6.75  tff(c_26778, plain, (![A_654, A_655]: (k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_654), A_655)), A_654), A_655)=k7_relat_1(k6_relat_1(A_654), A_655))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_276, c_6657])).
% 14.17/6.75  tff(c_384, plain, (![A_104, A_105]: (k1_relat_1(k7_relat_1(k6_relat_1(A_104), A_105))=k3_xboole_0(A_104, A_105))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_378])).
% 14.17/6.75  tff(c_44, plain, (![B_59, A_58]: (k3_xboole_0(k1_relat_1(B_59), A_58)=k1_relat_1(k7_relat_1(B_59, A_58)) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_107])).
% 14.17/6.75  tff(c_390, plain, (![A_104, A_105, A_58]: (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_104), A_105), A_58))=k3_xboole_0(k3_xboole_0(A_104, A_105), A_58) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_104), A_105)))), inference(superposition, [status(thm), theory('equality')], [c_384, c_44])).
% 14.17/6.75  tff(c_405, plain, (![A_104, A_105, A_58]: (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_104), A_105), A_58))=k3_xboole_0(k3_xboole_0(A_104, A_105), A_58))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_390])).
% 14.17/6.75  tff(c_26806, plain, (![A_654, A_655]: (k3_xboole_0(k3_xboole_0(k9_relat_1(k6_relat_1(A_654), A_655), A_654), A_655)=k1_relat_1(k7_relat_1(k6_relat_1(A_654), A_655)))), inference(superposition, [status(thm), theory('equality')], [c_26778, c_405])).
% 14.17/6.75  tff(c_27018, plain, (![A_654, A_655]: (k9_relat_1(k6_relat_1(A_654), A_655)=k3_xboole_0(A_654, A_655))), inference(demodulation, [status(thm), theory('equality')], [c_11401, c_789, c_382, c_26806])).
% 14.17/6.75  tff(c_11297, plain, (![A_456, A_455]: (r1_tarski(k9_relat_1(k6_relat_1(A_456), A_455), A_455))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_276, c_276, c_2208, c_18, c_36, c_10176, c_2208, c_34, c_36, c_11213])).
% 14.17/6.75  tff(c_27141, plain, (![A_456, A_455]: (r1_tarski(k3_xboole_0(A_456, A_455), A_455))), inference(demodulation, [status(thm), theory('equality')], [c_27018, c_11297])).
% 14.17/6.75  tff(c_285, plain, (![B_90, A_91]: (r1_tarski(k1_relat_1(k7_relat_1(B_90, A_91)), k1_relat_1(B_90)) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_103])).
% 14.17/6.75  tff(c_291, plain, (![A_51, A_91]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_51), A_91)), A_51) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_285])).
% 14.17/6.75  tff(c_295, plain, (![A_51, A_91]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_51), A_91)), A_51))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_291])).
% 14.17/6.75  tff(c_383, plain, (![A_51, A_91]: (r1_tarski(k3_xboole_0(A_51, A_91), A_51))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_295])).
% 14.17/6.75  tff(c_27143, plain, (![A_51, A_171]: (k2_relat_1(k7_relat_1(k6_relat_1(A_51), A_171))=k3_xboole_0(A_51, A_171))), inference(demodulation, [status(thm), theory('equality')], [c_27018, c_10176])).
% 14.17/6.75  tff(c_1227, plain, (![A_160, B_161, C_162]: (k8_relat_1(A_160, k5_relat_1(B_161, C_162))=k5_relat_1(B_161, k8_relat_1(A_160, C_162)) | ~v1_relat_1(C_162) | ~v1_relat_1(B_161))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.17/6.75  tff(c_1259, plain, (![B_38, A_160, A_37]: (k5_relat_1(B_38, k8_relat_1(A_160, k6_relat_1(A_37)))=k8_relat_1(A_160, k8_relat_1(A_37, B_38)) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(B_38) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1227])).
% 14.17/6.75  tff(c_1276, plain, (![B_38, A_160, A_37]: (k5_relat_1(B_38, k7_relat_1(k6_relat_1(A_160), A_37))=k8_relat_1(A_160, k8_relat_1(A_37, B_38)) | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_236, c_1259])).
% 14.17/6.75  tff(c_5960, plain, (![A_160, A_346]: (k8_relat_1(A_160, k8_relat_1(A_346, k6_relat_1(k1_relat_1(k6_relat_1(A_160)))))=k7_relat_1(k6_relat_1(A_160), A_346) | ~v1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_160)))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_160), A_346)) | ~v1_relat_1(k6_relat_1(A_160)))), inference(superposition, [status(thm), theory('equality')], [c_5950, c_1276])).
% 14.17/6.75  tff(c_6039, plain, (![A_160, A_346]: (k8_relat_1(A_160, k7_relat_1(k6_relat_1(A_346), A_160))=k7_relat_1(k6_relat_1(A_160), A_346))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_276, c_18, c_236, c_32, c_5960])).
% 14.17/6.75  tff(c_6072, plain, (![A_51, A_346]: (k5_relat_1(k6_relat_1(A_51), k7_relat_1(k6_relat_1(A_51), A_346))=k7_relat_1(k6_relat_1(A_51), A_346))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_276, c_6034])).
% 14.17/6.75  tff(c_869, plain, (![B_139, A_52]: (k5_relat_1(k4_relat_1(B_139), k6_relat_1(A_52))=k4_relat_1(k5_relat_1(k6_relat_1(A_52), B_139)) | ~v1_relat_1(B_139) | ~v1_relat_1(k6_relat_1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_851])).
% 14.17/6.75  tff(c_2026, plain, (![B_207, A_208]: (k5_relat_1(k4_relat_1(B_207), k6_relat_1(A_208))=k4_relat_1(k5_relat_1(k6_relat_1(A_208), B_207)) | ~v1_relat_1(B_207))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_869])).
% 14.17/6.75  tff(c_36418, plain, (![A_772, B_773]: (k4_relat_1(k5_relat_1(k6_relat_1(A_772), B_773))=k8_relat_1(A_772, k4_relat_1(B_773)) | ~v1_relat_1(k4_relat_1(B_773)) | ~v1_relat_1(B_773))), inference(superposition, [status(thm), theory('equality')], [c_2026, c_22])).
% 14.17/6.75  tff(c_36488, plain, (![A_51, A_346]: (k8_relat_1(A_51, k4_relat_1(k7_relat_1(k6_relat_1(A_51), A_346)))=k4_relat_1(k7_relat_1(k6_relat_1(A_51), A_346)) | ~v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_51), A_346))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_51), A_346)))), inference(superposition, [status(thm), theory('equality')], [c_6072, c_36418])).
% 14.17/6.75  tff(c_36543, plain, (![A_51, A_346]: (k7_relat_1(k6_relat_1(A_51), A_346)=k7_relat_1(k6_relat_1(A_346), A_51))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_276, c_2208, c_6039, c_2208, c_2208, c_36488])).
% 14.17/6.75  tff(c_471, plain, (![A_111, A_51]: (k5_relat_1(k6_relat_1(A_111), k6_relat_1(A_51))=k6_relat_1(A_51) | ~r1_tarski(A_51, A_111) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_458])).
% 14.17/6.75  tff(c_477, plain, (![A_111, A_51]: (k5_relat_1(k6_relat_1(A_111), k6_relat_1(A_51))=k6_relat_1(A_51) | ~r1_tarski(A_51, A_111))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_471])).
% 14.17/6.75  tff(c_1461, plain, (![A_111, A_171, A_51]: (k5_relat_1(k7_relat_1(k6_relat_1(A_111), A_171), k6_relat_1(A_51))=k7_relat_1(k6_relat_1(A_51), A_171) | ~v1_relat_1(k6_relat_1(A_51)) | ~v1_relat_1(k6_relat_1(A_111)) | ~r1_tarski(A_51, A_111))), inference(superposition, [status(thm), theory('equality')], [c_477, c_1429])).
% 14.17/6.75  tff(c_43511, plain, (![A_848, A_849, A_850]: (k5_relat_1(k7_relat_1(k6_relat_1(A_848), A_849), k6_relat_1(A_850))=k7_relat_1(k6_relat_1(A_850), A_849) | ~r1_tarski(A_850, A_848))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_1461])).
% 14.17/6.75  tff(c_43585, plain, (![A_848, A_849]: (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_848), A_849))), A_849)=k7_relat_1(k6_relat_1(A_848), A_849) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_848), A_849)) | ~r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_848), A_849)), A_848))), inference(superposition, [status(thm), theory('equality')], [c_43511, c_40])).
% 14.17/6.75  tff(c_44585, plain, (![A_860, A_861]: (k7_relat_1(k6_relat_1(A_860), k3_xboole_0(A_861, A_860))=k7_relat_1(k6_relat_1(A_861), A_860))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_27143, c_276, c_36543, c_27143, c_43585])).
% 14.17/6.75  tff(c_431, plain, (![A_51, A_107]: (k7_relat_1(k6_relat_1(A_51), A_107)=k6_relat_1(A_51) | ~r1_tarski(A_51, A_107))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_425])).
% 14.17/6.75  tff(c_2259, plain, (![A_217, A_218]: (k4_relat_1(k7_relat_1(k6_relat_1(A_217), A_218))=k7_relat_1(k6_relat_1(A_218), A_217))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_236, c_2170])).
% 14.17/6.75  tff(c_2280, plain, (![A_107, A_51]: (k7_relat_1(k6_relat_1(A_107), A_51)=k4_relat_1(k6_relat_1(A_51)) | ~r1_tarski(A_51, A_107))), inference(superposition, [status(thm), theory('equality')], [c_431, c_2259])).
% 14.17/6.75  tff(c_2298, plain, (![A_107, A_51]: (k7_relat_1(k6_relat_1(A_107), A_51)=k6_relat_1(A_51) | ~r1_tarski(A_51, A_107))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2280])).
% 14.17/6.75  tff(c_44797, plain, (![A_861, A_860]: (k7_relat_1(k6_relat_1(A_861), A_860)=k6_relat_1(k3_xboole_0(A_861, A_860)) | ~r1_tarski(k3_xboole_0(A_861, A_860), A_860))), inference(superposition, [status(thm), theory('equality')], [c_44585, c_2298])).
% 14.17/6.75  tff(c_45058, plain, (![A_861, A_860]: (k7_relat_1(k6_relat_1(A_861), A_860)=k6_relat_1(k3_xboole_0(A_861, A_860)))), inference(demodulation, [status(thm), theory('equality')], [c_27141, c_44797])).
% 14.17/6.75  tff(c_131, plain, (![A_76, B_77]: (k5_relat_1(k6_relat_1(A_76), B_77)=k7_relat_1(B_77, A_76) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.17/6.75  tff(c_50, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.17/6.75  tff(c_137, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_50])).
% 14.17/6.75  tff(c_161, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_137])).
% 14.17/6.75  tff(c_45174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45058, c_161])).
% 14.17/6.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.17/6.75  
% 14.17/6.75  Inference rules
% 14.17/6.75  ----------------------
% 14.17/6.75  #Ref     : 0
% 14.17/6.75  #Sup     : 10918
% 14.17/6.75  #Fact    : 0
% 14.17/6.75  #Define  : 0
% 14.17/6.75  #Split   : 2
% 14.17/6.75  #Chain   : 0
% 14.17/6.75  #Close   : 0
% 14.17/6.75  
% 14.17/6.75  Ordering : KBO
% 14.17/6.75  
% 14.17/6.75  Simplification rules
% 14.17/6.75  ----------------------
% 14.17/6.75  #Subsume      : 1747
% 14.17/6.75  #Demod        : 12108
% 14.17/6.75  #Tautology    : 4252
% 14.17/6.75  #SimpNegUnit  : 0
% 14.17/6.75  #BackRed      : 143
% 14.17/6.75  
% 14.17/6.75  #Partial instantiations: 0
% 14.17/6.75  #Strategies tried      : 1
% 14.17/6.75  
% 14.17/6.75  Timing (in seconds)
% 14.17/6.75  ----------------------
% 14.17/6.75  Preprocessing        : 0.36
% 14.17/6.75  Parsing              : 0.20
% 14.17/6.75  CNF conversion       : 0.02
% 14.17/6.75  Main loop            : 5.56
% 14.17/6.75  Inferencing          : 1.19
% 14.17/6.75  Reduction            : 2.48
% 14.17/6.75  Demodulation         : 2.11
% 14.17/6.75  BG Simplification    : 0.15
% 14.17/6.75  Subsumption          : 1.38
% 14.17/6.75  Abstraction          : 0.25
% 14.17/6.75  MUC search           : 0.00
% 14.17/6.75  Cooper               : 0.00
% 14.17/6.75  Total                : 5.97
% 14.17/6.75  Index Insertion      : 0.00
% 14.17/6.75  Index Deletion       : 0.00
% 14.17/6.75  Index Matching       : 0.00
% 14.17/6.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
