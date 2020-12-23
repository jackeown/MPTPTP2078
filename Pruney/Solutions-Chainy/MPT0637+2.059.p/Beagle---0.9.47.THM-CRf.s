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
% DateTime   : Thu Dec  3 10:03:32 EST 2020

% Result     : Theorem 18.58s
% Output     : CNFRefutation 18.73s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 375 expanded)
%              Number of leaves         :   37 ( 150 expanded)
%              Depth                    :   13
%              Number of atoms          :  178 ( 624 expanded)
%              Number of equality atoms :   54 ( 191 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_47,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_123,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_134,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_18,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_232,plain,(
    ! [B_97,A_98] :
      ( k5_relat_1(B_97,k6_relat_1(A_98)) = k8_relat_1(A_98,B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    ! [A_68,B_69] :
      ( k5_relat_1(k6_relat_1(A_68),B_69) = k7_relat_1(B_69,A_68)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_239,plain,(
    ! [A_98,A_68] :
      ( k8_relat_1(A_98,k6_relat_1(A_68)) = k7_relat_1(k6_relat_1(A_98),A_68)
      | ~ v1_relat_1(k6_relat_1(A_98))
      | ~ v1_relat_1(k6_relat_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_52])).

tff(c_276,plain,(
    ! [A_98,A_68] : k8_relat_1(A_98,k6_relat_1(A_68)) = k7_relat_1(k6_relat_1(A_98),A_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_239])).

tff(c_40,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_59),B_60),B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_260,plain,(
    ! [A_98,A_59] :
      ( r1_tarski(k8_relat_1(A_98,k6_relat_1(A_59)),k6_relat_1(A_98))
      | ~ v1_relat_1(k6_relat_1(A_98))
      | ~ v1_relat_1(k6_relat_1(A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_40])).

tff(c_284,plain,(
    ! [A_98,A_59] : r1_tarski(k8_relat_1(A_98,k6_relat_1(A_59)),k6_relat_1(A_98)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_260])).

tff(c_338,plain,(
    ! [A_98,A_59] : r1_tarski(k7_relat_1(k6_relat_1(A_98),A_59),k6_relat_1(A_98)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_284])).

tff(c_339,plain,(
    ! [A_107,A_108] : k8_relat_1(A_107,k6_relat_1(A_108)) = k7_relat_1(k6_relat_1(A_107),A_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_239])).

tff(c_16,plain,(
    ! [A_30,B_31] :
      ( v1_relat_1(k5_relat_1(A_30,B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_253,plain,(
    ! [A_98,B_97] :
      ( v1_relat_1(k8_relat_1(A_98,B_97))
      | ~ v1_relat_1(k6_relat_1(A_98))
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_16])).

tff(c_282,plain,(
    ! [A_98,B_97] :
      ( v1_relat_1(k8_relat_1(A_98,B_97))
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_253])).

tff(c_349,plain,(
    ! [A_107,A_108] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_107),A_108))
      | ~ v1_relat_1(k6_relat_1(A_108)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_282])).

tff(c_359,plain,(
    ! [A_107,A_108] : v1_relat_1(k7_relat_1(k6_relat_1(A_107),A_108)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_349])).

tff(c_36,plain,(
    ! [A_58] : k1_relat_1(k6_relat_1(A_58)) = A_58 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_383,plain,(
    ! [B_115,A_116] :
      ( k3_xboole_0(k1_relat_1(B_115),A_116) = k1_relat_1(k7_relat_1(B_115,A_116))
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_392,plain,(
    ! [A_58,A_116] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_58),A_116)) = k3_xboole_0(A_58,A_116)
      | ~ v1_relat_1(k6_relat_1(A_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_383])).

tff(c_396,plain,(
    ! [A_58,A_116] : k1_relat_1(k7_relat_1(k6_relat_1(A_58),A_116)) = k3_xboole_0(A_58,A_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_392])).

tff(c_999,plain,(
    ! [A_156,B_157] :
      ( r1_tarski(k1_relat_1(A_156),k1_relat_1(B_157))
      | ~ r1_tarski(A_156,B_157)
      | ~ v1_relat_1(B_157)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1023,plain,(
    ! [A_156,A_58] :
      ( r1_tarski(k1_relat_1(A_156),A_58)
      | ~ r1_tarski(A_156,k6_relat_1(A_58))
      | ~ v1_relat_1(k6_relat_1(A_58))
      | ~ v1_relat_1(A_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_999])).

tff(c_1624,plain,(
    ! [A_187,A_188] :
      ( r1_tarski(k1_relat_1(A_187),A_188)
      | ~ r1_tarski(A_187,k6_relat_1(A_188))
      | ~ v1_relat_1(A_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1023])).

tff(c_1641,plain,(
    ! [A_58,A_116,A_188] :
      ( r1_tarski(k3_xboole_0(A_58,A_116),A_188)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_58),A_116),k6_relat_1(A_188))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_58),A_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_1624])).

tff(c_30726,plain,(
    ! [A_697,A_698,A_699] :
      ( r1_tarski(k3_xboole_0(A_697,A_698),A_699)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_697),A_698),k6_relat_1(A_699)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_1641])).

tff(c_30819,plain,(
    ! [A_98,A_59] : r1_tarski(k3_xboole_0(A_98,A_59),A_98) ),
    inference(resolution,[status(thm)],[c_338,c_30726])).

tff(c_149,plain,(
    ! [A_87,B_88] :
      ( k5_relat_1(k6_relat_1(A_87),B_88) = k7_relat_1(B_88,A_87)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    ! [B_60,A_59] :
      ( r1_tarski(k5_relat_1(B_60,k6_relat_1(A_59)),B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_170,plain,(
    ! [A_59,A_87] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_59),A_87),k6_relat_1(A_87))
      | ~ v1_relat_1(k6_relat_1(A_87))
      | ~ v1_relat_1(k6_relat_1(A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_42])).

tff(c_194,plain,(
    ! [A_59,A_87] : r1_tarski(k7_relat_1(k6_relat_1(A_59),A_87),k6_relat_1(A_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_170])).

tff(c_30820,plain,(
    ! [A_59,A_87] : r1_tarski(k3_xboole_0(A_59,A_87),A_87) ),
    inference(resolution,[status(thm)],[c_194,c_30726])).

tff(c_38,plain,(
    ! [A_58] : k2_relat_1(k6_relat_1(A_58)) = A_58 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_95,plain,(
    ! [A_83] :
      ( k5_relat_1(A_83,k6_relat_1(k2_relat_1(A_83))) = A_83
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_114,plain,(
    ! [A_58] :
      ( k5_relat_1(k6_relat_1(A_58),k6_relat_1(A_58)) = k6_relat_1(A_58)
      | ~ v1_relat_1(k6_relat_1(A_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_95])).

tff(c_122,plain,(
    ! [A_58] : k5_relat_1(k6_relat_1(A_58),k6_relat_1(A_58)) = k6_relat_1(A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_114])).

tff(c_602,plain,(
    ! [A_128,B_129] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_128,B_129)),k2_relat_1(B_129))
      | ~ v1_relat_1(B_129)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_617,plain,(
    ! [A_58] :
      ( r1_tarski(k2_relat_1(k6_relat_1(A_58)),k2_relat_1(k6_relat_1(A_58)))
      | ~ v1_relat_1(k6_relat_1(A_58))
      | ~ v1_relat_1(k6_relat_1(A_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_602])).

tff(c_638,plain,(
    ! [A_130] : r1_tarski(A_130,A_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_38,c_38,c_617])).

tff(c_44,plain,(
    ! [A_61,B_62] :
      ( k5_relat_1(k6_relat_1(A_61),B_62) = B_62
      | ~ r1_tarski(k1_relat_1(B_62),A_61)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_688,plain,(
    ! [B_143] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_143)),B_143) = B_143
      | ~ v1_relat_1(B_143) ) ),
    inference(resolution,[status(thm)],[c_638,c_44])).

tff(c_736,plain,(
    ! [B_69] :
      ( k7_relat_1(B_69,k1_relat_1(B_69)) = B_69
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_688])).

tff(c_22,plain,(
    ! [B_38,A_37] :
      ( k5_relat_1(B_38,k6_relat_1(A_37)) = k8_relat_1(A_37,B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1653,plain,(
    ! [A_189,B_190,C_191] :
      ( k8_relat_1(A_189,k5_relat_1(B_190,C_191)) = k5_relat_1(B_190,k8_relat_1(A_189,C_191))
      | ~ v1_relat_1(C_191)
      | ~ v1_relat_1(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1688,plain,(
    ! [B_38,A_189,A_37] :
      ( k5_relat_1(B_38,k8_relat_1(A_189,k6_relat_1(A_37))) = k8_relat_1(A_189,k8_relat_1(A_37,B_38))
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1653])).

tff(c_6305,plain,(
    ! [B_328,A_329,A_330] :
      ( k5_relat_1(B_328,k7_relat_1(k6_relat_1(A_329),A_330)) = k8_relat_1(A_329,k8_relat_1(A_330,B_328))
      | ~ v1_relat_1(B_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_276,c_1688])).

tff(c_6414,plain,(
    ! [A_329,A_330,A_68] :
      ( k8_relat_1(A_329,k8_relat_1(A_330,k6_relat_1(A_68))) = k7_relat_1(k7_relat_1(k6_relat_1(A_329),A_330),A_68)
      | ~ v1_relat_1(k6_relat_1(A_68))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_329),A_330)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_6305])).

tff(c_6460,plain,(
    ! [A_329,A_330,A_68] : k8_relat_1(A_329,k7_relat_1(k6_relat_1(A_330),A_68)) = k7_relat_1(k7_relat_1(k6_relat_1(A_329),A_330),A_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_18,c_276,c_6414])).

tff(c_1691,plain,(
    ! [A_68,A_189,B_69] :
      ( k5_relat_1(k6_relat_1(A_68),k8_relat_1(A_189,B_69)) = k8_relat_1(A_189,k7_relat_1(B_69,A_68))
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(k6_relat_1(A_68))
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1653])).

tff(c_4963,plain,(
    ! [A_293,A_294,B_295] :
      ( k5_relat_1(k6_relat_1(A_293),k8_relat_1(A_294,B_295)) = k8_relat_1(A_294,k7_relat_1(B_295,A_293))
      | ~ v1_relat_1(B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1691])).

tff(c_5021,plain,(
    ! [A_293,A_98,A_68] :
      ( k5_relat_1(k6_relat_1(A_293),k7_relat_1(k6_relat_1(A_98),A_68)) = k8_relat_1(A_98,k7_relat_1(k6_relat_1(A_68),A_293))
      | ~ v1_relat_1(k6_relat_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_4963])).

tff(c_5044,plain,(
    ! [A_293,A_98,A_68] : k5_relat_1(k6_relat_1(A_293),k7_relat_1(k6_relat_1(A_98),A_68)) = k8_relat_1(A_98,k7_relat_1(k6_relat_1(A_68),A_293)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5021])).

tff(c_45873,plain,(
    ! [A_293,A_98,A_68] : k5_relat_1(k6_relat_1(A_293),k7_relat_1(k6_relat_1(A_98),A_68)) = k7_relat_1(k7_relat_1(k6_relat_1(A_98),A_68),A_293) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6460,c_5044])).

tff(c_810,plain,(
    ! [B_148,A_149] :
      ( k5_relat_1(B_148,k6_relat_1(A_149)) = B_148
      | ~ r1_tarski(k2_relat_1(B_148),A_149)
      | ~ v1_relat_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_835,plain,(
    ! [A_58,A_149] :
      ( k5_relat_1(k6_relat_1(A_58),k6_relat_1(A_149)) = k6_relat_1(A_58)
      | ~ r1_tarski(A_58,A_149)
      | ~ v1_relat_1(k6_relat_1(A_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_810])).

tff(c_845,plain,(
    ! [A_58,A_149] :
      ( k5_relat_1(k6_relat_1(A_58),k6_relat_1(A_149)) = k6_relat_1(A_58)
      | ~ r1_tarski(A_58,A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_835])).

tff(c_1675,plain,(
    ! [A_58,A_189,A_149] :
      ( k5_relat_1(k6_relat_1(A_58),k8_relat_1(A_189,k6_relat_1(A_149))) = k8_relat_1(A_189,k6_relat_1(A_58))
      | ~ v1_relat_1(k6_relat_1(A_149))
      | ~ v1_relat_1(k6_relat_1(A_58))
      | ~ r1_tarski(A_58,A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_845,c_1653])).

tff(c_1701,plain,(
    ! [A_58,A_189,A_149] :
      ( k5_relat_1(k6_relat_1(A_58),k7_relat_1(k6_relat_1(A_189),A_149)) = k7_relat_1(k6_relat_1(A_189),A_58)
      | ~ r1_tarski(A_58,A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_276,c_276,c_1675])).

tff(c_56467,plain,(
    ! [A_982,A_983,A_984] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_982),A_983),A_984) = k7_relat_1(k6_relat_1(A_982),A_984)
      | ~ r1_tarski(A_984,A_983) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45873,c_1701])).

tff(c_56790,plain,(
    ! [A_982,A_983] :
      ( k7_relat_1(k6_relat_1(A_982),k1_relat_1(k7_relat_1(k6_relat_1(A_982),A_983))) = k7_relat_1(k6_relat_1(A_982),A_983)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_982),A_983)),A_983)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_982),A_983))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_982),A_983)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_56467])).

tff(c_58214,plain,(
    ! [A_995,A_996] : k7_relat_1(k6_relat_1(A_995),k3_xboole_0(A_995,A_996)) = k7_relat_1(k6_relat_1(A_995),A_996) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_359,c_30820,c_396,c_396,c_56790])).

tff(c_1143,plain,(
    ! [A_161,A_162] :
      ( k5_relat_1(k6_relat_1(A_161),k6_relat_1(A_162)) = k6_relat_1(A_161)
      | ~ r1_tarski(A_161,A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_835])).

tff(c_1162,plain,(
    ! [A_162,A_161] :
      ( k8_relat_1(A_162,k6_relat_1(A_161)) = k6_relat_1(A_161)
      | ~ v1_relat_1(k6_relat_1(A_161))
      | ~ r1_tarski(A_161,A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_22])).

tff(c_1219,plain,(
    ! [A_162,A_161] :
      ( k7_relat_1(k6_relat_1(A_162),A_161) = k6_relat_1(A_161)
      | ~ r1_tarski(A_161,A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_276,c_1162])).

tff(c_58579,plain,(
    ! [A_995,A_996] :
      ( k7_relat_1(k6_relat_1(A_995),A_996) = k6_relat_1(k3_xboole_0(A_995,A_996))
      | ~ r1_tarski(k3_xboole_0(A_995,A_996),A_995) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58214,c_1219])).

tff(c_58883,plain,(
    ! [A_995,A_996] : k7_relat_1(k6_relat_1(A_995),A_996) = k6_relat_1(k3_xboole_0(A_995,A_996)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30819,c_58579])).

tff(c_54,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_159,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_54])).

tff(c_188,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_159])).

tff(c_59024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58883,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:43:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.58/9.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.58/10.00  
% 18.58/10.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.58/10.00  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 18.58/10.00  
% 18.58/10.00  %Foreground sorts:
% 18.58/10.00  
% 18.58/10.00  
% 18.58/10.00  %Background operators:
% 18.58/10.00  
% 18.58/10.00  
% 18.58/10.00  %Foreground operators:
% 18.58/10.00  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 18.58/10.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.58/10.00  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 18.58/10.00  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 18.58/10.00  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.58/10.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.58/10.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.58/10.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.58/10.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.58/10.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.58/10.00  tff('#skF_2', type, '#skF_2': $i).
% 18.58/10.00  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.58/10.00  tff('#skF_1', type, '#skF_1': $i).
% 18.58/10.00  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.58/10.00  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.58/10.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.58/10.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.58/10.00  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 18.58/10.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.58/10.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.58/10.00  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 18.58/10.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.58/10.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.58/10.00  
% 18.73/10.02  tff(f_47, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 18.73/10.02  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 18.73/10.02  tff(f_131, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 18.73/10.02  tff(f_107, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 18.73/10.02  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 18.73/10.02  tff(f_101, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 18.73/10.02  tff(f_127, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 18.73/10.02  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 18.73/10.02  tff(f_123, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 18.73/10.02  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 18.73/10.02  tff(f_113, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 18.73/10.02  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_relat_1)).
% 18.73/10.02  tff(f_119, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 18.73/10.02  tff(f_134, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 18.73/10.02  tff(c_18, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.73/10.02  tff(c_232, plain, (![B_97, A_98]: (k5_relat_1(B_97, k6_relat_1(A_98))=k8_relat_1(A_98, B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_58])).
% 18.73/10.02  tff(c_52, plain, (![A_68, B_69]: (k5_relat_1(k6_relat_1(A_68), B_69)=k7_relat_1(B_69, A_68) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_131])).
% 18.73/10.02  tff(c_239, plain, (![A_98, A_68]: (k8_relat_1(A_98, k6_relat_1(A_68))=k7_relat_1(k6_relat_1(A_98), A_68) | ~v1_relat_1(k6_relat_1(A_98)) | ~v1_relat_1(k6_relat_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_52])).
% 18.73/10.02  tff(c_276, plain, (![A_98, A_68]: (k8_relat_1(A_98, k6_relat_1(A_68))=k7_relat_1(k6_relat_1(A_98), A_68))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_239])).
% 18.73/10.02  tff(c_40, plain, (![A_59, B_60]: (r1_tarski(k5_relat_1(k6_relat_1(A_59), B_60), B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.73/10.02  tff(c_260, plain, (![A_98, A_59]: (r1_tarski(k8_relat_1(A_98, k6_relat_1(A_59)), k6_relat_1(A_98)) | ~v1_relat_1(k6_relat_1(A_98)) | ~v1_relat_1(k6_relat_1(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_40])).
% 18.73/10.02  tff(c_284, plain, (![A_98, A_59]: (r1_tarski(k8_relat_1(A_98, k6_relat_1(A_59)), k6_relat_1(A_98)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_260])).
% 18.73/10.02  tff(c_338, plain, (![A_98, A_59]: (r1_tarski(k7_relat_1(k6_relat_1(A_98), A_59), k6_relat_1(A_98)))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_284])).
% 18.73/10.02  tff(c_339, plain, (![A_107, A_108]: (k8_relat_1(A_107, k6_relat_1(A_108))=k7_relat_1(k6_relat_1(A_107), A_108))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_239])).
% 18.73/10.02  tff(c_16, plain, (![A_30, B_31]: (v1_relat_1(k5_relat_1(A_30, B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.73/10.02  tff(c_253, plain, (![A_98, B_97]: (v1_relat_1(k8_relat_1(A_98, B_97)) | ~v1_relat_1(k6_relat_1(A_98)) | ~v1_relat_1(B_97) | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_232, c_16])).
% 18.73/10.02  tff(c_282, plain, (![A_98, B_97]: (v1_relat_1(k8_relat_1(A_98, B_97)) | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_253])).
% 18.73/10.02  tff(c_349, plain, (![A_107, A_108]: (v1_relat_1(k7_relat_1(k6_relat_1(A_107), A_108)) | ~v1_relat_1(k6_relat_1(A_108)))), inference(superposition, [status(thm), theory('equality')], [c_339, c_282])).
% 18.73/10.02  tff(c_359, plain, (![A_107, A_108]: (v1_relat_1(k7_relat_1(k6_relat_1(A_107), A_108)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_349])).
% 18.73/10.02  tff(c_36, plain, (![A_58]: (k1_relat_1(k6_relat_1(A_58))=A_58)), inference(cnfTransformation, [status(thm)], [f_101])).
% 18.73/10.02  tff(c_383, plain, (![B_115, A_116]: (k3_xboole_0(k1_relat_1(B_115), A_116)=k1_relat_1(k7_relat_1(B_115, A_116)) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_127])).
% 18.73/10.02  tff(c_392, plain, (![A_58, A_116]: (k1_relat_1(k7_relat_1(k6_relat_1(A_58), A_116))=k3_xboole_0(A_58, A_116) | ~v1_relat_1(k6_relat_1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_383])).
% 18.73/10.02  tff(c_396, plain, (![A_58, A_116]: (k1_relat_1(k7_relat_1(k6_relat_1(A_58), A_116))=k3_xboole_0(A_58, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_392])).
% 18.73/10.02  tff(c_999, plain, (![A_156, B_157]: (r1_tarski(k1_relat_1(A_156), k1_relat_1(B_157)) | ~r1_tarski(A_156, B_157) | ~v1_relat_1(B_157) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.73/10.02  tff(c_1023, plain, (![A_156, A_58]: (r1_tarski(k1_relat_1(A_156), A_58) | ~r1_tarski(A_156, k6_relat_1(A_58)) | ~v1_relat_1(k6_relat_1(A_58)) | ~v1_relat_1(A_156))), inference(superposition, [status(thm), theory('equality')], [c_36, c_999])).
% 18.73/10.02  tff(c_1624, plain, (![A_187, A_188]: (r1_tarski(k1_relat_1(A_187), A_188) | ~r1_tarski(A_187, k6_relat_1(A_188)) | ~v1_relat_1(A_187))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1023])).
% 18.73/10.02  tff(c_1641, plain, (![A_58, A_116, A_188]: (r1_tarski(k3_xboole_0(A_58, A_116), A_188) | ~r1_tarski(k7_relat_1(k6_relat_1(A_58), A_116), k6_relat_1(A_188)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_58), A_116)))), inference(superposition, [status(thm), theory('equality')], [c_396, c_1624])).
% 18.73/10.02  tff(c_30726, plain, (![A_697, A_698, A_699]: (r1_tarski(k3_xboole_0(A_697, A_698), A_699) | ~r1_tarski(k7_relat_1(k6_relat_1(A_697), A_698), k6_relat_1(A_699)))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_1641])).
% 18.73/10.02  tff(c_30819, plain, (![A_98, A_59]: (r1_tarski(k3_xboole_0(A_98, A_59), A_98))), inference(resolution, [status(thm)], [c_338, c_30726])).
% 18.73/10.02  tff(c_149, plain, (![A_87, B_88]: (k5_relat_1(k6_relat_1(A_87), B_88)=k7_relat_1(B_88, A_87) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_131])).
% 18.73/10.02  tff(c_42, plain, (![B_60, A_59]: (r1_tarski(k5_relat_1(B_60, k6_relat_1(A_59)), B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.73/10.02  tff(c_170, plain, (![A_59, A_87]: (r1_tarski(k7_relat_1(k6_relat_1(A_59), A_87), k6_relat_1(A_87)) | ~v1_relat_1(k6_relat_1(A_87)) | ~v1_relat_1(k6_relat_1(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_42])).
% 18.73/10.02  tff(c_194, plain, (![A_59, A_87]: (r1_tarski(k7_relat_1(k6_relat_1(A_59), A_87), k6_relat_1(A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_170])).
% 18.73/10.02  tff(c_30820, plain, (![A_59, A_87]: (r1_tarski(k3_xboole_0(A_59, A_87), A_87))), inference(resolution, [status(thm)], [c_194, c_30726])).
% 18.73/10.02  tff(c_38, plain, (![A_58]: (k2_relat_1(k6_relat_1(A_58))=A_58)), inference(cnfTransformation, [status(thm)], [f_101])).
% 18.73/10.02  tff(c_95, plain, (![A_83]: (k5_relat_1(A_83, k6_relat_1(k2_relat_1(A_83)))=A_83 | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_123])).
% 18.73/10.02  tff(c_114, plain, (![A_58]: (k5_relat_1(k6_relat_1(A_58), k6_relat_1(A_58))=k6_relat_1(A_58) | ~v1_relat_1(k6_relat_1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_95])).
% 18.73/10.02  tff(c_122, plain, (![A_58]: (k5_relat_1(k6_relat_1(A_58), k6_relat_1(A_58))=k6_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_114])).
% 18.73/10.02  tff(c_602, plain, (![A_128, B_129]: (r1_tarski(k2_relat_1(k5_relat_1(A_128, B_129)), k2_relat_1(B_129)) | ~v1_relat_1(B_129) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.73/10.02  tff(c_617, plain, (![A_58]: (r1_tarski(k2_relat_1(k6_relat_1(A_58)), k2_relat_1(k6_relat_1(A_58))) | ~v1_relat_1(k6_relat_1(A_58)) | ~v1_relat_1(k6_relat_1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_602])).
% 18.73/10.02  tff(c_638, plain, (![A_130]: (r1_tarski(A_130, A_130))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_38, c_38, c_617])).
% 18.73/10.02  tff(c_44, plain, (![A_61, B_62]: (k5_relat_1(k6_relat_1(A_61), B_62)=B_62 | ~r1_tarski(k1_relat_1(B_62), A_61) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_113])).
% 18.73/10.02  tff(c_688, plain, (![B_143]: (k5_relat_1(k6_relat_1(k1_relat_1(B_143)), B_143)=B_143 | ~v1_relat_1(B_143))), inference(resolution, [status(thm)], [c_638, c_44])).
% 18.73/10.02  tff(c_736, plain, (![B_69]: (k7_relat_1(B_69, k1_relat_1(B_69))=B_69 | ~v1_relat_1(B_69) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_52, c_688])).
% 18.73/10.02  tff(c_22, plain, (![B_38, A_37]: (k5_relat_1(B_38, k6_relat_1(A_37))=k8_relat_1(A_37, B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 18.73/10.02  tff(c_1653, plain, (![A_189, B_190, C_191]: (k8_relat_1(A_189, k5_relat_1(B_190, C_191))=k5_relat_1(B_190, k8_relat_1(A_189, C_191)) | ~v1_relat_1(C_191) | ~v1_relat_1(B_190))), inference(cnfTransformation, [status(thm)], [f_65])).
% 18.73/10.02  tff(c_1688, plain, (![B_38, A_189, A_37]: (k5_relat_1(B_38, k8_relat_1(A_189, k6_relat_1(A_37)))=k8_relat_1(A_189, k8_relat_1(A_37, B_38)) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(B_38) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1653])).
% 18.73/10.02  tff(c_6305, plain, (![B_328, A_329, A_330]: (k5_relat_1(B_328, k7_relat_1(k6_relat_1(A_329), A_330))=k8_relat_1(A_329, k8_relat_1(A_330, B_328)) | ~v1_relat_1(B_328))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_276, c_1688])).
% 18.73/10.02  tff(c_6414, plain, (![A_329, A_330, A_68]: (k8_relat_1(A_329, k8_relat_1(A_330, k6_relat_1(A_68)))=k7_relat_1(k7_relat_1(k6_relat_1(A_329), A_330), A_68) | ~v1_relat_1(k6_relat_1(A_68)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_329), A_330)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_6305])).
% 18.73/10.02  tff(c_6460, plain, (![A_329, A_330, A_68]: (k8_relat_1(A_329, k7_relat_1(k6_relat_1(A_330), A_68))=k7_relat_1(k7_relat_1(k6_relat_1(A_329), A_330), A_68))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_18, c_276, c_6414])).
% 18.73/10.02  tff(c_1691, plain, (![A_68, A_189, B_69]: (k5_relat_1(k6_relat_1(A_68), k8_relat_1(A_189, B_69))=k8_relat_1(A_189, k7_relat_1(B_69, A_68)) | ~v1_relat_1(B_69) | ~v1_relat_1(k6_relat_1(A_68)) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1653])).
% 18.73/10.02  tff(c_4963, plain, (![A_293, A_294, B_295]: (k5_relat_1(k6_relat_1(A_293), k8_relat_1(A_294, B_295))=k8_relat_1(A_294, k7_relat_1(B_295, A_293)) | ~v1_relat_1(B_295))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1691])).
% 18.73/10.02  tff(c_5021, plain, (![A_293, A_98, A_68]: (k5_relat_1(k6_relat_1(A_293), k7_relat_1(k6_relat_1(A_98), A_68))=k8_relat_1(A_98, k7_relat_1(k6_relat_1(A_68), A_293)) | ~v1_relat_1(k6_relat_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_276, c_4963])).
% 18.73/10.02  tff(c_5044, plain, (![A_293, A_98, A_68]: (k5_relat_1(k6_relat_1(A_293), k7_relat_1(k6_relat_1(A_98), A_68))=k8_relat_1(A_98, k7_relat_1(k6_relat_1(A_68), A_293)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5021])).
% 18.73/10.02  tff(c_45873, plain, (![A_293, A_98, A_68]: (k5_relat_1(k6_relat_1(A_293), k7_relat_1(k6_relat_1(A_98), A_68))=k7_relat_1(k7_relat_1(k6_relat_1(A_98), A_68), A_293))), inference(demodulation, [status(thm), theory('equality')], [c_6460, c_5044])).
% 18.73/10.02  tff(c_810, plain, (![B_148, A_149]: (k5_relat_1(B_148, k6_relat_1(A_149))=B_148 | ~r1_tarski(k2_relat_1(B_148), A_149) | ~v1_relat_1(B_148))), inference(cnfTransformation, [status(thm)], [f_119])).
% 18.73/10.02  tff(c_835, plain, (![A_58, A_149]: (k5_relat_1(k6_relat_1(A_58), k6_relat_1(A_149))=k6_relat_1(A_58) | ~r1_tarski(A_58, A_149) | ~v1_relat_1(k6_relat_1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_810])).
% 18.73/10.02  tff(c_845, plain, (![A_58, A_149]: (k5_relat_1(k6_relat_1(A_58), k6_relat_1(A_149))=k6_relat_1(A_58) | ~r1_tarski(A_58, A_149))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_835])).
% 18.73/10.02  tff(c_1675, plain, (![A_58, A_189, A_149]: (k5_relat_1(k6_relat_1(A_58), k8_relat_1(A_189, k6_relat_1(A_149)))=k8_relat_1(A_189, k6_relat_1(A_58)) | ~v1_relat_1(k6_relat_1(A_149)) | ~v1_relat_1(k6_relat_1(A_58)) | ~r1_tarski(A_58, A_149))), inference(superposition, [status(thm), theory('equality')], [c_845, c_1653])).
% 18.73/10.02  tff(c_1701, plain, (![A_58, A_189, A_149]: (k5_relat_1(k6_relat_1(A_58), k7_relat_1(k6_relat_1(A_189), A_149))=k7_relat_1(k6_relat_1(A_189), A_58) | ~r1_tarski(A_58, A_149))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_276, c_276, c_1675])).
% 18.73/10.02  tff(c_56467, plain, (![A_982, A_983, A_984]: (k7_relat_1(k7_relat_1(k6_relat_1(A_982), A_983), A_984)=k7_relat_1(k6_relat_1(A_982), A_984) | ~r1_tarski(A_984, A_983))), inference(demodulation, [status(thm), theory('equality')], [c_45873, c_1701])).
% 18.73/10.02  tff(c_56790, plain, (![A_982, A_983]: (k7_relat_1(k6_relat_1(A_982), k1_relat_1(k7_relat_1(k6_relat_1(A_982), A_983)))=k7_relat_1(k6_relat_1(A_982), A_983) | ~r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_982), A_983)), A_983) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_982), A_983)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_982), A_983)))), inference(superposition, [status(thm), theory('equality')], [c_736, c_56467])).
% 18.73/10.02  tff(c_58214, plain, (![A_995, A_996]: (k7_relat_1(k6_relat_1(A_995), k3_xboole_0(A_995, A_996))=k7_relat_1(k6_relat_1(A_995), A_996))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_359, c_30820, c_396, c_396, c_56790])).
% 18.73/10.02  tff(c_1143, plain, (![A_161, A_162]: (k5_relat_1(k6_relat_1(A_161), k6_relat_1(A_162))=k6_relat_1(A_161) | ~r1_tarski(A_161, A_162))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_835])).
% 18.73/10.02  tff(c_1162, plain, (![A_162, A_161]: (k8_relat_1(A_162, k6_relat_1(A_161))=k6_relat_1(A_161) | ~v1_relat_1(k6_relat_1(A_161)) | ~r1_tarski(A_161, A_162))), inference(superposition, [status(thm), theory('equality')], [c_1143, c_22])).
% 18.73/10.02  tff(c_1219, plain, (![A_162, A_161]: (k7_relat_1(k6_relat_1(A_162), A_161)=k6_relat_1(A_161) | ~r1_tarski(A_161, A_162))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_276, c_1162])).
% 18.73/10.02  tff(c_58579, plain, (![A_995, A_996]: (k7_relat_1(k6_relat_1(A_995), A_996)=k6_relat_1(k3_xboole_0(A_995, A_996)) | ~r1_tarski(k3_xboole_0(A_995, A_996), A_995))), inference(superposition, [status(thm), theory('equality')], [c_58214, c_1219])).
% 18.73/10.02  tff(c_58883, plain, (![A_995, A_996]: (k7_relat_1(k6_relat_1(A_995), A_996)=k6_relat_1(k3_xboole_0(A_995, A_996)))), inference(demodulation, [status(thm), theory('equality')], [c_30819, c_58579])).
% 18.73/10.02  tff(c_54, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 18.73/10.02  tff(c_159, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_54])).
% 18.73/10.02  tff(c_188, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_159])).
% 18.73/10.02  tff(c_59024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58883, c_188])).
% 18.73/10.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.73/10.02  
% 18.73/10.02  Inference rules
% 18.73/10.02  ----------------------
% 18.73/10.02  #Ref     : 0
% 18.73/10.02  #Sup     : 14182
% 18.73/10.02  #Fact    : 0
% 18.73/10.02  #Define  : 0
% 18.73/10.02  #Split   : 2
% 18.73/10.02  #Chain   : 0
% 18.73/10.02  #Close   : 0
% 18.73/10.02  
% 18.73/10.02  Ordering : KBO
% 18.73/10.02  
% 18.73/10.02  Simplification rules
% 18.73/10.02  ----------------------
% 18.73/10.02  #Subsume      : 1824
% 18.73/10.02  #Demod        : 12669
% 18.73/10.02  #Tautology    : 4480
% 18.73/10.02  #SimpNegUnit  : 0
% 18.73/10.02  #BackRed      : 108
% 18.73/10.02  
% 18.73/10.02  #Partial instantiations: 0
% 18.73/10.02  #Strategies tried      : 1
% 18.73/10.02  
% 18.73/10.02  Timing (in seconds)
% 18.73/10.02  ----------------------
% 18.73/10.02  Preprocessing        : 0.41
% 18.73/10.02  Parsing              : 0.23
% 18.73/10.02  CNF conversion       : 0.03
% 18.73/10.02  Main loop            : 8.77
% 18.73/10.02  Inferencing          : 1.46
% 18.73/10.03  Reduction            : 4.19
% 18.73/10.03  Demodulation         : 3.64
% 18.73/10.03  BG Simplification    : 0.20
% 18.73/10.03  Subsumption          : 2.40
% 18.73/10.03  Abstraction          : 0.31
% 18.73/10.03  MUC search           : 0.00
% 18.73/10.03  Cooper               : 0.00
% 18.73/10.03  Total                : 9.21
% 18.73/10.03  Index Insertion      : 0.00
% 18.73/10.03  Index Deletion       : 0.00
% 18.73/10.03  Index Matching       : 0.00
% 18.73/10.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
