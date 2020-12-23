%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:49 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 229 expanded)
%              Number of leaves         :   26 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  130 ( 424 expanded)
%              Number of equality atoms :   38 ( 115 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_103,plain,(
    ! [B_37,A_38] :
      ( k1_relat_1(k7_relat_1(B_37,A_38)) = A_38
      | ~ r1_tarski(A_38,k1_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_116,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_103])).

tff(c_123,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_116])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_15,A_14)),k1_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_162,plain,(
    ! [A_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_14)),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_16])).

tff(c_218,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_221,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_218])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_221])).

tff(c_227,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_22,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    ! [A_27] :
      ( k10_relat_1(A_27,k2_relat_1(A_27)) = k1_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [A_13] :
      ( k10_relat_1(k6_relat_1(A_13),A_13) = k1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_52])).

tff(c_65,plain,(
    ! [A_13] : k10_relat_1(k6_relat_1(A_13),A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12,c_61])).

tff(c_6,plain,(
    ! [A_5] :
      ( k10_relat_1(A_5,k2_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = k7_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_275,plain,(
    ! [B_50,C_51,A_52] :
      ( k10_relat_1(k5_relat_1(B_50,C_51),A_52) = k10_relat_1(B_50,k10_relat_1(C_51,A_52))
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_296,plain,(
    ! [A_18,B_19,A_52] :
      ( k10_relat_1(k6_relat_1(A_18),k10_relat_1(B_19,A_52)) = k10_relat_1(k7_relat_1(B_19,A_18),A_52)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_275])).

tff(c_1053,plain,(
    ! [A_71,B_72,A_73] :
      ( k10_relat_1(k6_relat_1(A_71),k10_relat_1(B_72,A_73)) = k10_relat_1(k7_relat_1(B_72,A_71),A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_296])).

tff(c_1076,plain,(
    ! [B_72,A_73] :
      ( k10_relat_1(k7_relat_1(B_72,k10_relat_1(B_72,A_73)),A_73) = k10_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_65])).

tff(c_124,plain,(
    ! [A_39,B_40] :
      ( k10_relat_1(A_39,k1_relat_1(B_40)) = k1_relat_1(k5_relat_1(A_39,B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_141,plain,(
    ! [A_39,A_13] :
      ( k1_relat_1(k5_relat_1(A_39,k6_relat_1(A_13))) = k10_relat_1(A_39,A_13)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_124])).

tff(c_194,plain,(
    ! [A_43,A_44] :
      ( k1_relat_1(k5_relat_1(A_43,k6_relat_1(A_44))) = k10_relat_1(A_43,A_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_141])).

tff(c_213,plain,(
    ! [A_44,A_18] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_44),A_18)) = k10_relat_1(k6_relat_1(A_18),A_44)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(k6_relat_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_194])).

tff(c_217,plain,(
    ! [A_44,A_18] : k1_relat_1(k7_relat_1(k6_relat_1(A_44),A_18)) = k10_relat_1(k6_relat_1(A_18),A_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_213])).

tff(c_87,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_31,A_32)),k1_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_90,plain,(
    ! [A_13,A_32] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_13),A_32)),A_13)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_87])).

tff(c_92,plain,(
    ! [A_13,A_32] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_13),A_32)),A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_90])).

tff(c_230,plain,(
    ! [A_32,A_13] : r1_tarski(k10_relat_1(k6_relat_1(A_32),A_13),A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_92])).

tff(c_1145,plain,(
    ! [B_76,A_77,A_78] :
      ( r1_tarski(k10_relat_1(k7_relat_1(B_76,A_77),A_78),k10_relat_1(B_76,A_78))
      | ~ v1_relat_1(B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_230])).

tff(c_2217,plain,(
    ! [A_114,A_115] :
      ( r1_tarski(k10_relat_1(k7_relat_1(A_114,A_115),k2_relat_1(A_114)),k1_relat_1(A_114))
      | ~ v1_relat_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1145])).

tff(c_2742,plain,(
    ! [B_124] :
      ( r1_tarski(k10_relat_1(B_124,k2_relat_1(B_124)),k1_relat_1(B_124))
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1076,c_2217])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( k1_relat_1(k7_relat_1(B_17,A_16)) = A_16
      | ~ r1_tarski(A_16,k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2886,plain,(
    ! [B_127] :
      ( k1_relat_1(k7_relat_1(B_127,k10_relat_1(B_127,k2_relat_1(B_127)))) = k10_relat_1(B_127,k2_relat_1(B_127))
      | ~ v1_relat_1(B_127) ) ),
    inference(resolution,[status(thm)],[c_2742,c_18])).

tff(c_3203,plain,(
    ! [A_133] :
      ( k1_relat_1(k7_relat_1(A_133,k1_relat_1(A_133))) = k10_relat_1(A_133,k2_relat_1(A_133))
      | ~ v1_relat_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2886])).

tff(c_10,plain,(
    ! [A_10,B_12] :
      ( k10_relat_1(A_10,k1_relat_1(B_12)) = k1_relat_1(k5_relat_1(A_10,B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_153,plain,(
    ! [A_10] :
      ( k1_relat_1(k5_relat_1(A_10,k7_relat_1('#skF_2','#skF_1'))) = k10_relat_1(A_10,'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_10])).

tff(c_802,plain,(
    ! [A_64] :
      ( k1_relat_1(k5_relat_1(A_64,k7_relat_1('#skF_2','#skF_1'))) = k10_relat_1(A_64,'#skF_1')
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_153])).

tff(c_848,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_18)) = k10_relat_1(k6_relat_1(A_18),'#skF_1')
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_802])).

tff(c_862,plain,(
    ! [A_18] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_18)) = k10_relat_1(k6_relat_1(A_18),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_22,c_848])).

tff(c_3234,plain,
    ( k10_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_2','#skF_1'))),'#skF_1') = k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3203,c_862])).

tff(c_3343,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_227,c_65,c_123,c_3234])).

tff(c_1072,plain,(
    ! [B_72,A_71,A_73] :
      ( r1_tarski(k10_relat_1(k7_relat_1(B_72,A_71),A_73),k10_relat_1(B_72,A_73))
      | ~ v1_relat_1(B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_230])).

tff(c_3378,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3343,c_1072])).

tff(c_3405,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3378])).

tff(c_3422,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3405])).

tff(c_3427,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3422])).

tff(c_3429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_3427])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:38:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.87  
% 4.69/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.87  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.69/1.87  
% 4.69/1.87  %Foreground sorts:
% 4.69/1.87  
% 4.69/1.87  
% 4.69/1.87  %Background operators:
% 4.69/1.87  
% 4.69/1.87  
% 4.69/1.87  %Foreground operators:
% 4.69/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.69/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.87  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.69/1.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.69/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/1.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.69/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.69/1.87  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.69/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.69/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.87  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.69/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.69/1.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.69/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.69/1.87  
% 4.69/1.89  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 4.69/1.89  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.69/1.89  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.69/1.89  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 4.69/1.89  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 4.69/1.89  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.69/1.89  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.69/1.89  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.69/1.89  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 4.69/1.89  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 4.69/1.89  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 4.69/1.89  tff(c_26, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.69/1.89  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.69/1.89  tff(c_4, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.69/1.89  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.69/1.89  tff(c_28, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.69/1.89  tff(c_103, plain, (![B_37, A_38]: (k1_relat_1(k7_relat_1(B_37, A_38))=A_38 | ~r1_tarski(A_38, k1_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.69/1.89  tff(c_116, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_103])).
% 4.69/1.89  tff(c_123, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_116])).
% 4.69/1.89  tff(c_16, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(k7_relat_1(B_15, A_14)), k1_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.69/1.89  tff(c_162, plain, (![A_14]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_14)), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_123, c_16])).
% 4.69/1.89  tff(c_218, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_162])).
% 4.69/1.89  tff(c_221, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_218])).
% 4.69/1.89  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_221])).
% 4.69/1.89  tff(c_227, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_162])).
% 4.69/1.89  tff(c_22, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.69/1.89  tff(c_12, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.69/1.89  tff(c_14, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.69/1.89  tff(c_52, plain, (![A_27]: (k10_relat_1(A_27, k2_relat_1(A_27))=k1_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.69/1.89  tff(c_61, plain, (![A_13]: (k10_relat_1(k6_relat_1(A_13), A_13)=k1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_52])).
% 4.69/1.89  tff(c_65, plain, (![A_13]: (k10_relat_1(k6_relat_1(A_13), A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12, c_61])).
% 4.69/1.89  tff(c_6, plain, (![A_5]: (k10_relat_1(A_5, k2_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.69/1.89  tff(c_20, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=k7_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.69/1.89  tff(c_275, plain, (![B_50, C_51, A_52]: (k10_relat_1(k5_relat_1(B_50, C_51), A_52)=k10_relat_1(B_50, k10_relat_1(C_51, A_52)) | ~v1_relat_1(C_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.69/1.89  tff(c_296, plain, (![A_18, B_19, A_52]: (k10_relat_1(k6_relat_1(A_18), k10_relat_1(B_19, A_52))=k10_relat_1(k7_relat_1(B_19, A_18), A_52) | ~v1_relat_1(B_19) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(B_19))), inference(superposition, [status(thm), theory('equality')], [c_20, c_275])).
% 4.69/1.89  tff(c_1053, plain, (![A_71, B_72, A_73]: (k10_relat_1(k6_relat_1(A_71), k10_relat_1(B_72, A_73))=k10_relat_1(k7_relat_1(B_72, A_71), A_73) | ~v1_relat_1(B_72))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_296])).
% 4.69/1.89  tff(c_1076, plain, (![B_72, A_73]: (k10_relat_1(k7_relat_1(B_72, k10_relat_1(B_72, A_73)), A_73)=k10_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(superposition, [status(thm), theory('equality')], [c_1053, c_65])).
% 4.69/1.89  tff(c_124, plain, (![A_39, B_40]: (k10_relat_1(A_39, k1_relat_1(B_40))=k1_relat_1(k5_relat_1(A_39, B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.69/1.89  tff(c_141, plain, (![A_39, A_13]: (k1_relat_1(k5_relat_1(A_39, k6_relat_1(A_13)))=k10_relat_1(A_39, A_13) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_12, c_124])).
% 4.69/1.89  tff(c_194, plain, (![A_43, A_44]: (k1_relat_1(k5_relat_1(A_43, k6_relat_1(A_44)))=k10_relat_1(A_43, A_44) | ~v1_relat_1(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_141])).
% 4.69/1.89  tff(c_213, plain, (![A_44, A_18]: (k1_relat_1(k7_relat_1(k6_relat_1(A_44), A_18))=k10_relat_1(k6_relat_1(A_18), A_44) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(k6_relat_1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_194])).
% 4.69/1.89  tff(c_217, plain, (![A_44, A_18]: (k1_relat_1(k7_relat_1(k6_relat_1(A_44), A_18))=k10_relat_1(k6_relat_1(A_18), A_44))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_213])).
% 4.69/1.89  tff(c_87, plain, (![B_31, A_32]: (r1_tarski(k1_relat_1(k7_relat_1(B_31, A_32)), k1_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.69/1.89  tff(c_90, plain, (![A_13, A_32]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_13), A_32)), A_13) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_87])).
% 4.69/1.89  tff(c_92, plain, (![A_13, A_32]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_13), A_32)), A_13))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_90])).
% 4.69/1.89  tff(c_230, plain, (![A_32, A_13]: (r1_tarski(k10_relat_1(k6_relat_1(A_32), A_13), A_13))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_92])).
% 4.69/1.89  tff(c_1145, plain, (![B_76, A_77, A_78]: (r1_tarski(k10_relat_1(k7_relat_1(B_76, A_77), A_78), k10_relat_1(B_76, A_78)) | ~v1_relat_1(B_76))), inference(superposition, [status(thm), theory('equality')], [c_1053, c_230])).
% 4.69/1.89  tff(c_2217, plain, (![A_114, A_115]: (r1_tarski(k10_relat_1(k7_relat_1(A_114, A_115), k2_relat_1(A_114)), k1_relat_1(A_114)) | ~v1_relat_1(A_114) | ~v1_relat_1(A_114))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1145])).
% 4.69/1.89  tff(c_2742, plain, (![B_124]: (r1_tarski(k10_relat_1(B_124, k2_relat_1(B_124)), k1_relat_1(B_124)) | ~v1_relat_1(B_124) | ~v1_relat_1(B_124) | ~v1_relat_1(B_124))), inference(superposition, [status(thm), theory('equality')], [c_1076, c_2217])).
% 4.69/1.89  tff(c_18, plain, (![B_17, A_16]: (k1_relat_1(k7_relat_1(B_17, A_16))=A_16 | ~r1_tarski(A_16, k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.69/1.89  tff(c_2886, plain, (![B_127]: (k1_relat_1(k7_relat_1(B_127, k10_relat_1(B_127, k2_relat_1(B_127))))=k10_relat_1(B_127, k2_relat_1(B_127)) | ~v1_relat_1(B_127))), inference(resolution, [status(thm)], [c_2742, c_18])).
% 4.69/1.89  tff(c_3203, plain, (![A_133]: (k1_relat_1(k7_relat_1(A_133, k1_relat_1(A_133)))=k10_relat_1(A_133, k2_relat_1(A_133)) | ~v1_relat_1(A_133) | ~v1_relat_1(A_133))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2886])).
% 4.69/1.89  tff(c_10, plain, (![A_10, B_12]: (k10_relat_1(A_10, k1_relat_1(B_12))=k1_relat_1(k5_relat_1(A_10, B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.69/1.89  tff(c_153, plain, (![A_10]: (k1_relat_1(k5_relat_1(A_10, k7_relat_1('#skF_2', '#skF_1')))=k10_relat_1(A_10, '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_123, c_10])).
% 4.69/1.89  tff(c_802, plain, (![A_64]: (k1_relat_1(k5_relat_1(A_64, k7_relat_1('#skF_2', '#skF_1')))=k10_relat_1(A_64, '#skF_1') | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_153])).
% 4.69/1.89  tff(c_848, plain, (![A_18]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_18))=k10_relat_1(k6_relat_1(A_18), '#skF_1') | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_20, c_802])).
% 4.69/1.89  tff(c_862, plain, (![A_18]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_18))=k10_relat_1(k6_relat_1(A_18), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_22, c_848])).
% 4.69/1.89  tff(c_3234, plain, (k10_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), '#skF_1')=k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3203, c_862])).
% 4.69/1.89  tff(c_3343, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_227, c_65, c_123, c_3234])).
% 4.69/1.89  tff(c_1072, plain, (![B_72, A_71, A_73]: (r1_tarski(k10_relat_1(k7_relat_1(B_72, A_71), A_73), k10_relat_1(B_72, A_73)) | ~v1_relat_1(B_72))), inference(superposition, [status(thm), theory('equality')], [c_1053, c_230])).
% 4.69/1.89  tff(c_3378, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3343, c_1072])).
% 4.69/1.89  tff(c_3405, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3378])).
% 4.69/1.89  tff(c_3422, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_3405])).
% 4.69/1.89  tff(c_3427, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3422])).
% 4.69/1.89  tff(c_3429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_3427])).
% 4.69/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.89  
% 4.69/1.89  Inference rules
% 4.69/1.89  ----------------------
% 4.69/1.89  #Ref     : 0
% 4.69/1.89  #Sup     : 766
% 4.69/1.89  #Fact    : 0
% 4.69/1.89  #Define  : 0
% 4.69/1.89  #Split   : 3
% 4.69/1.89  #Chain   : 0
% 4.69/1.89  #Close   : 0
% 4.69/1.89  
% 4.69/1.89  Ordering : KBO
% 4.69/1.89  
% 4.69/1.89  Simplification rules
% 4.69/1.89  ----------------------
% 4.69/1.89  #Subsume      : 57
% 4.69/1.89  #Demod        : 751
% 4.69/1.89  #Tautology    : 274
% 4.69/1.89  #SimpNegUnit  : 1
% 4.69/1.89  #BackRed      : 5
% 4.69/1.89  
% 4.69/1.89  #Partial instantiations: 0
% 4.69/1.89  #Strategies tried      : 1
% 4.69/1.89  
% 4.69/1.89  Timing (in seconds)
% 4.69/1.89  ----------------------
% 4.69/1.89  Preprocessing        : 0.31
% 4.69/1.89  Parsing              : 0.17
% 4.69/1.89  CNF conversion       : 0.02
% 4.69/1.89  Main loop            : 0.80
% 4.69/1.89  Inferencing          : 0.29
% 4.69/1.89  Reduction            : 0.29
% 4.69/1.89  Demodulation         : 0.22
% 4.69/1.89  BG Simplification    : 0.04
% 4.69/1.89  Subsumption          : 0.13
% 4.69/1.89  Abstraction          : 0.05
% 4.69/1.89  MUC search           : 0.00
% 4.69/1.89  Cooper               : 0.00
% 4.69/1.89  Total                : 1.14
% 4.69/1.89  Index Insertion      : 0.00
% 4.69/1.89  Index Deletion       : 0.00
% 4.69/1.89  Index Matching       : 0.00
% 4.69/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
