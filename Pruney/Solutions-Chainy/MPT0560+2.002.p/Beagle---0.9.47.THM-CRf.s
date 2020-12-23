%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:10 EST 2020

% Result     : Theorem 26.37s
% Output     : CNFRefutation 26.37s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 475 expanded)
%              Number of leaves         :   31 ( 179 expanded)
%              Depth                    :   21
%              Number of atoms          :  250 ( 951 expanded)
%              Number of equality atoms :   42 ( 169 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_50,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [A_26] : k1_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_239,plain,(
    ! [B_75,A_76] :
      ( k7_relat_1(B_75,A_76) = B_75
      | ~ r1_tarski(k1_relat_1(B_75),A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_250,plain,(
    ! [B_77] :
      ( k7_relat_1(B_77,k1_relat_1(B_77)) = B_77
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_239])).

tff(c_276,plain,(
    ! [A_26] :
      ( k7_relat_1(k6_relat_1(A_26),A_26) = k6_relat_1(A_26)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_250])).

tff(c_285,plain,(
    ! [A_26] : k7_relat_1(k6_relat_1(A_26),A_26) = k6_relat_1(A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_276])).

tff(c_172,plain,(
    ! [A_63,B_64] :
      ( k5_relat_1(k6_relat_1(A_63),B_64) = k7_relat_1(B_64,A_63)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_112,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(k5_relat_1(B_49,k6_relat_1(A_50)),B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_97,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_101,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(A_6)
      | ~ v1_relat_1(B_7)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_97])).

tff(c_116,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(k5_relat_1(B_49,k6_relat_1(A_50)))
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_112,c_101])).

tff(c_185,plain,(
    ! [A_50,A_63] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_50),A_63))
      | ~ v1_relat_1(k6_relat_1(A_63))
      | ~ v1_relat_1(k6_relat_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_116])).

tff(c_195,plain,(
    ! [A_50,A_63] : v1_relat_1(k7_relat_1(k6_relat_1(A_50),A_63)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_185])).

tff(c_36,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k5_relat_1(B_28,k6_relat_1(A_27)),B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_189,plain,(
    ! [A_27,A_63] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_27),A_63),k6_relat_1(A_63))
      | ~ v1_relat_1(k6_relat_1(A_63))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_36])).

tff(c_197,plain,(
    ! [A_27,A_63] : r1_tarski(k7_relat_1(k6_relat_1(A_27),A_63),k6_relat_1(A_63)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_189])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    ! [A_26] : k2_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_286,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k2_relat_1(A_78),k2_relat_1(B_79))
      | ~ r1_tarski(A_78,B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_305,plain,(
    ! [A_78,A_26] :
      ( r1_tarski(k2_relat_1(A_78),A_26)
      | ~ r1_tarski(A_78,k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_286])).

tff(c_473,plain,(
    ! [A_89,A_90] :
      ( r1_tarski(k2_relat_1(A_89),A_90)
      | ~ r1_tarski(A_89,k6_relat_1(A_90))
      | ~ v1_relat_1(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_305])).

tff(c_43511,plain,(
    ! [B_1112,A_1113,A_1114] :
      ( r1_tarski(k9_relat_1(B_1112,A_1113),A_1114)
      | ~ r1_tarski(k7_relat_1(B_1112,A_1113),k6_relat_1(A_1114))
      | ~ v1_relat_1(k7_relat_1(B_1112,A_1113))
      | ~ v1_relat_1(B_1112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_473])).

tff(c_43590,plain,(
    ! [A_27,A_63] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_27),A_63),A_63)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_27),A_63))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(resolution,[status(thm)],[c_197,c_43511])).

tff(c_43653,plain,(
    ! [A_27,A_63] : r1_tarski(k9_relat_1(k6_relat_1(A_27),A_63),A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_195,c_43590])).

tff(c_43654,plain,(
    ! [A_1115,A_1116] : r1_tarski(k9_relat_1(k6_relat_1(A_1115),A_1116),A_1116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_195,c_43590])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46294,plain,(
    ! [A_1142,A_1143,A_1144] :
      ( r1_tarski(A_1142,A_1143)
      | ~ r1_tarski(A_1142,k9_relat_1(k6_relat_1(A_1144),A_1143)) ) ),
    inference(resolution,[status(thm)],[c_43654,c_8])).

tff(c_46489,plain,(
    ! [A_27,A_1144,A_1143] : r1_tarski(k9_relat_1(k6_relat_1(A_27),k9_relat_1(k6_relat_1(A_1144),A_1143)),A_1143) ),
    inference(resolution,[status(thm)],[c_43653,c_46294])).

tff(c_242,plain,(
    ! [A_26,A_76] :
      ( k7_relat_1(k6_relat_1(A_26),A_76) = k6_relat_1(A_26)
      | ~ r1_tarski(A_26,A_76)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_239])).

tff(c_344,plain,(
    ! [A_81,A_82] :
      ( k7_relat_1(k6_relat_1(A_81),A_82) = k6_relat_1(A_81)
      | ~ r1_tarski(A_81,A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_242])).

tff(c_367,plain,(
    ! [A_81,A_82] :
      ( r1_tarski(k6_relat_1(A_81),k6_relat_1(A_82))
      | ~ r1_tarski(A_81,A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_197])).

tff(c_435,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k1_relat_1(A_85),k1_relat_1(B_86))
      | ~ r1_tarski(A_85,B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_451,plain,(
    ! [A_85,A_26] :
      ( r1_tarski(k1_relat_1(A_85),A_26)
      | ~ r1_tarski(A_85,k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_435])).

tff(c_558,plain,(
    ! [A_100,A_101] :
      ( r1_tarski(k1_relat_1(A_100),A_101)
      | ~ r1_tarski(A_100,k6_relat_1(A_101))
      | ~ v1_relat_1(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_451])).

tff(c_44,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_141,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(B_61,C_60)
      | ~ r1_tarski(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_153,plain,(
    ! [A_59] :
      ( r1_tarski(A_59,'#skF_3')
      | ~ r1_tarski(A_59,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_141])).

tff(c_614,plain,(
    ! [A_104] :
      ( r1_tarski(k1_relat_1(A_104),'#skF_3')
      | ~ r1_tarski(A_104,k6_relat_1('#skF_2'))
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_558,c_153])).

tff(c_40,plain,(
    ! [B_32,A_31] :
      ( k7_relat_1(B_32,A_31) = B_32
      | ~ r1_tarski(k1_relat_1(B_32),A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_961,plain,(
    ! [A_126] :
      ( k7_relat_1(A_126,'#skF_3') = A_126
      | ~ r1_tarski(A_126,k6_relat_1('#skF_2'))
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_614,c_40])).

tff(c_1001,plain,
    ( k7_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k6_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_961])).

tff(c_1027,plain,(
    k7_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k6_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1001])).

tff(c_200,plain,(
    ! [A_67,A_68] : r1_tarski(k7_relat_1(k6_relat_1(A_67),A_68),k6_relat_1(A_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_189])).

tff(c_208,plain,(
    ! [A_3,A_68,A_67] :
      ( r1_tarski(A_3,k6_relat_1(A_68))
      | ~ r1_tarski(A_3,k7_relat_1(k6_relat_1(A_67),A_68)) ) ),
    inference(resolution,[status(thm)],[c_200,c_8])).

tff(c_1182,plain,(
    ! [A_128] :
      ( r1_tarski(A_128,k6_relat_1('#skF_3'))
      | ~ r1_tarski(A_128,k6_relat_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_208])).

tff(c_1231,plain,(
    ! [A_81] :
      ( r1_tarski(k6_relat_1(A_81),k6_relat_1('#skF_3'))
      | ~ r1_tarski(A_81,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_367,c_1182])).

tff(c_18,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_762,plain,(
    ! [B_116,A_117,C_118] :
      ( r1_tarski(k9_relat_1(B_116,A_117),k9_relat_1(C_118,A_117))
      | ~ r1_tarski(B_116,C_118)
      | ~ v1_relat_1(C_118)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4956,plain,(
    ! [A_275,C_276] :
      ( r1_tarski(k2_relat_1(A_275),k9_relat_1(C_276,k1_relat_1(A_275)))
      | ~ r1_tarski(A_275,C_276)
      | ~ v1_relat_1(C_276)
      | ~ v1_relat_1(A_275)
      | ~ v1_relat_1(A_275) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_762])).

tff(c_4997,plain,(
    ! [A_26,C_276] :
      ( r1_tarski(A_26,k9_relat_1(C_276,k1_relat_1(k6_relat_1(A_26))))
      | ~ r1_tarski(k6_relat_1(A_26),C_276)
      | ~ v1_relat_1(C_276)
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4956])).

tff(c_5225,plain,(
    ! [A_285,C_286] :
      ( r1_tarski(A_285,k9_relat_1(C_286,A_285))
      | ~ r1_tarski(k6_relat_1(A_285),C_286)
      | ~ v1_relat_1(C_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_30,c_4997])).

tff(c_5227,plain,(
    ! [A_81] :
      ( r1_tarski(A_81,k9_relat_1(k6_relat_1('#skF_3'),A_81))
      | ~ v1_relat_1(k6_relat_1('#skF_3'))
      | ~ r1_tarski(A_81,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1231,c_5225])).

tff(c_5237,plain,(
    ! [A_81] :
      ( r1_tarski(A_81,k9_relat_1(k6_relat_1('#skF_3'),A_81))
      | ~ r1_tarski(A_81,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5227])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_27),B_28),B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_634,plain,(
    ! [A_105,A_106,A_107] :
      ( r1_tarski(A_105,k6_relat_1(A_106))
      | ~ r1_tarski(A_105,k7_relat_1(k6_relat_1(A_107),A_106)) ) ),
    inference(resolution,[status(thm)],[c_200,c_8])).

tff(c_660,plain,(
    ! [A_27,A_107,A_106] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_27),k7_relat_1(k6_relat_1(A_107),A_106)),k6_relat_1(A_106))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_107),A_106)) ) ),
    inference(resolution,[status(thm)],[c_34,c_634])).

tff(c_1615,plain,(
    ! [A_147,A_148,A_149] : r1_tarski(k5_relat_1(k6_relat_1(A_147),k7_relat_1(k6_relat_1(A_148),A_149)),k6_relat_1(A_149)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_660])).

tff(c_1633,plain,(
    ! [A_147,A_148,A_149] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_147),k7_relat_1(k6_relat_1(A_148),A_149)))
      | ~ v1_relat_1(k6_relat_1(A_149)) ) ),
    inference(resolution,[status(thm)],[c_1615,c_101])).

tff(c_1667,plain,(
    ! [A_150,A_151,A_152] : v1_relat_1(k5_relat_1(k6_relat_1(A_150),k7_relat_1(k6_relat_1(A_151),A_152))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1633])).

tff(c_1675,plain,(
    ! [A_150,A_26] : v1_relat_1(k5_relat_1(k6_relat_1(A_150),k6_relat_1(A_26))) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_1667])).

tff(c_38,plain,(
    ! [A_29,B_30] :
      ( k5_relat_1(k6_relat_1(A_29),B_30) = k7_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_132,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_55),B_56),B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1989,plain,(
    ! [A_167,B_168] :
      ( k5_relat_1(k6_relat_1(A_167),B_168) = B_168
      | ~ r1_tarski(B_168,k5_relat_1(k6_relat_1(A_167),B_168))
      | ~ v1_relat_1(B_168) ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_19294,plain,(
    ! [A_738,B_739] :
      ( k5_relat_1(k6_relat_1(A_738),B_739) = B_739
      | ~ r1_tarski(B_739,k7_relat_1(B_739,A_738))
      | ~ v1_relat_1(B_739)
      | ~ v1_relat_1(B_739) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1989])).

tff(c_19326,plain,
    ( k5_relat_1(k6_relat_1('#skF_3'),k6_relat_1('#skF_2')) = k6_relat_1('#skF_2')
    | ~ r1_tarski(k6_relat_1('#skF_2'),k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_19294])).

tff(c_19363,plain,(
    k5_relat_1(k6_relat_1('#skF_3'),k6_relat_1('#skF_2')) = k6_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_6,c_19326])).

tff(c_536,plain,(
    ! [B_97,C_98,A_99] :
      ( k9_relat_1(k5_relat_1(B_97,C_98),A_99) = k9_relat_1(C_98,k9_relat_1(B_97,A_99))
      | ~ v1_relat_1(C_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_553,plain,(
    ! [C_98,B_97] :
      ( k9_relat_1(C_98,k9_relat_1(B_97,k1_relat_1(k5_relat_1(B_97,C_98)))) = k2_relat_1(k5_relat_1(B_97,C_98))
      | ~ v1_relat_1(C_98)
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(k5_relat_1(B_97,C_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_536])).

tff(c_19415,plain,
    ( k9_relat_1(k6_relat_1('#skF_2'),k9_relat_1(k6_relat_1('#skF_3'),k1_relat_1(k6_relat_1('#skF_2')))) = k2_relat_1(k5_relat_1(k6_relat_1('#skF_3'),k6_relat_1('#skF_2')))
    | ~ v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_3'))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_3'),k6_relat_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_19363,c_553])).

tff(c_19490,plain,(
    k9_relat_1(k6_relat_1('#skF_2'),k9_relat_1(k6_relat_1('#skF_3'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1675,c_16,c_16,c_32,c_19363,c_30,c_19415])).

tff(c_460,plain,(
    ! [A_87,A_88] :
      ( r1_tarski(k6_relat_1(A_87),k6_relat_1(A_88))
      | ~ r1_tarski(A_87,A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_197])).

tff(c_17398,plain,(
    ! [A_718,A_719,A_720] :
      ( r1_tarski(A_718,k6_relat_1(A_719))
      | ~ r1_tarski(A_718,k6_relat_1(A_720))
      | ~ r1_tarski(A_720,A_719) ) ),
    inference(resolution,[status(thm)],[c_460,c_8])).

tff(c_17511,plain,(
    ! [A_27,A_63,A_719] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_27),A_63),k6_relat_1(A_719))
      | ~ r1_tarski(A_63,A_719) ) ),
    inference(resolution,[status(thm)],[c_197,c_17398])).

tff(c_43523,plain,(
    ! [A_27,A_63,A_719] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_27),A_63),A_719)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_27),A_63))
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ r1_tarski(A_63,A_719) ) ),
    inference(resolution,[status(thm)],[c_17511,c_43511])).

tff(c_47002,plain,(
    ! [A_1148,A_1149,A_1150] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_1148),A_1149),A_1150)
      | ~ r1_tarski(A_1149,A_1150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_195,c_43523])).

tff(c_51256,plain,(
    ! [A_1189] :
      ( r1_tarski('#skF_2',A_1189)
      | ~ r1_tarski(k9_relat_1(k6_relat_1('#skF_3'),'#skF_2'),A_1189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19490,c_47002])).

tff(c_51316,plain,
    ( r1_tarski('#skF_2',k9_relat_1(k6_relat_1('#skF_3'),k9_relat_1(k6_relat_1('#skF_3'),'#skF_2')))
    | ~ r1_tarski(k9_relat_1(k6_relat_1('#skF_3'),'#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_5237,c_51256])).

tff(c_51377,plain,(
    r1_tarski('#skF_2',k9_relat_1(k6_relat_1('#skF_3'),k9_relat_1(k6_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43653,c_51316])).

tff(c_51841,plain,
    ( k9_relat_1(k6_relat_1('#skF_3'),k9_relat_1(k6_relat_1('#skF_3'),'#skF_2')) = '#skF_2'
    | ~ r1_tarski(k9_relat_1(k6_relat_1('#skF_3'),k9_relat_1(k6_relat_1('#skF_3'),'#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_51377,c_2])).

tff(c_51889,plain,(
    k9_relat_1(k6_relat_1('#skF_3'),k9_relat_1(k6_relat_1('#skF_3'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46489,c_51841])).

tff(c_549,plain,(
    ! [B_30,A_29,A_99] :
      ( k9_relat_1(B_30,k9_relat_1(k6_relat_1(A_29),A_99)) = k9_relat_1(k7_relat_1(B_30,A_29),A_99)
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_536])).

tff(c_557,plain,(
    ! [B_30,A_29,A_99] :
      ( k9_relat_1(B_30,k9_relat_1(k6_relat_1(A_29),A_99)) = k9_relat_1(k7_relat_1(B_30,A_29),A_99)
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_549])).

tff(c_52027,plain,
    ( k9_relat_1(k7_relat_1(k6_relat_1('#skF_3'),'#skF_3'),'#skF_2') = '#skF_2'
    | ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_51889,c_557])).

tff(c_52107,plain,(
    k9_relat_1(k6_relat_1('#skF_3'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_285,c_52027])).

tff(c_82339,plain,(
    ! [B_1529] :
      ( k9_relat_1(k7_relat_1(B_1529,'#skF_3'),'#skF_2') = k9_relat_1(B_1529,'#skF_2')
      | ~ v1_relat_1(B_1529) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52107,c_557])).

tff(c_42,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_82535,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_82339,c_42])).

tff(c_82643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_82535])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n015.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 10:22:38 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.37/17.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.37/17.78  
% 26.37/17.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.37/17.78  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 26.37/17.78  
% 26.37/17.78  %Foreground sorts:
% 26.37/17.78  
% 26.37/17.78  
% 26.37/17.78  %Background operators:
% 26.37/17.78  
% 26.37/17.78  
% 26.37/17.78  %Foreground operators:
% 26.37/17.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.37/17.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 26.37/17.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 26.37/17.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.37/17.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 26.37/17.78  tff('#skF_2', type, '#skF_2': $i).
% 26.37/17.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 26.37/17.78  tff('#skF_3', type, '#skF_3': $i).
% 26.37/17.78  tff('#skF_1', type, '#skF_1': $i).
% 26.37/17.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.37/17.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.37/17.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 26.37/17.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 26.37/17.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.37/17.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 26.37/17.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.37/17.78  
% 26.37/17.81  tff(f_113, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 26.37/17.81  tff(f_50, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 26.37/17.81  tff(f_89, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 26.37/17.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 26.37/17.81  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 26.37/17.81  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 26.37/17.81  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 26.37/17.81  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 26.37/17.81  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 26.37/17.81  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 26.37/17.81  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 26.37/17.81  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 26.37/17.81  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 26.37/17.81  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 26.37/17.81  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 26.37/17.81  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 26.37/17.81  tff(c_16, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 26.37/17.81  tff(c_30, plain, (![A_26]: (k1_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_89])).
% 26.37/17.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 26.37/17.81  tff(c_239, plain, (![B_75, A_76]: (k7_relat_1(B_75, A_76)=B_75 | ~r1_tarski(k1_relat_1(B_75), A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_105])).
% 26.37/17.81  tff(c_250, plain, (![B_77]: (k7_relat_1(B_77, k1_relat_1(B_77))=B_77 | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_6, c_239])).
% 26.37/17.81  tff(c_276, plain, (![A_26]: (k7_relat_1(k6_relat_1(A_26), A_26)=k6_relat_1(A_26) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_250])).
% 26.37/17.81  tff(c_285, plain, (![A_26]: (k7_relat_1(k6_relat_1(A_26), A_26)=k6_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_276])).
% 26.37/17.81  tff(c_172, plain, (![A_63, B_64]: (k5_relat_1(k6_relat_1(A_63), B_64)=k7_relat_1(B_64, A_63) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_99])).
% 26.37/17.81  tff(c_112, plain, (![B_49, A_50]: (r1_tarski(k5_relat_1(B_49, k6_relat_1(A_50)), B_49) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_95])).
% 26.37/17.81  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 26.37/17.81  tff(c_97, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_48])).
% 26.37/17.81  tff(c_101, plain, (![A_6, B_7]: (v1_relat_1(A_6) | ~v1_relat_1(B_7) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_12, c_97])).
% 26.37/17.81  tff(c_116, plain, (![B_49, A_50]: (v1_relat_1(k5_relat_1(B_49, k6_relat_1(A_50))) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_112, c_101])).
% 26.37/17.81  tff(c_185, plain, (![A_50, A_63]: (v1_relat_1(k7_relat_1(k6_relat_1(A_50), A_63)) | ~v1_relat_1(k6_relat_1(A_63)) | ~v1_relat_1(k6_relat_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_116])).
% 26.37/17.81  tff(c_195, plain, (![A_50, A_63]: (v1_relat_1(k7_relat_1(k6_relat_1(A_50), A_63)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_185])).
% 26.37/17.81  tff(c_36, plain, (![B_28, A_27]: (r1_tarski(k5_relat_1(B_28, k6_relat_1(A_27)), B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_95])).
% 26.37/17.81  tff(c_189, plain, (![A_27, A_63]: (r1_tarski(k7_relat_1(k6_relat_1(A_27), A_63), k6_relat_1(A_63)) | ~v1_relat_1(k6_relat_1(A_63)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_36])).
% 26.37/17.81  tff(c_197, plain, (![A_27, A_63]: (r1_tarski(k7_relat_1(k6_relat_1(A_27), A_63), k6_relat_1(A_63)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_189])).
% 26.37/17.81  tff(c_20, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 26.37/17.81  tff(c_32, plain, (![A_26]: (k2_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_89])).
% 26.37/17.81  tff(c_286, plain, (![A_78, B_79]: (r1_tarski(k2_relat_1(A_78), k2_relat_1(B_79)) | ~r1_tarski(A_78, B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_85])).
% 26.37/17.81  tff(c_305, plain, (![A_78, A_26]: (r1_tarski(k2_relat_1(A_78), A_26) | ~r1_tarski(A_78, k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(A_78))), inference(superposition, [status(thm), theory('equality')], [c_32, c_286])).
% 26.37/17.81  tff(c_473, plain, (![A_89, A_90]: (r1_tarski(k2_relat_1(A_89), A_90) | ~r1_tarski(A_89, k6_relat_1(A_90)) | ~v1_relat_1(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_305])).
% 26.37/17.81  tff(c_43511, plain, (![B_1112, A_1113, A_1114]: (r1_tarski(k9_relat_1(B_1112, A_1113), A_1114) | ~r1_tarski(k7_relat_1(B_1112, A_1113), k6_relat_1(A_1114)) | ~v1_relat_1(k7_relat_1(B_1112, A_1113)) | ~v1_relat_1(B_1112))), inference(superposition, [status(thm), theory('equality')], [c_20, c_473])).
% 26.37/17.81  tff(c_43590, plain, (![A_27, A_63]: (r1_tarski(k9_relat_1(k6_relat_1(A_27), A_63), A_63) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_27), A_63)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(resolution, [status(thm)], [c_197, c_43511])).
% 26.37/17.81  tff(c_43653, plain, (![A_27, A_63]: (r1_tarski(k9_relat_1(k6_relat_1(A_27), A_63), A_63))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_195, c_43590])).
% 26.37/17.81  tff(c_43654, plain, (![A_1115, A_1116]: (r1_tarski(k9_relat_1(k6_relat_1(A_1115), A_1116), A_1116))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_195, c_43590])).
% 26.37/17.81  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 26.37/17.81  tff(c_46294, plain, (![A_1142, A_1143, A_1144]: (r1_tarski(A_1142, A_1143) | ~r1_tarski(A_1142, k9_relat_1(k6_relat_1(A_1144), A_1143)))), inference(resolution, [status(thm)], [c_43654, c_8])).
% 26.37/17.81  tff(c_46489, plain, (![A_27, A_1144, A_1143]: (r1_tarski(k9_relat_1(k6_relat_1(A_27), k9_relat_1(k6_relat_1(A_1144), A_1143)), A_1143))), inference(resolution, [status(thm)], [c_43653, c_46294])).
% 26.37/17.81  tff(c_242, plain, (![A_26, A_76]: (k7_relat_1(k6_relat_1(A_26), A_76)=k6_relat_1(A_26) | ~r1_tarski(A_26, A_76) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_239])).
% 26.37/17.81  tff(c_344, plain, (![A_81, A_82]: (k7_relat_1(k6_relat_1(A_81), A_82)=k6_relat_1(A_81) | ~r1_tarski(A_81, A_82))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_242])).
% 26.37/17.81  tff(c_367, plain, (![A_81, A_82]: (r1_tarski(k6_relat_1(A_81), k6_relat_1(A_82)) | ~r1_tarski(A_81, A_82))), inference(superposition, [status(thm), theory('equality')], [c_344, c_197])).
% 26.37/17.81  tff(c_435, plain, (![A_85, B_86]: (r1_tarski(k1_relat_1(A_85), k1_relat_1(B_86)) | ~r1_tarski(A_85, B_86) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_85])).
% 26.37/17.81  tff(c_451, plain, (![A_85, A_26]: (r1_tarski(k1_relat_1(A_85), A_26) | ~r1_tarski(A_85, k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_30, c_435])).
% 26.37/17.81  tff(c_558, plain, (![A_100, A_101]: (r1_tarski(k1_relat_1(A_100), A_101) | ~r1_tarski(A_100, k6_relat_1(A_101)) | ~v1_relat_1(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_451])).
% 26.37/17.81  tff(c_44, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 26.37/17.81  tff(c_141, plain, (![A_59, C_60, B_61]: (r1_tarski(A_59, C_60) | ~r1_tarski(B_61, C_60) | ~r1_tarski(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_37])).
% 26.37/17.81  tff(c_153, plain, (![A_59]: (r1_tarski(A_59, '#skF_3') | ~r1_tarski(A_59, '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_141])).
% 26.37/17.81  tff(c_614, plain, (![A_104]: (r1_tarski(k1_relat_1(A_104), '#skF_3') | ~r1_tarski(A_104, k6_relat_1('#skF_2')) | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_558, c_153])).
% 26.37/17.81  tff(c_40, plain, (![B_32, A_31]: (k7_relat_1(B_32, A_31)=B_32 | ~r1_tarski(k1_relat_1(B_32), A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_105])).
% 26.37/17.81  tff(c_961, plain, (![A_126]: (k7_relat_1(A_126, '#skF_3')=A_126 | ~r1_tarski(A_126, k6_relat_1('#skF_2')) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_614, c_40])).
% 26.37/17.81  tff(c_1001, plain, (k7_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k6_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_961])).
% 26.37/17.81  tff(c_1027, plain, (k7_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k6_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1001])).
% 26.37/17.81  tff(c_200, plain, (![A_67, A_68]: (r1_tarski(k7_relat_1(k6_relat_1(A_67), A_68), k6_relat_1(A_68)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_189])).
% 26.37/17.81  tff(c_208, plain, (![A_3, A_68, A_67]: (r1_tarski(A_3, k6_relat_1(A_68)) | ~r1_tarski(A_3, k7_relat_1(k6_relat_1(A_67), A_68)))), inference(resolution, [status(thm)], [c_200, c_8])).
% 26.37/17.81  tff(c_1182, plain, (![A_128]: (r1_tarski(A_128, k6_relat_1('#skF_3')) | ~r1_tarski(A_128, k6_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1027, c_208])).
% 26.37/17.81  tff(c_1231, plain, (![A_81]: (r1_tarski(k6_relat_1(A_81), k6_relat_1('#skF_3')) | ~r1_tarski(A_81, '#skF_2'))), inference(resolution, [status(thm)], [c_367, c_1182])).
% 26.37/17.81  tff(c_18, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 26.37/17.81  tff(c_762, plain, (![B_116, A_117, C_118]: (r1_tarski(k9_relat_1(B_116, A_117), k9_relat_1(C_118, A_117)) | ~r1_tarski(B_116, C_118) | ~v1_relat_1(C_118) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_67])).
% 26.37/17.81  tff(c_4956, plain, (![A_275, C_276]: (r1_tarski(k2_relat_1(A_275), k9_relat_1(C_276, k1_relat_1(A_275))) | ~r1_tarski(A_275, C_276) | ~v1_relat_1(C_276) | ~v1_relat_1(A_275) | ~v1_relat_1(A_275))), inference(superposition, [status(thm), theory('equality')], [c_18, c_762])).
% 26.37/17.81  tff(c_4997, plain, (![A_26, C_276]: (r1_tarski(A_26, k9_relat_1(C_276, k1_relat_1(k6_relat_1(A_26)))) | ~r1_tarski(k6_relat_1(A_26), C_276) | ~v1_relat_1(C_276) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_4956])).
% 26.37/17.81  tff(c_5225, plain, (![A_285, C_286]: (r1_tarski(A_285, k9_relat_1(C_286, A_285)) | ~r1_tarski(k6_relat_1(A_285), C_286) | ~v1_relat_1(C_286))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_30, c_4997])).
% 26.37/17.81  tff(c_5227, plain, (![A_81]: (r1_tarski(A_81, k9_relat_1(k6_relat_1('#skF_3'), A_81)) | ~v1_relat_1(k6_relat_1('#skF_3')) | ~r1_tarski(A_81, '#skF_2'))), inference(resolution, [status(thm)], [c_1231, c_5225])).
% 26.37/17.81  tff(c_5237, plain, (![A_81]: (r1_tarski(A_81, k9_relat_1(k6_relat_1('#skF_3'), A_81)) | ~r1_tarski(A_81, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5227])).
% 26.37/17.81  tff(c_34, plain, (![A_27, B_28]: (r1_tarski(k5_relat_1(k6_relat_1(A_27), B_28), B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_95])).
% 26.37/17.81  tff(c_634, plain, (![A_105, A_106, A_107]: (r1_tarski(A_105, k6_relat_1(A_106)) | ~r1_tarski(A_105, k7_relat_1(k6_relat_1(A_107), A_106)))), inference(resolution, [status(thm)], [c_200, c_8])).
% 26.37/17.81  tff(c_660, plain, (![A_27, A_107, A_106]: (r1_tarski(k5_relat_1(k6_relat_1(A_27), k7_relat_1(k6_relat_1(A_107), A_106)), k6_relat_1(A_106)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_107), A_106)))), inference(resolution, [status(thm)], [c_34, c_634])).
% 26.37/17.81  tff(c_1615, plain, (![A_147, A_148, A_149]: (r1_tarski(k5_relat_1(k6_relat_1(A_147), k7_relat_1(k6_relat_1(A_148), A_149)), k6_relat_1(A_149)))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_660])).
% 26.37/17.81  tff(c_1633, plain, (![A_147, A_148, A_149]: (v1_relat_1(k5_relat_1(k6_relat_1(A_147), k7_relat_1(k6_relat_1(A_148), A_149))) | ~v1_relat_1(k6_relat_1(A_149)))), inference(resolution, [status(thm)], [c_1615, c_101])).
% 26.37/17.81  tff(c_1667, plain, (![A_150, A_151, A_152]: (v1_relat_1(k5_relat_1(k6_relat_1(A_150), k7_relat_1(k6_relat_1(A_151), A_152))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1633])).
% 26.37/17.81  tff(c_1675, plain, (![A_150, A_26]: (v1_relat_1(k5_relat_1(k6_relat_1(A_150), k6_relat_1(A_26))))), inference(superposition, [status(thm), theory('equality')], [c_285, c_1667])).
% 26.37/17.81  tff(c_38, plain, (![A_29, B_30]: (k5_relat_1(k6_relat_1(A_29), B_30)=k7_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_99])).
% 26.37/17.81  tff(c_132, plain, (![A_55, B_56]: (r1_tarski(k5_relat_1(k6_relat_1(A_55), B_56), B_56) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_95])).
% 26.37/17.81  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 26.37/17.81  tff(c_1989, plain, (![A_167, B_168]: (k5_relat_1(k6_relat_1(A_167), B_168)=B_168 | ~r1_tarski(B_168, k5_relat_1(k6_relat_1(A_167), B_168)) | ~v1_relat_1(B_168))), inference(resolution, [status(thm)], [c_132, c_2])).
% 26.37/17.81  tff(c_19294, plain, (![A_738, B_739]: (k5_relat_1(k6_relat_1(A_738), B_739)=B_739 | ~r1_tarski(B_739, k7_relat_1(B_739, A_738)) | ~v1_relat_1(B_739) | ~v1_relat_1(B_739))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1989])).
% 26.37/17.81  tff(c_19326, plain, (k5_relat_1(k6_relat_1('#skF_3'), k6_relat_1('#skF_2'))=k6_relat_1('#skF_2') | ~r1_tarski(k6_relat_1('#skF_2'), k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1027, c_19294])).
% 26.37/17.81  tff(c_19363, plain, (k5_relat_1(k6_relat_1('#skF_3'), k6_relat_1('#skF_2'))=k6_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_6, c_19326])).
% 26.37/17.81  tff(c_536, plain, (![B_97, C_98, A_99]: (k9_relat_1(k5_relat_1(B_97, C_98), A_99)=k9_relat_1(C_98, k9_relat_1(B_97, A_99)) | ~v1_relat_1(C_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_74])).
% 26.37/17.81  tff(c_553, plain, (![C_98, B_97]: (k9_relat_1(C_98, k9_relat_1(B_97, k1_relat_1(k5_relat_1(B_97, C_98))))=k2_relat_1(k5_relat_1(B_97, C_98)) | ~v1_relat_1(C_98) | ~v1_relat_1(B_97) | ~v1_relat_1(k5_relat_1(B_97, C_98)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_536])).
% 26.37/17.81  tff(c_19415, plain, (k9_relat_1(k6_relat_1('#skF_2'), k9_relat_1(k6_relat_1('#skF_3'), k1_relat_1(k6_relat_1('#skF_2'))))=k2_relat_1(k5_relat_1(k6_relat_1('#skF_3'), k6_relat_1('#skF_2'))) | ~v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_3')) | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_3'), k6_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_19363, c_553])).
% 26.37/17.81  tff(c_19490, plain, (k9_relat_1(k6_relat_1('#skF_2'), k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1675, c_16, c_16, c_32, c_19363, c_30, c_19415])).
% 26.37/17.81  tff(c_460, plain, (![A_87, A_88]: (r1_tarski(k6_relat_1(A_87), k6_relat_1(A_88)) | ~r1_tarski(A_87, A_88))), inference(superposition, [status(thm), theory('equality')], [c_344, c_197])).
% 26.37/17.81  tff(c_17398, plain, (![A_718, A_719, A_720]: (r1_tarski(A_718, k6_relat_1(A_719)) | ~r1_tarski(A_718, k6_relat_1(A_720)) | ~r1_tarski(A_720, A_719))), inference(resolution, [status(thm)], [c_460, c_8])).
% 26.37/17.81  tff(c_17511, plain, (![A_27, A_63, A_719]: (r1_tarski(k7_relat_1(k6_relat_1(A_27), A_63), k6_relat_1(A_719)) | ~r1_tarski(A_63, A_719))), inference(resolution, [status(thm)], [c_197, c_17398])).
% 26.37/17.81  tff(c_43523, plain, (![A_27, A_63, A_719]: (r1_tarski(k9_relat_1(k6_relat_1(A_27), A_63), A_719) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_27), A_63)) | ~v1_relat_1(k6_relat_1(A_27)) | ~r1_tarski(A_63, A_719))), inference(resolution, [status(thm)], [c_17511, c_43511])).
% 26.37/17.81  tff(c_47002, plain, (![A_1148, A_1149, A_1150]: (r1_tarski(k9_relat_1(k6_relat_1(A_1148), A_1149), A_1150) | ~r1_tarski(A_1149, A_1150))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_195, c_43523])).
% 26.37/17.81  tff(c_51256, plain, (![A_1189]: (r1_tarski('#skF_2', A_1189) | ~r1_tarski(k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'), A_1189))), inference(superposition, [status(thm), theory('equality')], [c_19490, c_47002])).
% 26.37/17.81  tff(c_51316, plain, (r1_tarski('#skF_2', k9_relat_1(k6_relat_1('#skF_3'), k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'))) | ~r1_tarski(k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_5237, c_51256])).
% 26.37/17.81  tff(c_51377, plain, (r1_tarski('#skF_2', k9_relat_1(k6_relat_1('#skF_3'), k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_43653, c_51316])).
% 26.37/17.81  tff(c_51841, plain, (k9_relat_1(k6_relat_1('#skF_3'), k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'))='#skF_2' | ~r1_tarski(k9_relat_1(k6_relat_1('#skF_3'), k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_51377, c_2])).
% 26.37/17.81  tff(c_51889, plain, (k9_relat_1(k6_relat_1('#skF_3'), k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46489, c_51841])).
% 26.37/17.81  tff(c_549, plain, (![B_30, A_29, A_99]: (k9_relat_1(B_30, k9_relat_1(k6_relat_1(A_29), A_99))=k9_relat_1(k7_relat_1(B_30, A_29), A_99) | ~v1_relat_1(B_30) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_38, c_536])).
% 26.37/17.81  tff(c_557, plain, (![B_30, A_29, A_99]: (k9_relat_1(B_30, k9_relat_1(k6_relat_1(A_29), A_99))=k9_relat_1(k7_relat_1(B_30, A_29), A_99) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_549])).
% 26.37/17.81  tff(c_52027, plain, (k9_relat_1(k7_relat_1(k6_relat_1('#skF_3'), '#skF_3'), '#skF_2')='#skF_2' | ~v1_relat_1(k6_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_51889, c_557])).
% 26.37/17.81  tff(c_52107, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_285, c_52027])).
% 26.37/17.81  tff(c_82339, plain, (![B_1529]: (k9_relat_1(k7_relat_1(B_1529, '#skF_3'), '#skF_2')=k9_relat_1(B_1529, '#skF_2') | ~v1_relat_1(B_1529))), inference(superposition, [status(thm), theory('equality')], [c_52107, c_557])).
% 26.37/17.81  tff(c_42, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 26.37/17.81  tff(c_82535, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_82339, c_42])).
% 26.37/17.81  tff(c_82643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_82535])).
% 26.37/17.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.37/17.81  
% 26.37/17.81  Inference rules
% 26.37/17.81  ----------------------
% 26.37/17.81  #Ref     : 0
% 26.37/17.81  #Sup     : 17907
% 26.37/17.81  #Fact    : 0
% 26.37/17.81  #Define  : 0
% 26.37/17.81  #Split   : 6
% 26.37/17.81  #Chain   : 0
% 26.37/17.81  #Close   : 0
% 26.37/17.81  
% 26.37/17.81  Ordering : KBO
% 26.37/17.81  
% 26.37/17.81  Simplification rules
% 26.37/17.81  ----------------------
% 26.37/17.81  #Subsume      : 4702
% 26.37/17.81  #Demod        : 12678
% 26.37/17.81  #Tautology    : 3849
% 26.37/17.81  #SimpNegUnit  : 193
% 26.37/17.81  #BackRed      : 8
% 26.37/17.81  
% 26.37/17.81  #Partial instantiations: 0
% 26.37/17.81  #Strategies tried      : 1
% 26.37/17.81  
% 26.37/17.81  Timing (in seconds)
% 26.37/17.81  ----------------------
% 26.37/17.81  Preprocessing        : 0.33
% 26.37/17.81  Parsing              : 0.19
% 26.37/17.81  CNF conversion       : 0.02
% 26.37/17.81  Main loop            : 16.79
% 26.37/17.81  Inferencing          : 1.81
% 26.37/17.81  Reduction            : 7.81
% 26.37/17.81  Demodulation         : 6.73
% 26.37/17.81  BG Simplification    : 0.19
% 26.37/17.81  Subsumption          : 6.36
% 26.37/17.81  Abstraction          : 0.31
% 26.37/17.81  MUC search           : 0.00
% 26.37/17.81  Cooper               : 0.00
% 26.37/17.81  Total                : 17.17
% 26.37/17.81  Index Insertion      : 0.00
% 26.37/17.81  Index Deletion       : 0.00
% 26.37/17.81  Index Matching       : 0.00
% 26.37/17.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
