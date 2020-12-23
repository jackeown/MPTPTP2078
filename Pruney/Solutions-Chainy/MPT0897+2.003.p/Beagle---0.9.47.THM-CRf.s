%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:47 EST 2020

% Result     : Theorem 12.53s
% Output     : CNFRefutation 12.82s
% Verified   : 
% Statistics : Number of formulae       :  258 (1430 expanded)
%              Number of leaves         :   30 ( 426 expanded)
%              Depth                    :   15
%              Number of atoms          :  445 (3531 expanded)
%              Number of equality atoms :  300 (2919 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_50,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

tff(c_16,plain,(
    ! [A_13,B_14,C_15,D_16] : k2_zfmisc_1(k3_zfmisc_1(A_13,B_14,C_15),D_16) = k4_zfmisc_1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12) = k3_zfmisc_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_17373,plain,(
    ! [A_674,B_675,C_676] : k2_zfmisc_1(k2_zfmisc_1(A_674,B_675),C_676) = k3_zfmisc_1(A_674,B_675,C_676) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_17384,plain,(
    ! [A_10,B_11,C_12,C_676] : k3_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12,C_676) = k2_zfmisc_1(k3_zfmisc_1(A_10,B_11,C_12),C_676) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_17373])).

tff(c_18235,plain,(
    ! [A_10,B_11,C_12,C_676] : k3_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12,C_676) = k4_zfmisc_1(A_10,B_11,C_12,C_676) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_17384])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17390,plain,(
    ! [A_677,C_678,B_679] :
      ( r2_hidden(k2_mcart_1(A_677),C_678)
      | ~ r2_hidden(A_677,k2_zfmisc_1(B_679,C_678)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_17402,plain,(
    ! [A_680,C_681,A_682,B_683] :
      ( r2_hidden(k2_mcart_1(A_680),C_681)
      | ~ r2_hidden(A_680,k3_zfmisc_1(A_682,B_683,C_681)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_17390])).

tff(c_17406,plain,(
    ! [A_682,B_683,C_681] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k3_zfmisc_1(A_682,B_683,C_681))),C_681)
      | v1_xboole_0(k3_zfmisc_1(A_682,B_683,C_681)) ) ),
    inference(resolution,[status(thm)],[c_4,c_17402])).

tff(c_6,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_37,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_33])).

tff(c_38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_6])).

tff(c_17368,plain,(
    ! [A_671,B_672,C_673] :
      ( r2_hidden(k1_mcart_1(A_671),B_672)
      | ~ r2_hidden(A_671,k2_zfmisc_1(B_672,C_673)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_17423,plain,(
    ! [B_688,C_689] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_688,C_689))),B_688)
      | v1_xboole_0(k2_zfmisc_1(B_688,C_689)) ) ),
    inference(resolution,[status(thm)],[c_4,c_17368])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17451,plain,(
    ! [B_690,C_691] :
      ( ~ v1_xboole_0(B_690)
      | v1_xboole_0(k2_zfmisc_1(B_690,C_691)) ) ),
    inference(resolution,[status(thm)],[c_17423,c_2])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_17462,plain,(
    ! [B_692,C_693] :
      ( k2_zfmisc_1(B_692,C_693) = k1_xboole_0
      | ~ v1_xboole_0(B_692) ) ),
    inference(resolution,[status(thm)],[c_17451,c_8])).

tff(c_17469,plain,(
    ! [C_693] : k2_zfmisc_1(k1_xboole_0,C_693) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_17462])).

tff(c_28,plain,
    ( '#skF_5' != '#skF_9'
    | '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_54,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_32,plain,(
    k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_177,plain,(
    ! [D_57,B_58,A_59,C_60] :
      ( D_57 = B_58
      | k1_xboole_0 = B_58
      | k1_xboole_0 = A_59
      | k2_zfmisc_1(C_60,D_57) != k2_zfmisc_1(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2126,plain,(
    ! [C_221,D_216,B_217,A_220,B_218,A_219] :
      ( D_216 = B_218
      | k1_xboole_0 = B_218
      | k1_xboole_0 = A_219
      | k4_zfmisc_1(A_220,B_217,C_221,D_216) != k2_zfmisc_1(A_219,B_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_177])).

tff(c_2305,plain,(
    ! [B_226,A_227] :
      ( B_226 = '#skF_9'
      | k1_xboole_0 = B_226
      | k1_xboole_0 = A_227
      | k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != k2_zfmisc_1(A_227,B_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2126])).

tff(c_2323,plain,(
    ! [D_16,A_13,B_14,C_15] :
      ( D_16 = '#skF_9'
      | k1_xboole_0 = D_16
      | k3_zfmisc_1(A_13,B_14,C_15) = k1_xboole_0
      | k4_zfmisc_1(A_13,B_14,C_15,D_16) != k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2305])).

tff(c_11506,plain,
    ( '#skF_5' = '#skF_9'
    | k1_xboole_0 = '#skF_5'
    | k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2323])).

tff(c_11571,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_11506])).

tff(c_74,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden(k1_mcart_1(A_33),B_34)
      | ~ r2_hidden(A_33,k2_zfmisc_1(B_34,C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_126,plain,(
    ! [B_51,C_52] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_51,C_52))),B_51)
      | v1_xboole_0(k2_zfmisc_1(B_51,C_52)) ) ),
    inference(resolution,[status(thm)],[c_4,c_74])).

tff(c_154,plain,(
    ! [B_53,C_54] :
      ( ~ v1_xboole_0(B_53)
      | v1_xboole_0(k2_zfmisc_1(B_53,C_54)) ) ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_4731,plain,(
    ! [A_335,B_336,C_337,D_338] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_335,B_336,C_337))
      | v1_xboole_0(k4_zfmisc_1(A_335,B_336,C_337,D_338)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_154])).

tff(c_4801,plain,(
    ! [A_335,B_336,C_337,D_338] :
      ( k4_zfmisc_1(A_335,B_336,C_337,D_338) = k1_xboole_0
      | ~ v1_xboole_0(k3_zfmisc_1(A_335,B_336,C_337)) ) ),
    inference(resolution,[status(thm)],[c_4731,c_8])).

tff(c_11625,plain,(
    ! [D_338] :
      ( k4_zfmisc_1('#skF_2','#skF_3','#skF_4',D_338) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11571,c_4801])).

tff(c_11701,plain,(
    ! [D_338] : k4_zfmisc_1('#skF_2','#skF_3','#skF_4',D_338) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_11625])).

tff(c_30,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_11724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11701,c_30])).

tff(c_11726,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_11506])).

tff(c_93,plain,(
    ! [A_43,B_44,C_45,D_46] : k2_zfmisc_1(k3_zfmisc_1(A_43,B_44,C_45),D_46) = k4_zfmisc_1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [A_17,C_19,B_18] :
      ( r2_hidden(k2_mcart_1(A_17),C_19)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_465,plain,(
    ! [A_119,A_122,D_121,C_120,B_123] :
      ( r2_hidden(k2_mcart_1(A_119),D_121)
      | ~ r2_hidden(A_119,k4_zfmisc_1(A_122,B_123,C_120,D_121)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_18])).

tff(c_699,plain,(
    ! [A_130] :
      ( r2_hidden(k2_mcart_1(A_130),'#skF_9')
      | ~ r2_hidden(A_130,k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_465])).

tff(c_703,plain,(
    ! [A_130] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ r2_hidden(A_130,k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_699,c_2])).

tff(c_921,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_703])).

tff(c_165,plain,(
    ! [B_55,C_56] :
      ( k2_zfmisc_1(B_55,C_56) = k1_xboole_0
      | ~ v1_xboole_0(B_55) ) ),
    inference(resolution,[status(thm)],[c_154,c_8])).

tff(c_172,plain,(
    ! [C_56] : k2_zfmisc_1(k1_xboole_0,C_56) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_165])).

tff(c_4043,plain,(
    ! [B_301,C_305,D_303,D_300,A_302,C_304] :
      ( D_303 = D_300
      | k1_xboole_0 = D_300
      | k3_zfmisc_1(A_302,B_301,C_304) = k1_xboole_0
      | k4_zfmisc_1(A_302,B_301,C_304,D_300) != k2_zfmisc_1(C_305,D_303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_177])).

tff(c_4109,plain,(
    ! [D_303,C_305] :
      ( D_303 = '#skF_9'
      | k1_xboole_0 = '#skF_9'
      | k3_zfmisc_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != k2_zfmisc_1(C_305,D_303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4043])).

tff(c_4115,plain,(
    k3_zfmisc_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4109])).

tff(c_4168,plain,(
    ! [D_16] : k4_zfmisc_1('#skF_6','#skF_7','#skF_8',D_16) = k2_zfmisc_1(k1_xboole_0,D_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_4115,c_16])).

tff(c_4182,plain,(
    ! [D_16] : k4_zfmisc_1('#skF_6','#skF_7','#skF_8',D_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_4168])).

tff(c_4184,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4182,c_32])).

tff(c_4186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4184])).

tff(c_4187,plain,(
    ! [D_303,C_305] :
      ( k1_xboole_0 = '#skF_9'
      | D_303 = '#skF_9'
      | k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != k2_zfmisc_1(C_305,D_303) ) ),
    inference(splitRight,[status(thm)],[c_4109])).

tff(c_4523,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_4187])).

tff(c_4583,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4523,c_38])).

tff(c_4587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_921,c_4583])).

tff(c_4589,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_4187])).

tff(c_11725,plain,
    ( k1_xboole_0 = '#skF_5'
    | '#skF_5' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_11506])).

tff(c_11727,plain,(
    '#skF_5' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_11725])).

tff(c_113,plain,(
    ! [C_47,A_48,B_49,D_50] :
      ( C_47 = A_48
      | k1_xboole_0 = B_49
      | k1_xboole_0 = A_48
      | k2_zfmisc_1(C_47,D_50) != k2_zfmisc_1(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4189,plain,(
    ! [B_307,C_311,A_310,D_306,A_309,B_308] :
      ( k3_zfmisc_1(A_310,B_307,C_311) = A_309
      | k1_xboole_0 = B_308
      | k1_xboole_0 = A_309
      | k4_zfmisc_1(A_310,B_307,C_311,D_306) != k2_zfmisc_1(A_309,B_308) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_113])).

tff(c_4262,plain,(
    ! [A_312,B_313] :
      ( k3_zfmisc_1('#skF_6','#skF_7','#skF_8') = A_312
      | k1_xboole_0 = B_313
      | k1_xboole_0 = A_312
      | k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != k2_zfmisc_1(A_312,B_313) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4189])).

tff(c_4289,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k3_zfmisc_1(A_13,B_14,C_15) = k3_zfmisc_1('#skF_6','#skF_7','#skF_8')
      | k1_xboole_0 = D_16
      | k3_zfmisc_1(A_13,B_14,C_15) = k1_xboole_0
      | k4_zfmisc_1(A_13,B_14,C_15,D_16) != k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4262])).

tff(c_15268,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k3_zfmisc_1(A_13,B_14,C_15) = k3_zfmisc_1('#skF_6','#skF_7','#skF_8')
      | k1_xboole_0 = D_16
      | k3_zfmisc_1(A_13,B_14,C_15) = k1_xboole_0
      | k4_zfmisc_1(A_13,B_14,C_15,D_16) != k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11727,c_4289])).

tff(c_15271,plain,
    ( k3_zfmisc_1('#skF_6','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_9'
    | k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_15268])).

tff(c_15272,plain,(
    k3_zfmisc_1('#skF_6','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_11726,c_4589,c_15271])).

tff(c_26,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] :
      ( D_23 = A_20
      | k3_zfmisc_1(A_20,B_21,C_22) = k1_xboole_0
      | k3_zfmisc_1(D_23,E_24,F_25) != k3_zfmisc_1(A_20,B_21,C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_15451,plain,(
    ! [D_23,E_24,F_25] :
      ( D_23 = '#skF_6'
      | k3_zfmisc_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0
      | k3_zfmisc_1(D_23,E_24,F_25) != k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15272,c_26])).

tff(c_15479,plain,(
    ! [D_23,E_24,F_25] :
      ( D_23 = '#skF_6'
      | k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k3_zfmisc_1(D_23,E_24,F_25) != k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15272,c_15451])).

tff(c_15480,plain,(
    ! [D_23,E_24,F_25] :
      ( D_23 = '#skF_6'
      | k3_zfmisc_1(D_23,E_24,F_25) != k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_11726,c_15479])).

tff(c_15914,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_15480])).

tff(c_15916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_15914])).

tff(c_15917,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_11725])).

tff(c_81,plain,(
    ! [A_36,C_37,B_38] :
      ( r2_hidden(k2_mcart_1(A_36),C_37)
      | ~ r2_hidden(A_36,k2_zfmisc_1(B_38,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_480,plain,(
    ! [B_124,C_125] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_124,C_125))),C_125)
      | v1_xboole_0(k2_zfmisc_1(B_124,C_125)) ) ),
    inference(resolution,[status(thm)],[c_4,c_81])).

tff(c_190,plain,(
    ! [C_61] : k2_zfmisc_1(k1_xboole_0,C_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_165])).

tff(c_256,plain,(
    ! [A_70,C_71] :
      ( r2_hidden(k2_mcart_1(A_70),C_71)
      | ~ r2_hidden(A_70,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_18])).

tff(c_272,plain,(
    ! [C_71,A_70] :
      ( ~ v1_xboole_0(C_71)
      | ~ r2_hidden(A_70,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_256,c_2])).

tff(c_285,plain,(
    ! [A_70] : ~ r2_hidden(A_70,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_518,plain,(
    ! [B_126] : v1_xboole_0(k2_zfmisc_1(B_126,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_480,c_285])).

tff(c_548,plain,(
    ! [B_126] : k2_zfmisc_1(B_126,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_518,c_8])).

tff(c_16187,plain,(
    ! [B_613] : k2_zfmisc_1(B_613,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15917,c_15917,c_548])).

tff(c_16246,plain,(
    ! [A_13,B_14,C_15] : k4_zfmisc_1(A_13,B_14,C_15,'#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_16187])).

tff(c_15999,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15917,c_30])).

tff(c_17012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16246,c_15999])).

tff(c_17014,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_703])).

tff(c_17030,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_17014,c_8])).

tff(c_17052,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17030,c_30])).

tff(c_17043,plain,(
    ! [A_70] : ~ r2_hidden(A_70,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17030,c_285])).

tff(c_474,plain,(
    ! [A_119] :
      ( r2_hidden(k2_mcart_1(A_119),'#skF_9')
      | ~ r2_hidden(A_119,k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_465])).

tff(c_17221,plain,(
    ! [A_664] : ~ r2_hidden(A_664,k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_17043,c_474])).

tff(c_17236,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_17221])).

tff(c_17055,plain,(
    ! [A_5] :
      ( A_5 = '#skF_9'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17030,c_8])).

tff(c_17350,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_17236,c_17055])).

tff(c_17354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17052,c_17350])).

tff(c_17355,plain,(
    ! [C_71] : ~ v1_xboole_0(C_71) ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_17360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17355,c_38])).

tff(c_17361,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4'
    | '#skF_5' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_17367,plain,(
    '#skF_5' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_17361])).

tff(c_17362,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_17397,plain,(
    k4_zfmisc_1('#skF_2','#skF_7','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17362,c_32])).

tff(c_17511,plain,(
    ! [D_697,B_698,A_699,C_700] :
      ( D_697 = B_698
      | k1_xboole_0 = B_698
      | k1_xboole_0 = A_699
      | k2_zfmisc_1(C_700,D_697) != k2_zfmisc_1(A_699,B_698) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18943,plain,(
    ! [C_844,B_840,A_842,B_841,A_843,D_839] :
      ( D_839 = B_840
      | k1_xboole_0 = B_840
      | k1_xboole_0 = A_842
      | k4_zfmisc_1(A_843,B_841,C_844,D_839) != k2_zfmisc_1(A_842,B_840) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_17511])).

tff(c_19220,plain,(
    ! [B_853,A_854] :
      ( B_853 = '#skF_9'
      | k1_xboole_0 = B_853
      | k1_xboole_0 = A_854
      | k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != k2_zfmisc_1(A_854,B_853) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17397,c_18943])).

tff(c_19238,plain,(
    ! [D_16,A_13,B_14,C_15] :
      ( D_16 = '#skF_9'
      | k1_xboole_0 = D_16
      | k3_zfmisc_1(A_13,B_14,C_15) = k1_xboole_0
      | k4_zfmisc_1(A_13,B_14,C_15,D_16) != k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_19220])).

tff(c_23906,plain,
    ( '#skF_5' = '#skF_9'
    | k1_xboole_0 = '#skF_5'
    | k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_19238])).

tff(c_23907,plain,
    ( k1_xboole_0 = '#skF_5'
    | k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_17367,c_23906])).

tff(c_23958,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_23907])).

tff(c_24033,plain,(
    ! [D_16] : k4_zfmisc_1('#skF_2','#skF_3','#skF_4',D_16) = k2_zfmisc_1(k1_xboole_0,D_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_23958,c_16])).

tff(c_24054,plain,(
    ! [D_16] : k4_zfmisc_1('#skF_2','#skF_3','#skF_4',D_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17469,c_24033])).

tff(c_24067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24054,c_30])).

tff(c_24068,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_23907])).

tff(c_17470,plain,(
    ! [C_694] : k2_zfmisc_1(k1_xboole_0,C_694) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_17462])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(k1_mcart_1(A_17),B_18)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_17546,plain,(
    ! [A_707] :
      ( r2_hidden(k1_mcart_1(A_707),k1_xboole_0)
      | ~ r2_hidden(A_707,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17470,c_20])).

tff(c_17549,plain,(
    ! [A_707] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_707,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_17546,c_2])).

tff(c_17552,plain,(
    ! [A_707] : ~ r2_hidden(A_707,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_17549])).

tff(c_24149,plain,(
    ! [A_1029] : ~ r2_hidden(A_1029,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24068,c_17552])).

tff(c_24421,plain,(
    ! [A_1044,B_1045] : v1_xboole_0(k3_zfmisc_1(A_1044,B_1045,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_17406,c_24149])).

tff(c_24748,plain,(
    ! [A_1064,B_1065,C_1066] : v1_xboole_0(k4_zfmisc_1(A_1064,B_1065,C_1066,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18235,c_24421])).

tff(c_24140,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24068,c_8])).

tff(c_24765,plain,(
    ! [A_1064,B_1065,C_1066] : k4_zfmisc_1(A_1064,B_1065,C_1066,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_24748,c_24140])).

tff(c_24137,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24068,c_30])).

tff(c_24891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24765,c_24137])).

tff(c_24892,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17361])).

tff(c_24899,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_24892])).

tff(c_24893,plain,(
    '#skF_5' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_17361])).

tff(c_24905,plain,(
    k4_zfmisc_1('#skF_2','#skF_7','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24893,c_17362,c_32])).

tff(c_25065,plain,(
    ! [D_1102,B_1103,A_1104,C_1105] :
      ( D_1102 = B_1103
      | k1_xboole_0 = B_1103
      | k1_xboole_0 = A_1104
      | k2_zfmisc_1(C_1105,D_1102) != k2_zfmisc_1(A_1104,B_1103) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_31283,plain,(
    ! [C_1414,D_1409,C_1413,B_1410,A_1412,D_1411] :
      ( D_1411 = D_1409
      | k1_xboole_0 = D_1409
      | k3_zfmisc_1(A_1412,B_1410,C_1414) = k1_xboole_0
      | k4_zfmisc_1(A_1412,B_1410,C_1414,D_1409) != k2_zfmisc_1(C_1413,D_1411) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_25065])).

tff(c_31361,plain,(
    ! [D_1411,C_1413] :
      ( D_1411 = '#skF_9'
      | k1_xboole_0 = '#skF_9'
      | k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != k2_zfmisc_1(C_1413,D_1411) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24905,c_31283])).

tff(c_31790,plain,(
    k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_31361])).

tff(c_24900,plain,(
    ! [A_1074,B_1075,C_1076] :
      ( r2_hidden(k1_mcart_1(A_1074),B_1075)
      | ~ r2_hidden(A_1074,k2_zfmisc_1(B_1075,C_1076)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_25752,plain,(
    ! [B_1185,C_1186] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1185,C_1186))),B_1185)
      | v1_xboole_0(k2_zfmisc_1(B_1185,C_1186)) ) ),
    inference(resolution,[status(thm)],[c_4,c_24900])).

tff(c_25993,plain,(
    ! [B_1191,C_1192] :
      ( ~ v1_xboole_0(B_1191)
      | v1_xboole_0(k2_zfmisc_1(B_1191,C_1192)) ) ),
    inference(resolution,[status(thm)],[c_25752,c_2])).

tff(c_29140,plain,(
    ! [A_1348,B_1349,C_1350,D_1351] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_1348,B_1349,C_1350))
      | v1_xboole_0(k4_zfmisc_1(A_1348,B_1349,C_1350,D_1351)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_25993])).

tff(c_29200,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'))
    | v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24905,c_29140])).

tff(c_30418,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_29200])).

tff(c_31791,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31790,c_30418])).

tff(c_31795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_31791])).

tff(c_31796,plain,(
    ! [D_1411,C_1413] :
      ( k1_xboole_0 = '#skF_9'
      | D_1411 = '#skF_9'
      | k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != k2_zfmisc_1(C_1413,D_1411) ) ),
    inference(splitRight,[status(thm)],[c_31361])).

tff(c_33384,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_31796])).

tff(c_24910,plain,(
    ! [A_1077,C_1078,B_1079] :
      ( r2_hidden(k2_mcart_1(A_1077),C_1078)
      | ~ r2_hidden(A_1077,k2_zfmisc_1(B_1079,C_1078)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24955,plain,(
    ! [B_1091,C_1092] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1091,C_1092))),C_1092)
      | v1_xboole_0(k2_zfmisc_1(B_1091,C_1092)) ) ),
    inference(resolution,[status(thm)],[c_4,c_24910])).

tff(c_24997,plain,(
    ! [C_1097,B_1098] :
      ( ~ v1_xboole_0(C_1097)
      | v1_xboole_0(k2_zfmisc_1(B_1098,C_1097)) ) ),
    inference(resolution,[status(thm)],[c_24955,c_2])).

tff(c_25008,plain,(
    ! [B_1099,C_1100] :
      ( k2_zfmisc_1(B_1099,C_1100) = k1_xboole_0
      | ~ v1_xboole_0(C_1100) ) ),
    inference(resolution,[status(thm)],[c_24997,c_8])).

tff(c_25014,plain,(
    ! [B_1099] : k2_zfmisc_1(B_1099,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_25008])).

tff(c_33519,plain,(
    ! [B_1471] : k2_zfmisc_1(B_1471,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33384,c_33384,c_25014])).

tff(c_33540,plain,(
    ! [A_13,B_14,C_15] : k4_zfmisc_1(A_13,B_14,C_15,'#skF_9') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_33519,c_16])).

tff(c_24894,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24893,c_30])).

tff(c_33460,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33384,c_24894])).

tff(c_33875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33540,c_33460])).

tff(c_33877,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_31796])).

tff(c_24984,plain,(
    ! [C_1093,A_1094,B_1095,D_1096] :
      ( C_1093 = A_1094
      | k1_xboole_0 = B_1095
      | k1_xboole_0 = A_1094
      | k2_zfmisc_1(C_1093,D_1096) != k2_zfmisc_1(A_1094,B_1095) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32275,plain,(
    ! [A_1443,D_1440,B_1441,A_1442,C_1444,B_1439] :
      ( k3_zfmisc_1(A_1442,B_1441,C_1444) = A_1443
      | k1_xboole_0 = B_1439
      | k1_xboole_0 = A_1443
      | k4_zfmisc_1(A_1442,B_1441,C_1444,D_1440) != k2_zfmisc_1(A_1443,B_1439) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_24984])).

tff(c_33019,plain,(
    ! [A_1455,B_1456] :
      ( k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = A_1455
      | k1_xboole_0 = B_1456
      | k1_xboole_0 = A_1455
      | k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != k2_zfmisc_1(A_1455,B_1456) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24905,c_32275])).

tff(c_33061,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k3_zfmisc_1(A_13,B_14,C_15) = k3_zfmisc_1('#skF_2','#skF_7','#skF_8')
      | k1_xboole_0 = D_16
      | k3_zfmisc_1(A_13,B_14,C_15) = k1_xboole_0
      | k4_zfmisc_1(A_13,B_14,C_15,D_16) != k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_33019])).

tff(c_36394,plain,
    ( k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_9'
    | k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_33061])).

tff(c_36395,plain,
    ( k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4')
    | k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_33877,c_36394])).

tff(c_39669,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36395])).

tff(c_29210,plain,(
    ! [A_1348,B_1349,C_1350,D_1351] :
      ( k4_zfmisc_1(A_1348,B_1349,C_1350,D_1351) = k1_xboole_0
      | ~ v1_xboole_0(k3_zfmisc_1(A_1348,B_1349,C_1350)) ) ),
    inference(resolution,[status(thm)],[c_29140,c_8])).

tff(c_39714,plain,(
    ! [D_1351] :
      ( k4_zfmisc_1('#skF_2','#skF_3','#skF_4',D_1351) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39669,c_29210])).

tff(c_39805,plain,(
    ! [D_1351] : k4_zfmisc_1('#skF_2','#skF_3','#skF_4',D_1351) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_39714])).

tff(c_39837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39805,c_24894])).

tff(c_39839,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36395])).

tff(c_39838,plain,(
    k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36395])).

tff(c_24,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] :
      ( E_24 = B_21
      | k3_zfmisc_1(A_20,B_21,C_22) = k1_xboole_0
      | k3_zfmisc_1(D_23,E_24,F_25) != k3_zfmisc_1(A_20,B_21,C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39955,plain,(
    ! [E_24,D_23,F_25] :
      ( E_24 = '#skF_7'
      | k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = k1_xboole_0
      | k3_zfmisc_1(D_23,E_24,F_25) != k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39838,c_24])).

tff(c_39973,plain,(
    ! [E_24,D_23,F_25] :
      ( E_24 = '#skF_7'
      | k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k3_zfmisc_1(D_23,E_24,F_25) != k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39838,c_39955])).

tff(c_39974,plain,(
    ! [E_24,D_23,F_25] :
      ( E_24 = '#skF_7'
      | k3_zfmisc_1(D_23,E_24,F_25) != k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_39839,c_39973])).

tff(c_41814,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_39974])).

tff(c_41816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24899,c_41814])).

tff(c_41817,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24892])).

tff(c_41818,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24892])).

tff(c_41819,plain,(
    k4_zfmisc_1('#skF_2','#skF_7','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17362,c_24893,c_32])).

tff(c_41824,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41818,c_41819])).

tff(c_42002,plain,(
    ! [D_1693,B_1694,A_1695,C_1696] :
      ( D_1693 = B_1694
      | k1_xboole_0 = B_1694
      | k1_xboole_0 = A_1695
      | k2_zfmisc_1(C_1696,D_1693) != k2_zfmisc_1(A_1695,B_1694) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_45575,plain,(
    ! [C_1929,B_1925,A_1928,D_1924,D_1926,C_1927] :
      ( D_1926 = D_1924
      | k1_xboole_0 = D_1924
      | k3_zfmisc_1(A_1928,B_1925,C_1929) = k1_xboole_0
      | k4_zfmisc_1(A_1928,B_1925,C_1929,D_1924) != k2_zfmisc_1(C_1927,D_1926) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_42002])).

tff(c_45632,plain,(
    ! [D_1926,C_1927] :
      ( D_1926 = '#skF_9'
      | k1_xboole_0 = '#skF_9'
      | k3_zfmisc_1('#skF_2','#skF_3','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != k2_zfmisc_1(C_1927,D_1926) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41824,c_45575])).

tff(c_45779,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_45632])).

tff(c_41867,plain,(
    ! [A_1673,B_1674,C_1675,D_1676] : k2_zfmisc_1(k3_zfmisc_1(A_1673,B_1674,C_1675),D_1676) = k4_zfmisc_1(A_1673,B_1674,C_1675,D_1676) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_43241,plain,(
    ! [C_1817,B_1819,A_1815,A_1816,D_1818] :
      ( r2_hidden(k1_mcart_1(A_1815),k3_zfmisc_1(A_1816,B_1819,C_1817))
      | ~ r2_hidden(A_1815,k4_zfmisc_1(A_1816,B_1819,C_1817,D_1818)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41867,c_20])).

tff(c_43313,plain,(
    ! [A_1828] :
      ( r2_hidden(k1_mcart_1(A_1828),k3_zfmisc_1('#skF_2','#skF_3','#skF_8'))
      | ~ r2_hidden(A_1828,k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41824,c_43241])).

tff(c_43323,plain,(
    ! [A_1828] :
      ( ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_8'))
      | ~ r2_hidden(A_1828,k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_43313,c_2])).

tff(c_44088,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_43323])).

tff(c_45780,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45779,c_44088])).

tff(c_45784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_45780])).

tff(c_45785,plain,(
    ! [D_1926,C_1927] :
      ( k1_xboole_0 = '#skF_9'
      | D_1926 = '#skF_9'
      | k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != k2_zfmisc_1(C_1927,D_1926) ) ),
    inference(splitRight,[status(thm)],[c_45632])).

tff(c_46275,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_45785])).

tff(c_41834,plain,(
    ! [A_1663,C_1664,B_1665] :
      ( r2_hidden(k2_mcart_1(A_1663),C_1664)
      | ~ r2_hidden(A_1663,k2_zfmisc_1(B_1665,C_1664)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42243,plain,(
    ! [B_1753,C_1754] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1753,C_1754))),C_1754)
      | v1_xboole_0(k2_zfmisc_1(B_1753,C_1754)) ) ),
    inference(resolution,[status(thm)],[c_4,c_41834])).

tff(c_41829,plain,(
    ! [A_1660,B_1661,C_1662] :
      ( r2_hidden(k1_mcart_1(A_1660),B_1661)
      | ~ r2_hidden(A_1660,k2_zfmisc_1(B_1661,C_1662)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_41883,plain,(
    ! [B_1677,C_1678] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1677,C_1678))),B_1677)
      | v1_xboole_0(k2_zfmisc_1(B_1677,C_1678)) ) ),
    inference(resolution,[status(thm)],[c_4,c_41829])).

tff(c_41928,plain,(
    ! [B_1683,C_1684] :
      ( ~ v1_xboole_0(B_1683)
      | v1_xboole_0(k2_zfmisc_1(B_1683,C_1684)) ) ),
    inference(resolution,[status(thm)],[c_41883,c_2])).

tff(c_41939,plain,(
    ! [B_1685,C_1686] :
      ( k2_zfmisc_1(B_1685,C_1686) = k1_xboole_0
      | ~ v1_xboole_0(B_1685) ) ),
    inference(resolution,[status(thm)],[c_41928,c_8])).

tff(c_41947,plain,(
    ! [C_1687] : k2_zfmisc_1(k1_xboole_0,C_1687) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_41939])).

tff(c_42030,plain,(
    ! [A_1700] :
      ( r2_hidden(k1_mcart_1(A_1700),k1_xboole_0)
      | ~ r2_hidden(A_1700,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41947,c_20])).

tff(c_42033,plain,(
    ! [A_1700] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_1700,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42030,c_2])).

tff(c_42036,plain,(
    ! [A_1700] : ~ r2_hidden(A_1700,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42033])).

tff(c_42332,plain,(
    ! [B_1759] : v1_xboole_0(k2_zfmisc_1(B_1759,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_42243,c_42036])).

tff(c_42362,plain,(
    ! [B_1759] : k2_zfmisc_1(B_1759,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42332,c_8])).

tff(c_46446,plain,(
    ! [B_1963] : k2_zfmisc_1(B_1963,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46275,c_46275,c_42362])).

tff(c_46470,plain,(
    ! [A_13,B_14,C_15] : k4_zfmisc_1(A_13,B_14,C_15,'#skF_9') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_46446,c_16])).

tff(c_46334,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46275,c_24894])).

tff(c_46975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46470,c_46334])).

tff(c_46977,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_45785])).

tff(c_41915,plain,(
    ! [C_1679,A_1680,B_1681,D_1682] :
      ( C_1679 = A_1680
      | k1_xboole_0 = B_1681
      | k1_xboole_0 = A_1680
      | k2_zfmisc_1(C_1679,D_1682) != k2_zfmisc_1(A_1680,B_1681) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_45933,plain,(
    ! [D_1940,B_1942,A_1944,B_1941,C_1945,A_1943] :
      ( k3_zfmisc_1(A_1943,B_1941,C_1945) = A_1944
      | k1_xboole_0 = B_1942
      | k1_xboole_0 = A_1944
      | k4_zfmisc_1(A_1943,B_1941,C_1945,D_1940) != k2_zfmisc_1(A_1944,B_1942) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_41915])).

tff(c_46006,plain,(
    ! [A_1946,B_1947] :
      ( k3_zfmisc_1('#skF_2','#skF_3','#skF_8') = A_1946
      | k1_xboole_0 = B_1947
      | k1_xboole_0 = A_1946
      | k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != k2_zfmisc_1(A_1946,B_1947) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41824,c_45933])).

tff(c_46033,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k3_zfmisc_1(A_13,B_14,C_15) = k3_zfmisc_1('#skF_2','#skF_3','#skF_8')
      | k1_xboole_0 = D_16
      | k3_zfmisc_1(A_13,B_14,C_15) = k1_xboole_0
      | k4_zfmisc_1(A_13,B_14,C_15,D_16) != k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_46006])).

tff(c_48354,plain,
    ( k3_zfmisc_1('#skF_2','#skF_3','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_9'
    | k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_46033])).

tff(c_48355,plain,
    ( k3_zfmisc_1('#skF_2','#skF_3','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4')
    | k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_46977,c_48354])).

tff(c_50927,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48355])).

tff(c_47149,plain,(
    ! [A_2011,B_2012,C_2013,D_2014] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_2011,B_2012,C_2013))
      | v1_xboole_0(k4_zfmisc_1(A_2011,B_2012,C_2013,D_2014)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_41928])).

tff(c_47219,plain,(
    ! [A_2011,B_2012,C_2013,D_2014] :
      ( k4_zfmisc_1(A_2011,B_2012,C_2013,D_2014) = k1_xboole_0
      | ~ v1_xboole_0(k3_zfmisc_1(A_2011,B_2012,C_2013)) ) ),
    inference(resolution,[status(thm)],[c_47149,c_8])).

tff(c_50957,plain,(
    ! [D_2014] :
      ( k4_zfmisc_1('#skF_2','#skF_3','#skF_4',D_2014) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50927,c_47219])).

tff(c_51028,plain,(
    ! [D_2014] : k4_zfmisc_1('#skF_2','#skF_3','#skF_4',D_2014) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50957])).

tff(c_51055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51028,c_24894])).

tff(c_51057,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48355])).

tff(c_51056,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48355])).

tff(c_22,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] :
      ( F_25 = C_22
      | k3_zfmisc_1(A_20,B_21,C_22) = k1_xboole_0
      | k3_zfmisc_1(D_23,E_24,F_25) != k3_zfmisc_1(A_20,B_21,C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_51146,plain,(
    ! [F_25,D_23,E_24] :
      ( F_25 = '#skF_8'
      | k3_zfmisc_1('#skF_2','#skF_3','#skF_8') = k1_xboole_0
      | k3_zfmisc_1(D_23,E_24,F_25) != k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51056,c_22])).

tff(c_51161,plain,(
    ! [F_25,D_23,E_24] :
      ( F_25 = '#skF_8'
      | k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k3_zfmisc_1(D_23,E_24,F_25) != k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51056,c_51146])).

tff(c_51162,plain,(
    ! [F_25,D_23,E_24] :
      ( F_25 = '#skF_8'
      | k3_zfmisc_1(D_23,E_24,F_25) != k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_51057,c_51161])).

tff(c_51337,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_51162])).

tff(c_51339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41817,c_51337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.53/5.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.53/5.52  
% 12.53/5.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.53/5.52  %$ r2_hidden > v1_xboole_0 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4
% 12.53/5.52  
% 12.53/5.52  %Foreground sorts:
% 12.53/5.52  
% 12.53/5.52  
% 12.53/5.52  %Background operators:
% 12.53/5.52  
% 12.53/5.52  
% 12.53/5.52  %Foreground operators:
% 12.53/5.52  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 12.53/5.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.53/5.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.53/5.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.53/5.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.53/5.52  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 12.53/5.52  tff('#skF_7', type, '#skF_7': $i).
% 12.53/5.52  tff('#skF_5', type, '#skF_5': $i).
% 12.53/5.52  tff('#skF_6', type, '#skF_6': $i).
% 12.53/5.52  tff('#skF_2', type, '#skF_2': $i).
% 12.53/5.52  tff('#skF_3', type, '#skF_3': $i).
% 12.53/5.52  tff('#skF_9', type, '#skF_9': $i).
% 12.53/5.52  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 12.53/5.52  tff('#skF_8', type, '#skF_8': $i).
% 12.53/5.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.53/5.52  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 12.53/5.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.53/5.52  tff('#skF_4', type, '#skF_4': $i).
% 12.53/5.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.53/5.52  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 12.53/5.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.53/5.52  
% 12.82/5.57  tff(f_50, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 12.82/5.57  tff(f_48, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 12.82/5.57  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.82/5.57  tff(f_56, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 12.82/5.57  tff(f_32, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 12.82/5.57  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 12.82/5.57  tff(f_79, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_mcart_1)).
% 12.82/5.57  tff(f_46, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 12.82/5.57  tff(f_66, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 12.82/5.57  tff(c_16, plain, (![A_13, B_14, C_15, D_16]: (k2_zfmisc_1(k3_zfmisc_1(A_13, B_14, C_15), D_16)=k4_zfmisc_1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.82/5.57  tff(c_14, plain, (![A_10, B_11, C_12]: (k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12)=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.82/5.57  tff(c_17373, plain, (![A_674, B_675, C_676]: (k2_zfmisc_1(k2_zfmisc_1(A_674, B_675), C_676)=k3_zfmisc_1(A_674, B_675, C_676))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.82/5.57  tff(c_17384, plain, (![A_10, B_11, C_12, C_676]: (k3_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12, C_676)=k2_zfmisc_1(k3_zfmisc_1(A_10, B_11, C_12), C_676))), inference(superposition, [status(thm), theory('equality')], [c_14, c_17373])).
% 12.82/5.57  tff(c_18235, plain, (![A_10, B_11, C_12, C_676]: (k3_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12, C_676)=k4_zfmisc_1(A_10, B_11, C_12, C_676))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_17384])).
% 12.82/5.57  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.82/5.57  tff(c_17390, plain, (![A_677, C_678, B_679]: (r2_hidden(k2_mcart_1(A_677), C_678) | ~r2_hidden(A_677, k2_zfmisc_1(B_679, C_678)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.82/5.57  tff(c_17402, plain, (![A_680, C_681, A_682, B_683]: (r2_hidden(k2_mcart_1(A_680), C_681) | ~r2_hidden(A_680, k3_zfmisc_1(A_682, B_683, C_681)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_17390])).
% 12.82/5.57  tff(c_17406, plain, (![A_682, B_683, C_681]: (r2_hidden(k2_mcart_1('#skF_1'(k3_zfmisc_1(A_682, B_683, C_681))), C_681) | v1_xboole_0(k3_zfmisc_1(A_682, B_683, C_681)))), inference(resolution, [status(thm)], [c_4, c_17402])).
% 12.82/5.57  tff(c_6, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.82/5.57  tff(c_33, plain, (![A_26]: (k1_xboole_0=A_26 | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.82/5.57  tff(c_37, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_33])).
% 12.82/5.57  tff(c_38, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37, c_6])).
% 12.82/5.57  tff(c_17368, plain, (![A_671, B_672, C_673]: (r2_hidden(k1_mcart_1(A_671), B_672) | ~r2_hidden(A_671, k2_zfmisc_1(B_672, C_673)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.82/5.57  tff(c_17423, plain, (![B_688, C_689]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_688, C_689))), B_688) | v1_xboole_0(k2_zfmisc_1(B_688, C_689)))), inference(resolution, [status(thm)], [c_4, c_17368])).
% 12.82/5.57  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.82/5.57  tff(c_17451, plain, (![B_690, C_691]: (~v1_xboole_0(B_690) | v1_xboole_0(k2_zfmisc_1(B_690, C_691)))), inference(resolution, [status(thm)], [c_17423, c_2])).
% 12.82/5.57  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.82/5.57  tff(c_17462, plain, (![B_692, C_693]: (k2_zfmisc_1(B_692, C_693)=k1_xboole_0 | ~v1_xboole_0(B_692))), inference(resolution, [status(thm)], [c_17451, c_8])).
% 12.82/5.57  tff(c_17469, plain, (![C_693]: (k2_zfmisc_1(k1_xboole_0, C_693)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_17462])).
% 12.82/5.57  tff(c_28, plain, ('#skF_5'!='#skF_9' | '#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.82/5.57  tff(c_54, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_28])).
% 12.82/5.57  tff(c_32, plain, (k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.82/5.57  tff(c_177, plain, (![D_57, B_58, A_59, C_60]: (D_57=B_58 | k1_xboole_0=B_58 | k1_xboole_0=A_59 | k2_zfmisc_1(C_60, D_57)!=k2_zfmisc_1(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.82/5.57  tff(c_2126, plain, (![C_221, D_216, B_217, A_220, B_218, A_219]: (D_216=B_218 | k1_xboole_0=B_218 | k1_xboole_0=A_219 | k4_zfmisc_1(A_220, B_217, C_221, D_216)!=k2_zfmisc_1(A_219, B_218))), inference(superposition, [status(thm), theory('equality')], [c_16, c_177])).
% 12.82/5.57  tff(c_2305, plain, (![B_226, A_227]: (B_226='#skF_9' | k1_xboole_0=B_226 | k1_xboole_0=A_227 | k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k2_zfmisc_1(A_227, B_226))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2126])).
% 12.82/5.57  tff(c_2323, plain, (![D_16, A_13, B_14, C_15]: (D_16='#skF_9' | k1_xboole_0=D_16 | k3_zfmisc_1(A_13, B_14, C_15)=k1_xboole_0 | k4_zfmisc_1(A_13, B_14, C_15, D_16)!=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2305])).
% 12.82/5.57  tff(c_11506, plain, ('#skF_5'='#skF_9' | k1_xboole_0='#skF_5' | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_2323])).
% 12.82/5.57  tff(c_11571, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_11506])).
% 12.82/5.57  tff(c_74, plain, (![A_33, B_34, C_35]: (r2_hidden(k1_mcart_1(A_33), B_34) | ~r2_hidden(A_33, k2_zfmisc_1(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.82/5.57  tff(c_126, plain, (![B_51, C_52]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_51, C_52))), B_51) | v1_xboole_0(k2_zfmisc_1(B_51, C_52)))), inference(resolution, [status(thm)], [c_4, c_74])).
% 12.82/5.57  tff(c_154, plain, (![B_53, C_54]: (~v1_xboole_0(B_53) | v1_xboole_0(k2_zfmisc_1(B_53, C_54)))), inference(resolution, [status(thm)], [c_126, c_2])).
% 12.82/5.57  tff(c_4731, plain, (![A_335, B_336, C_337, D_338]: (~v1_xboole_0(k3_zfmisc_1(A_335, B_336, C_337)) | v1_xboole_0(k4_zfmisc_1(A_335, B_336, C_337, D_338)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_154])).
% 12.82/5.57  tff(c_4801, plain, (![A_335, B_336, C_337, D_338]: (k4_zfmisc_1(A_335, B_336, C_337, D_338)=k1_xboole_0 | ~v1_xboole_0(k3_zfmisc_1(A_335, B_336, C_337)))), inference(resolution, [status(thm)], [c_4731, c_8])).
% 12.82/5.57  tff(c_11625, plain, (![D_338]: (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', D_338)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11571, c_4801])).
% 12.82/5.57  tff(c_11701, plain, (![D_338]: (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', D_338)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_11625])).
% 12.82/5.57  tff(c_30, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.82/5.57  tff(c_11724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11701, c_30])).
% 12.82/5.57  tff(c_11726, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_11506])).
% 12.82/5.57  tff(c_93, plain, (![A_43, B_44, C_45, D_46]: (k2_zfmisc_1(k3_zfmisc_1(A_43, B_44, C_45), D_46)=k4_zfmisc_1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.82/5.57  tff(c_18, plain, (![A_17, C_19, B_18]: (r2_hidden(k2_mcart_1(A_17), C_19) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.82/5.57  tff(c_465, plain, (![A_119, A_122, D_121, C_120, B_123]: (r2_hidden(k2_mcart_1(A_119), D_121) | ~r2_hidden(A_119, k4_zfmisc_1(A_122, B_123, C_120, D_121)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_18])).
% 12.82/5.57  tff(c_699, plain, (![A_130]: (r2_hidden(k2_mcart_1(A_130), '#skF_9') | ~r2_hidden(A_130, k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_465])).
% 12.82/5.57  tff(c_703, plain, (![A_130]: (~v1_xboole_0('#skF_9') | ~r2_hidden(A_130, k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_699, c_2])).
% 12.82/5.57  tff(c_921, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_703])).
% 12.82/5.57  tff(c_165, plain, (![B_55, C_56]: (k2_zfmisc_1(B_55, C_56)=k1_xboole_0 | ~v1_xboole_0(B_55))), inference(resolution, [status(thm)], [c_154, c_8])).
% 12.82/5.57  tff(c_172, plain, (![C_56]: (k2_zfmisc_1(k1_xboole_0, C_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_165])).
% 12.82/5.57  tff(c_4043, plain, (![B_301, C_305, D_303, D_300, A_302, C_304]: (D_303=D_300 | k1_xboole_0=D_300 | k3_zfmisc_1(A_302, B_301, C_304)=k1_xboole_0 | k4_zfmisc_1(A_302, B_301, C_304, D_300)!=k2_zfmisc_1(C_305, D_303))), inference(superposition, [status(thm), theory('equality')], [c_16, c_177])).
% 12.82/5.57  tff(c_4109, plain, (![D_303, C_305]: (D_303='#skF_9' | k1_xboole_0='#skF_9' | k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k2_zfmisc_1(C_305, D_303))), inference(superposition, [status(thm), theory('equality')], [c_32, c_4043])).
% 12.82/5.57  tff(c_4115, plain, (k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4109])).
% 12.82/5.57  tff(c_4168, plain, (![D_16]: (k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', D_16)=k2_zfmisc_1(k1_xboole_0, D_16))), inference(superposition, [status(thm), theory('equality')], [c_4115, c_16])).
% 12.82/5.57  tff(c_4182, plain, (![D_16]: (k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', D_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_172, c_4168])).
% 12.82/5.57  tff(c_4184, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4182, c_32])).
% 12.82/5.57  tff(c_4186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_4184])).
% 12.82/5.57  tff(c_4187, plain, (![D_303, C_305]: (k1_xboole_0='#skF_9' | D_303='#skF_9' | k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k2_zfmisc_1(C_305, D_303))), inference(splitRight, [status(thm)], [c_4109])).
% 12.82/5.57  tff(c_4523, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_4187])).
% 12.82/5.57  tff(c_4583, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4523, c_38])).
% 12.82/5.57  tff(c_4587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_921, c_4583])).
% 12.82/5.57  tff(c_4589, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_4187])).
% 12.82/5.57  tff(c_11725, plain, (k1_xboole_0='#skF_5' | '#skF_5'='#skF_9'), inference(splitRight, [status(thm)], [c_11506])).
% 12.82/5.57  tff(c_11727, plain, ('#skF_5'='#skF_9'), inference(splitLeft, [status(thm)], [c_11725])).
% 12.82/5.57  tff(c_113, plain, (![C_47, A_48, B_49, D_50]: (C_47=A_48 | k1_xboole_0=B_49 | k1_xboole_0=A_48 | k2_zfmisc_1(C_47, D_50)!=k2_zfmisc_1(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.82/5.57  tff(c_4189, plain, (![B_307, C_311, A_310, D_306, A_309, B_308]: (k3_zfmisc_1(A_310, B_307, C_311)=A_309 | k1_xboole_0=B_308 | k1_xboole_0=A_309 | k4_zfmisc_1(A_310, B_307, C_311, D_306)!=k2_zfmisc_1(A_309, B_308))), inference(superposition, [status(thm), theory('equality')], [c_16, c_113])).
% 12.82/5.57  tff(c_4262, plain, (![A_312, B_313]: (k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')=A_312 | k1_xboole_0=B_313 | k1_xboole_0=A_312 | k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k2_zfmisc_1(A_312, B_313))), inference(superposition, [status(thm), theory('equality')], [c_32, c_4189])).
% 12.82/5.57  tff(c_4289, plain, (![A_13, B_14, C_15, D_16]: (k3_zfmisc_1(A_13, B_14, C_15)=k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8') | k1_xboole_0=D_16 | k3_zfmisc_1(A_13, B_14, C_15)=k1_xboole_0 | k4_zfmisc_1(A_13, B_14, C_15, D_16)!=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4262])).
% 12.82/5.57  tff(c_15268, plain, (![A_13, B_14, C_15, D_16]: (k3_zfmisc_1(A_13, B_14, C_15)=k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8') | k1_xboole_0=D_16 | k3_zfmisc_1(A_13, B_14, C_15)=k1_xboole_0 | k4_zfmisc_1(A_13, B_14, C_15, D_16)!=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_11727, c_4289])).
% 12.82/5.57  tff(c_15271, plain, (k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4') | k1_xboole_0='#skF_9' | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_15268])).
% 12.82/5.57  tff(c_15272, plain, (k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_11726, c_4589, c_15271])).
% 12.82/5.57  tff(c_26, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (D_23=A_20 | k3_zfmisc_1(A_20, B_21, C_22)=k1_xboole_0 | k3_zfmisc_1(D_23, E_24, F_25)!=k3_zfmisc_1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.82/5.57  tff(c_15451, plain, (![D_23, E_24, F_25]: (D_23='#skF_6' | k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0 | k3_zfmisc_1(D_23, E_24, F_25)!=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_15272, c_26])).
% 12.82/5.57  tff(c_15479, plain, (![D_23, E_24, F_25]: (D_23='#skF_6' | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k3_zfmisc_1(D_23, E_24, F_25)!=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15272, c_15451])).
% 12.82/5.57  tff(c_15480, plain, (![D_23, E_24, F_25]: (D_23='#skF_6' | k3_zfmisc_1(D_23, E_24, F_25)!=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_11726, c_15479])).
% 12.82/5.57  tff(c_15914, plain, ('#skF_6'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_15480])).
% 12.82/5.57  tff(c_15916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_15914])).
% 12.82/5.57  tff(c_15917, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_11725])).
% 12.82/5.57  tff(c_81, plain, (![A_36, C_37, B_38]: (r2_hidden(k2_mcart_1(A_36), C_37) | ~r2_hidden(A_36, k2_zfmisc_1(B_38, C_37)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.82/5.57  tff(c_480, plain, (![B_124, C_125]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_124, C_125))), C_125) | v1_xboole_0(k2_zfmisc_1(B_124, C_125)))), inference(resolution, [status(thm)], [c_4, c_81])).
% 12.82/5.57  tff(c_190, plain, (![C_61]: (k2_zfmisc_1(k1_xboole_0, C_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_165])).
% 12.82/5.57  tff(c_256, plain, (![A_70, C_71]: (r2_hidden(k2_mcart_1(A_70), C_71) | ~r2_hidden(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_190, c_18])).
% 12.82/5.57  tff(c_272, plain, (![C_71, A_70]: (~v1_xboole_0(C_71) | ~r2_hidden(A_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_256, c_2])).
% 12.82/5.57  tff(c_285, plain, (![A_70]: (~r2_hidden(A_70, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_272])).
% 12.82/5.57  tff(c_518, plain, (![B_126]: (v1_xboole_0(k2_zfmisc_1(B_126, k1_xboole_0)))), inference(resolution, [status(thm)], [c_480, c_285])).
% 12.82/5.57  tff(c_548, plain, (![B_126]: (k2_zfmisc_1(B_126, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_518, c_8])).
% 12.82/5.57  tff(c_16187, plain, (![B_613]: (k2_zfmisc_1(B_613, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15917, c_15917, c_548])).
% 12.82/5.57  tff(c_16246, plain, (![A_13, B_14, C_15]: (k4_zfmisc_1(A_13, B_14, C_15, '#skF_5')='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16, c_16187])).
% 12.82/5.57  tff(c_15999, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_15917, c_30])).
% 12.82/5.57  tff(c_17012, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16246, c_15999])).
% 12.82/5.57  tff(c_17014, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_703])).
% 12.82/5.57  tff(c_17030, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_17014, c_8])).
% 12.82/5.57  tff(c_17052, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_17030, c_30])).
% 12.82/5.57  tff(c_17043, plain, (![A_70]: (~r2_hidden(A_70, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_17030, c_285])).
% 12.82/5.57  tff(c_474, plain, (![A_119]: (r2_hidden(k2_mcart_1(A_119), '#skF_9') | ~r2_hidden(A_119, k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_465])).
% 12.82/5.57  tff(c_17221, plain, (![A_664]: (~r2_hidden(A_664, k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_17043, c_474])).
% 12.82/5.57  tff(c_17236, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_17221])).
% 12.82/5.57  tff(c_17055, plain, (![A_5]: (A_5='#skF_9' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_17030, c_8])).
% 12.82/5.57  tff(c_17350, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_17236, c_17055])).
% 12.82/5.57  tff(c_17354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17052, c_17350])).
% 12.82/5.57  tff(c_17355, plain, (![C_71]: (~v1_xboole_0(C_71))), inference(splitRight, [status(thm)], [c_272])).
% 12.82/5.57  tff(c_17360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17355, c_38])).
% 12.82/5.57  tff(c_17361, plain, ('#skF_7'!='#skF_3' | '#skF_8'!='#skF_4' | '#skF_5'!='#skF_9'), inference(splitRight, [status(thm)], [c_28])).
% 12.82/5.57  tff(c_17367, plain, ('#skF_5'!='#skF_9'), inference(splitLeft, [status(thm)], [c_17361])).
% 12.82/5.57  tff(c_17362, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 12.82/5.57  tff(c_17397, plain, (k4_zfmisc_1('#skF_2', '#skF_7', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17362, c_32])).
% 12.82/5.57  tff(c_17511, plain, (![D_697, B_698, A_699, C_700]: (D_697=B_698 | k1_xboole_0=B_698 | k1_xboole_0=A_699 | k2_zfmisc_1(C_700, D_697)!=k2_zfmisc_1(A_699, B_698))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.82/5.57  tff(c_18943, plain, (![C_844, B_840, A_842, B_841, A_843, D_839]: (D_839=B_840 | k1_xboole_0=B_840 | k1_xboole_0=A_842 | k4_zfmisc_1(A_843, B_841, C_844, D_839)!=k2_zfmisc_1(A_842, B_840))), inference(superposition, [status(thm), theory('equality')], [c_16, c_17511])).
% 12.82/5.57  tff(c_19220, plain, (![B_853, A_854]: (B_853='#skF_9' | k1_xboole_0=B_853 | k1_xboole_0=A_854 | k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k2_zfmisc_1(A_854, B_853))), inference(superposition, [status(thm), theory('equality')], [c_17397, c_18943])).
% 12.82/5.57  tff(c_19238, plain, (![D_16, A_13, B_14, C_15]: (D_16='#skF_9' | k1_xboole_0=D_16 | k3_zfmisc_1(A_13, B_14, C_15)=k1_xboole_0 | k4_zfmisc_1(A_13, B_14, C_15, D_16)!=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_19220])).
% 12.82/5.57  tff(c_23906, plain, ('#skF_5'='#skF_9' | k1_xboole_0='#skF_5' | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_19238])).
% 12.82/5.57  tff(c_23907, plain, (k1_xboole_0='#skF_5' | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_17367, c_23906])).
% 12.82/5.57  tff(c_23958, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_23907])).
% 12.82/5.57  tff(c_24033, plain, (![D_16]: (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', D_16)=k2_zfmisc_1(k1_xboole_0, D_16))), inference(superposition, [status(thm), theory('equality')], [c_23958, c_16])).
% 12.82/5.57  tff(c_24054, plain, (![D_16]: (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', D_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17469, c_24033])).
% 12.82/5.57  tff(c_24067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24054, c_30])).
% 12.82/5.57  tff(c_24068, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_23907])).
% 12.82/5.57  tff(c_17470, plain, (![C_694]: (k2_zfmisc_1(k1_xboole_0, C_694)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_17462])).
% 12.82/5.57  tff(c_20, plain, (![A_17, B_18, C_19]: (r2_hidden(k1_mcart_1(A_17), B_18) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.82/5.57  tff(c_17546, plain, (![A_707]: (r2_hidden(k1_mcart_1(A_707), k1_xboole_0) | ~r2_hidden(A_707, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_17470, c_20])).
% 12.82/5.57  tff(c_17549, plain, (![A_707]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_707, k1_xboole_0))), inference(resolution, [status(thm)], [c_17546, c_2])).
% 12.82/5.57  tff(c_17552, plain, (![A_707]: (~r2_hidden(A_707, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_17549])).
% 12.82/5.57  tff(c_24149, plain, (![A_1029]: (~r2_hidden(A_1029, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_24068, c_17552])).
% 12.82/5.57  tff(c_24421, plain, (![A_1044, B_1045]: (v1_xboole_0(k3_zfmisc_1(A_1044, B_1045, '#skF_5')))), inference(resolution, [status(thm)], [c_17406, c_24149])).
% 12.82/5.57  tff(c_24748, plain, (![A_1064, B_1065, C_1066]: (v1_xboole_0(k4_zfmisc_1(A_1064, B_1065, C_1066, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_18235, c_24421])).
% 12.82/5.57  tff(c_24140, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_24068, c_8])).
% 12.82/5.57  tff(c_24765, plain, (![A_1064, B_1065, C_1066]: (k4_zfmisc_1(A_1064, B_1065, C_1066, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_24748, c_24140])).
% 12.82/5.57  tff(c_24137, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24068, c_30])).
% 12.82/5.57  tff(c_24891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24765, c_24137])).
% 12.82/5.57  tff(c_24892, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_17361])).
% 12.82/5.57  tff(c_24899, plain, ('#skF_7'!='#skF_3'), inference(splitLeft, [status(thm)], [c_24892])).
% 12.82/5.57  tff(c_24893, plain, ('#skF_5'='#skF_9'), inference(splitRight, [status(thm)], [c_17361])).
% 12.82/5.57  tff(c_24905, plain, (k4_zfmisc_1('#skF_2', '#skF_7', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_24893, c_17362, c_32])).
% 12.82/5.57  tff(c_25065, plain, (![D_1102, B_1103, A_1104, C_1105]: (D_1102=B_1103 | k1_xboole_0=B_1103 | k1_xboole_0=A_1104 | k2_zfmisc_1(C_1105, D_1102)!=k2_zfmisc_1(A_1104, B_1103))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.82/5.57  tff(c_31283, plain, (![C_1414, D_1409, C_1413, B_1410, A_1412, D_1411]: (D_1411=D_1409 | k1_xboole_0=D_1409 | k3_zfmisc_1(A_1412, B_1410, C_1414)=k1_xboole_0 | k4_zfmisc_1(A_1412, B_1410, C_1414, D_1409)!=k2_zfmisc_1(C_1413, D_1411))), inference(superposition, [status(thm), theory('equality')], [c_16, c_25065])).
% 12.82/5.57  tff(c_31361, plain, (![D_1411, C_1413]: (D_1411='#skF_9' | k1_xboole_0='#skF_9' | k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!=k2_zfmisc_1(C_1413, D_1411))), inference(superposition, [status(thm), theory('equality')], [c_24905, c_31283])).
% 12.82/5.57  tff(c_31790, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_31361])).
% 12.82/5.57  tff(c_24900, plain, (![A_1074, B_1075, C_1076]: (r2_hidden(k1_mcart_1(A_1074), B_1075) | ~r2_hidden(A_1074, k2_zfmisc_1(B_1075, C_1076)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.82/5.57  tff(c_25752, plain, (![B_1185, C_1186]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1185, C_1186))), B_1185) | v1_xboole_0(k2_zfmisc_1(B_1185, C_1186)))), inference(resolution, [status(thm)], [c_4, c_24900])).
% 12.82/5.57  tff(c_25993, plain, (![B_1191, C_1192]: (~v1_xboole_0(B_1191) | v1_xboole_0(k2_zfmisc_1(B_1191, C_1192)))), inference(resolution, [status(thm)], [c_25752, c_2])).
% 12.82/5.57  tff(c_29140, plain, (![A_1348, B_1349, C_1350, D_1351]: (~v1_xboole_0(k3_zfmisc_1(A_1348, B_1349, C_1350)) | v1_xboole_0(k4_zfmisc_1(A_1348, B_1349, C_1350, D_1351)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_25993])).
% 12.82/5.57  tff(c_29200, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')) | v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_24905, c_29140])).
% 12.82/5.57  tff(c_30418, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_29200])).
% 12.82/5.57  tff(c_31791, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_31790, c_30418])).
% 12.82/5.57  tff(c_31795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_31791])).
% 12.82/5.57  tff(c_31796, plain, (![D_1411, C_1413]: (k1_xboole_0='#skF_9' | D_1411='#skF_9' | k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!=k2_zfmisc_1(C_1413, D_1411))), inference(splitRight, [status(thm)], [c_31361])).
% 12.82/5.57  tff(c_33384, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_31796])).
% 12.82/5.57  tff(c_24910, plain, (![A_1077, C_1078, B_1079]: (r2_hidden(k2_mcart_1(A_1077), C_1078) | ~r2_hidden(A_1077, k2_zfmisc_1(B_1079, C_1078)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.82/5.57  tff(c_24955, plain, (![B_1091, C_1092]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1091, C_1092))), C_1092) | v1_xboole_0(k2_zfmisc_1(B_1091, C_1092)))), inference(resolution, [status(thm)], [c_4, c_24910])).
% 12.82/5.57  tff(c_24997, plain, (![C_1097, B_1098]: (~v1_xboole_0(C_1097) | v1_xboole_0(k2_zfmisc_1(B_1098, C_1097)))), inference(resolution, [status(thm)], [c_24955, c_2])).
% 12.82/5.57  tff(c_25008, plain, (![B_1099, C_1100]: (k2_zfmisc_1(B_1099, C_1100)=k1_xboole_0 | ~v1_xboole_0(C_1100))), inference(resolution, [status(thm)], [c_24997, c_8])).
% 12.82/5.57  tff(c_25014, plain, (![B_1099]: (k2_zfmisc_1(B_1099, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_25008])).
% 12.82/5.57  tff(c_33519, plain, (![B_1471]: (k2_zfmisc_1(B_1471, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_33384, c_33384, c_25014])).
% 12.82/5.57  tff(c_33540, plain, (![A_13, B_14, C_15]: (k4_zfmisc_1(A_13, B_14, C_15, '#skF_9')='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_33519, c_16])).
% 12.82/5.57  tff(c_24894, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24893, c_30])).
% 12.82/5.57  tff(c_33460, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_33384, c_24894])).
% 12.82/5.57  tff(c_33875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33540, c_33460])).
% 12.82/5.57  tff(c_33877, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_31796])).
% 12.82/5.57  tff(c_24984, plain, (![C_1093, A_1094, B_1095, D_1096]: (C_1093=A_1094 | k1_xboole_0=B_1095 | k1_xboole_0=A_1094 | k2_zfmisc_1(C_1093, D_1096)!=k2_zfmisc_1(A_1094, B_1095))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.82/5.57  tff(c_32275, plain, (![A_1443, D_1440, B_1441, A_1442, C_1444, B_1439]: (k3_zfmisc_1(A_1442, B_1441, C_1444)=A_1443 | k1_xboole_0=B_1439 | k1_xboole_0=A_1443 | k4_zfmisc_1(A_1442, B_1441, C_1444, D_1440)!=k2_zfmisc_1(A_1443, B_1439))), inference(superposition, [status(thm), theory('equality')], [c_16, c_24984])).
% 12.82/5.57  tff(c_33019, plain, (![A_1455, B_1456]: (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=A_1455 | k1_xboole_0=B_1456 | k1_xboole_0=A_1455 | k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!=k2_zfmisc_1(A_1455, B_1456))), inference(superposition, [status(thm), theory('equality')], [c_24905, c_32275])).
% 12.82/5.57  tff(c_33061, plain, (![A_13, B_14, C_15, D_16]: (k3_zfmisc_1(A_13, B_14, C_15)=k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8') | k1_xboole_0=D_16 | k3_zfmisc_1(A_13, B_14, C_15)=k1_xboole_0 | k4_zfmisc_1(A_13, B_14, C_15, D_16)!=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_33019])).
% 12.82/5.57  tff(c_36394, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4') | k1_xboole_0='#skF_9' | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_33061])).
% 12.82/5.57  tff(c_36395, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4') | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_33877, c_36394])).
% 12.82/5.57  tff(c_39669, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36395])).
% 12.82/5.57  tff(c_29210, plain, (![A_1348, B_1349, C_1350, D_1351]: (k4_zfmisc_1(A_1348, B_1349, C_1350, D_1351)=k1_xboole_0 | ~v1_xboole_0(k3_zfmisc_1(A_1348, B_1349, C_1350)))), inference(resolution, [status(thm)], [c_29140, c_8])).
% 12.82/5.57  tff(c_39714, plain, (![D_1351]: (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', D_1351)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_39669, c_29210])).
% 12.82/5.57  tff(c_39805, plain, (![D_1351]: (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', D_1351)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_39714])).
% 12.82/5.57  tff(c_39837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39805, c_24894])).
% 12.82/5.57  tff(c_39839, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36395])).
% 12.82/5.57  tff(c_39838, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_36395])).
% 12.82/5.57  tff(c_24, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (E_24=B_21 | k3_zfmisc_1(A_20, B_21, C_22)=k1_xboole_0 | k3_zfmisc_1(D_23, E_24, F_25)!=k3_zfmisc_1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.82/5.57  tff(c_39955, plain, (![E_24, D_23, F_25]: (E_24='#skF_7' | k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=k1_xboole_0 | k3_zfmisc_1(D_23, E_24, F_25)!=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_39838, c_24])).
% 12.82/5.57  tff(c_39973, plain, (![E_24, D_23, F_25]: (E_24='#skF_7' | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k3_zfmisc_1(D_23, E_24, F_25)!=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39838, c_39955])).
% 12.82/5.57  tff(c_39974, plain, (![E_24, D_23, F_25]: (E_24='#skF_7' | k3_zfmisc_1(D_23, E_24, F_25)!=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_39839, c_39973])).
% 12.82/5.57  tff(c_41814, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_39974])).
% 12.82/5.57  tff(c_41816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24899, c_41814])).
% 12.82/5.57  tff(c_41817, plain, ('#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_24892])).
% 12.82/5.57  tff(c_41818, plain, ('#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_24892])).
% 12.82/5.57  tff(c_41819, plain, (k4_zfmisc_1('#skF_2', '#skF_7', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_17362, c_24893, c_32])).
% 12.82/5.57  tff(c_41824, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_41818, c_41819])).
% 12.82/5.57  tff(c_42002, plain, (![D_1693, B_1694, A_1695, C_1696]: (D_1693=B_1694 | k1_xboole_0=B_1694 | k1_xboole_0=A_1695 | k2_zfmisc_1(C_1696, D_1693)!=k2_zfmisc_1(A_1695, B_1694))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.82/5.57  tff(c_45575, plain, (![C_1929, B_1925, A_1928, D_1924, D_1926, C_1927]: (D_1926=D_1924 | k1_xboole_0=D_1924 | k3_zfmisc_1(A_1928, B_1925, C_1929)=k1_xboole_0 | k4_zfmisc_1(A_1928, B_1925, C_1929, D_1924)!=k2_zfmisc_1(C_1927, D_1926))), inference(superposition, [status(thm), theory('equality')], [c_16, c_42002])).
% 12.82/5.57  tff(c_45632, plain, (![D_1926, C_1927]: (D_1926='#skF_9' | k1_xboole_0='#skF_9' | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!=k2_zfmisc_1(C_1927, D_1926))), inference(superposition, [status(thm), theory('equality')], [c_41824, c_45575])).
% 12.82/5.57  tff(c_45779, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_45632])).
% 12.82/5.57  tff(c_41867, plain, (![A_1673, B_1674, C_1675, D_1676]: (k2_zfmisc_1(k3_zfmisc_1(A_1673, B_1674, C_1675), D_1676)=k4_zfmisc_1(A_1673, B_1674, C_1675, D_1676))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.82/5.57  tff(c_43241, plain, (![C_1817, B_1819, A_1815, A_1816, D_1818]: (r2_hidden(k1_mcart_1(A_1815), k3_zfmisc_1(A_1816, B_1819, C_1817)) | ~r2_hidden(A_1815, k4_zfmisc_1(A_1816, B_1819, C_1817, D_1818)))), inference(superposition, [status(thm), theory('equality')], [c_41867, c_20])).
% 12.82/5.57  tff(c_43313, plain, (![A_1828]: (r2_hidden(k1_mcart_1(A_1828), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')) | ~r2_hidden(A_1828, k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_41824, c_43241])).
% 12.82/5.57  tff(c_43323, plain, (![A_1828]: (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')) | ~r2_hidden(A_1828, k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')))), inference(resolution, [status(thm)], [c_43313, c_2])).
% 12.82/5.57  tff(c_44088, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'))), inference(splitLeft, [status(thm)], [c_43323])).
% 12.82/5.57  tff(c_45780, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_45779, c_44088])).
% 12.82/5.57  tff(c_45784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_45780])).
% 12.82/5.57  tff(c_45785, plain, (![D_1926, C_1927]: (k1_xboole_0='#skF_9' | D_1926='#skF_9' | k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!=k2_zfmisc_1(C_1927, D_1926))), inference(splitRight, [status(thm)], [c_45632])).
% 12.82/5.57  tff(c_46275, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_45785])).
% 12.82/5.57  tff(c_41834, plain, (![A_1663, C_1664, B_1665]: (r2_hidden(k2_mcart_1(A_1663), C_1664) | ~r2_hidden(A_1663, k2_zfmisc_1(B_1665, C_1664)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.82/5.57  tff(c_42243, plain, (![B_1753, C_1754]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1753, C_1754))), C_1754) | v1_xboole_0(k2_zfmisc_1(B_1753, C_1754)))), inference(resolution, [status(thm)], [c_4, c_41834])).
% 12.82/5.57  tff(c_41829, plain, (![A_1660, B_1661, C_1662]: (r2_hidden(k1_mcart_1(A_1660), B_1661) | ~r2_hidden(A_1660, k2_zfmisc_1(B_1661, C_1662)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.82/5.57  tff(c_41883, plain, (![B_1677, C_1678]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1677, C_1678))), B_1677) | v1_xboole_0(k2_zfmisc_1(B_1677, C_1678)))), inference(resolution, [status(thm)], [c_4, c_41829])).
% 12.82/5.57  tff(c_41928, plain, (![B_1683, C_1684]: (~v1_xboole_0(B_1683) | v1_xboole_0(k2_zfmisc_1(B_1683, C_1684)))), inference(resolution, [status(thm)], [c_41883, c_2])).
% 12.82/5.57  tff(c_41939, plain, (![B_1685, C_1686]: (k2_zfmisc_1(B_1685, C_1686)=k1_xboole_0 | ~v1_xboole_0(B_1685))), inference(resolution, [status(thm)], [c_41928, c_8])).
% 12.82/5.57  tff(c_41947, plain, (![C_1687]: (k2_zfmisc_1(k1_xboole_0, C_1687)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_41939])).
% 12.82/5.57  tff(c_42030, plain, (![A_1700]: (r2_hidden(k1_mcart_1(A_1700), k1_xboole_0) | ~r2_hidden(A_1700, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_41947, c_20])).
% 12.82/5.57  tff(c_42033, plain, (![A_1700]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_1700, k1_xboole_0))), inference(resolution, [status(thm)], [c_42030, c_2])).
% 12.82/5.57  tff(c_42036, plain, (![A_1700]: (~r2_hidden(A_1700, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42033])).
% 12.82/5.57  tff(c_42332, plain, (![B_1759]: (v1_xboole_0(k2_zfmisc_1(B_1759, k1_xboole_0)))), inference(resolution, [status(thm)], [c_42243, c_42036])).
% 12.82/5.57  tff(c_42362, plain, (![B_1759]: (k2_zfmisc_1(B_1759, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42332, c_8])).
% 12.82/5.57  tff(c_46446, plain, (![B_1963]: (k2_zfmisc_1(B_1963, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_46275, c_46275, c_42362])).
% 12.82/5.57  tff(c_46470, plain, (![A_13, B_14, C_15]: (k4_zfmisc_1(A_13, B_14, C_15, '#skF_9')='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_46446, c_16])).
% 12.82/5.57  tff(c_46334, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_46275, c_24894])).
% 12.82/5.57  tff(c_46975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46470, c_46334])).
% 12.82/5.57  tff(c_46977, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_45785])).
% 12.82/5.57  tff(c_41915, plain, (![C_1679, A_1680, B_1681, D_1682]: (C_1679=A_1680 | k1_xboole_0=B_1681 | k1_xboole_0=A_1680 | k2_zfmisc_1(C_1679, D_1682)!=k2_zfmisc_1(A_1680, B_1681))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.82/5.57  tff(c_45933, plain, (![D_1940, B_1942, A_1944, B_1941, C_1945, A_1943]: (k3_zfmisc_1(A_1943, B_1941, C_1945)=A_1944 | k1_xboole_0=B_1942 | k1_xboole_0=A_1944 | k4_zfmisc_1(A_1943, B_1941, C_1945, D_1940)!=k2_zfmisc_1(A_1944, B_1942))), inference(superposition, [status(thm), theory('equality')], [c_16, c_41915])).
% 12.82/5.57  tff(c_46006, plain, (![A_1946, B_1947]: (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')=A_1946 | k1_xboole_0=B_1947 | k1_xboole_0=A_1946 | k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!=k2_zfmisc_1(A_1946, B_1947))), inference(superposition, [status(thm), theory('equality')], [c_41824, c_45933])).
% 12.82/5.57  tff(c_46033, plain, (![A_13, B_14, C_15, D_16]: (k3_zfmisc_1(A_13, B_14, C_15)=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8') | k1_xboole_0=D_16 | k3_zfmisc_1(A_13, B_14, C_15)=k1_xboole_0 | k4_zfmisc_1(A_13, B_14, C_15, D_16)!=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_46006])).
% 12.82/5.57  tff(c_48354, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4') | k1_xboole_0='#skF_9' | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_46033])).
% 12.82/5.57  tff(c_48355, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4') | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_46977, c_48354])).
% 12.82/5.57  tff(c_50927, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48355])).
% 12.82/5.57  tff(c_47149, plain, (![A_2011, B_2012, C_2013, D_2014]: (~v1_xboole_0(k3_zfmisc_1(A_2011, B_2012, C_2013)) | v1_xboole_0(k4_zfmisc_1(A_2011, B_2012, C_2013, D_2014)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_41928])).
% 12.82/5.57  tff(c_47219, plain, (![A_2011, B_2012, C_2013, D_2014]: (k4_zfmisc_1(A_2011, B_2012, C_2013, D_2014)=k1_xboole_0 | ~v1_xboole_0(k3_zfmisc_1(A_2011, B_2012, C_2013)))), inference(resolution, [status(thm)], [c_47149, c_8])).
% 12.82/5.57  tff(c_50957, plain, (![D_2014]: (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', D_2014)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50927, c_47219])).
% 12.82/5.57  tff(c_51028, plain, (![D_2014]: (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', D_2014)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50957])).
% 12.82/5.57  tff(c_51055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51028, c_24894])).
% 12.82/5.57  tff(c_51057, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48355])).
% 12.82/5.57  tff(c_51056, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48355])).
% 12.82/5.57  tff(c_22, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (F_25=C_22 | k3_zfmisc_1(A_20, B_21, C_22)=k1_xboole_0 | k3_zfmisc_1(D_23, E_24, F_25)!=k3_zfmisc_1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.82/5.57  tff(c_51146, plain, (![F_25, D_23, E_24]: (F_25='#skF_8' | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')=k1_xboole_0 | k3_zfmisc_1(D_23, E_24, F_25)!=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_51056, c_22])).
% 12.82/5.57  tff(c_51161, plain, (![F_25, D_23, E_24]: (F_25='#skF_8' | k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k3_zfmisc_1(D_23, E_24, F_25)!=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_51056, c_51146])).
% 12.82/5.57  tff(c_51162, plain, (![F_25, D_23, E_24]: (F_25='#skF_8' | k3_zfmisc_1(D_23, E_24, F_25)!=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_51057, c_51161])).
% 12.82/5.57  tff(c_51337, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_51162])).
% 12.82/5.57  tff(c_51339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41817, c_51337])).
% 12.82/5.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.82/5.57  
% 12.82/5.57  Inference rules
% 12.82/5.57  ----------------------
% 12.82/5.57  #Ref     : 39
% 12.82/5.57  #Sup     : 13540
% 12.82/5.57  #Fact    : 0
% 12.82/5.57  #Define  : 0
% 12.82/5.57  #Split   : 27
% 12.82/5.57  #Chain   : 0
% 12.82/5.57  #Close   : 0
% 12.82/5.57  
% 12.82/5.57  Ordering : KBO
% 12.82/5.57  
% 12.82/5.57  Simplification rules
% 12.82/5.57  ----------------------
% 12.82/5.57  #Subsume      : 3195
% 12.82/5.57  #Demod        : 7260
% 12.82/5.57  #Tautology    : 7614
% 12.82/5.57  #SimpNegUnit  : 275
% 12.82/5.57  #BackRed      : 616
% 12.82/5.57  
% 12.82/5.57  #Partial instantiations: 0
% 12.82/5.57  #Strategies tried      : 1
% 12.82/5.57  
% 12.82/5.57  Timing (in seconds)
% 12.82/5.57  ----------------------
% 12.82/5.58  Preprocessing        : 0.29
% 12.82/5.58  Parsing              : 0.15
% 12.82/5.58  CNF conversion       : 0.02
% 12.82/5.58  Main loop            : 4.42
% 12.82/5.58  Inferencing          : 1.23
% 12.82/5.58  Reduction            : 1.34
% 12.82/5.58  Demodulation         : 0.94
% 12.82/5.58  BG Simplification    : 0.12
% 12.82/5.58  Subsumption          : 1.46
% 12.82/5.58  Abstraction          : 0.17
% 12.82/5.58  MUC search           : 0.00
% 12.82/5.58  Cooper               : 0.00
% 12.82/5.58  Total                : 4.83
% 12.82/5.58  Index Insertion      : 0.00
% 12.82/5.58  Index Deletion       : 0.00
% 12.82/5.58  Index Matching       : 0.00
% 12.82/5.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
