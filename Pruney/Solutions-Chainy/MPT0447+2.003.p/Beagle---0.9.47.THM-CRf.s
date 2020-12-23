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
% DateTime   : Thu Dec  3 09:58:28 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.99s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 189 expanded)
%              Number of leaves         :   51 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :  145 ( 289 expanded)
%              Number of equality atoms :   29 (  66 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_71,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_115,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_87,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_75,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_85,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_101,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_99,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_142,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_84,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_82,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_70,plain,(
    ! [A_69] :
      ( k2_xboole_0(k1_relat_1(A_69),k2_relat_1(A_69)) = k3_relat_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    ! [A_23] : r1_tarski(k1_xboole_0,A_23) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2266,plain,(
    ! [C_223,A_224] :
      ( r2_hidden(k4_tarski(C_223,'#skF_6'(A_224,k1_relat_1(A_224),C_223)),A_224)
      | ~ r2_hidden(C_223,k1_relat_1(A_224)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    ! [A_35] : r1_xboole_0(A_35,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_185,plain,(
    ! [A_98,B_99] :
      ( k4_xboole_0(A_98,B_99) = k1_xboole_0
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_201,plain,(
    ! [B_14] : k4_xboole_0(B_14,B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_185])).

tff(c_34,plain,(
    ! [A_26] : k4_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_385,plain,(
    ! [A_112,B_113] : k4_xboole_0(A_112,k4_xboole_0(A_112,B_113)) = k3_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_426,plain,(
    ! [A_26] : k4_xboole_0(A_26,A_26) = k3_xboole_0(A_26,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_385])).

tff(c_433,plain,(
    ! [A_26] : k3_xboole_0(A_26,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_426])).

tff(c_637,plain,(
    ! [A_129,B_130,C_131] :
      ( ~ r1_xboole_0(A_129,B_130)
      | ~ r2_hidden(C_131,k3_xboole_0(A_129,B_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_653,plain,(
    ! [A_26,C_131] :
      ( ~ r1_xboole_0(A_26,k1_xboole_0)
      | ~ r2_hidden(C_131,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_637])).

tff(c_664,plain,(
    ! [C_131] : ~ r2_hidden(C_131,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_653])).

tff(c_2284,plain,(
    ! [C_225] : ~ r2_hidden(C_225,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2266,c_664])).

tff(c_2313,plain,(
    ! [B_227] : r1_tarski(k1_relat_1(k1_xboole_0),B_227) ),
    inference(resolution,[status(thm)],[c_6,c_2284])).

tff(c_526,plain,(
    ! [B_119,A_120] :
      ( B_119 = A_120
      | ~ r1_tarski(B_119,A_120)
      | ~ r1_tarski(A_120,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_539,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_526])).

tff(c_2323,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2313,c_539])).

tff(c_80,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_200,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_185])).

tff(c_52,plain,(
    ! [A_45,B_46] : k6_subset_1(A_45,B_46) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_72,plain,(
    ! [A_70,B_72] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_70),k1_relat_1(B_72)),k1_relat_1(k6_subset_1(A_70,B_72)))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2600,plain,(
    ! [A_234,B_235] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_234),k1_relat_1(B_235)),k1_relat_1(k4_xboole_0(A_234,B_235)))
      | ~ v1_relat_1(B_235)
      | ~ v1_relat_1(A_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_72])).

tff(c_2651,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_2600])).

tff(c_2676,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_2323,c_2651])).

tff(c_2695,plain,(
    k4_xboole_0(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2676,c_539])).

tff(c_38,plain,(
    ! [A_30,B_31,C_32] :
      ( r1_tarski(A_30,k2_xboole_0(B_31,C_32))
      | ~ r1_tarski(k4_xboole_0(A_30,B_31),C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2723,plain,(
    ! [C_32] :
      ( r1_tarski(k1_relat_1('#skF_8'),k2_xboole_0(k1_relat_1('#skF_9'),C_32))
      | ~ r1_tarski(k1_xboole_0,C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2695,c_38])).

tff(c_3142,plain,(
    ! [C_256] : r1_tarski(k1_relat_1('#skF_8'),k2_xboole_0(k1_relat_1('#skF_9'),C_256)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2723])).

tff(c_3151,plain,
    ( r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_3142])).

tff(c_3163,plain,(
    r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3151])).

tff(c_46,plain,(
    ! [B_40,A_39] : k2_tarski(B_40,A_39) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_314,plain,(
    ! [A_106,B_107] : k3_tarski(k2_tarski(A_106,B_107)) = k2_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_921,plain,(
    ! [A_150,B_151] : k3_tarski(k2_tarski(A_150,B_151)) = k2_xboole_0(B_151,A_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_314])).

tff(c_50,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_927,plain,(
    ! [B_151,A_150] : k2_xboole_0(B_151,A_150) = k2_xboole_0(A_150,B_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_921,c_50])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [A_83] :
      ( v1_relat_1(A_83)
      | ~ v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_95,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_91])).

tff(c_74,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_7'(A_73,B_74),k1_relat_1(B_74))
      | ~ r2_hidden(A_73,k2_relat_1(B_74))
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2292,plain,(
    ! [A_73] :
      ( ~ r2_hidden(A_73,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_74,c_2284])).

tff(c_2302,plain,(
    ! [A_226] : ~ r2_hidden(A_226,k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_2292])).

tff(c_2363,plain,(
    ! [B_229] : r1_tarski(k2_relat_1(k1_xboole_0),B_229) ),
    inference(resolution,[status(thm)],[c_6,c_2302])).

tff(c_2373,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2363,c_539])).

tff(c_76,plain,(
    ! [A_76,B_78] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_76),k2_relat_1(B_78)),k2_relat_1(k6_subset_1(A_76,B_78)))
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2820,plain,(
    ! [A_241,B_242] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_241),k2_relat_1(B_242)),k2_relat_1(k4_xboole_0(A_241,B_242)))
      | ~ v1_relat_1(B_242)
      | ~ v1_relat_1(A_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_76])).

tff(c_2874,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_8'),k2_relat_1('#skF_9')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_2820])).

tff(c_2900,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_8'),k2_relat_1('#skF_9')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_2373,c_2874])).

tff(c_2980,plain,(
    k4_xboole_0(k2_relat_1('#skF_8'),k2_relat_1('#skF_9')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2900,c_539])).

tff(c_3011,plain,(
    ! [C_32] :
      ( r1_tarski(k2_relat_1('#skF_8'),k2_xboole_0(k2_relat_1('#skF_9'),C_32))
      | ~ r1_tarski(k1_xboole_0,C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2980,c_38])).

tff(c_3290,plain,(
    ! [C_261] : r1_tarski(k2_relat_1('#skF_8'),k2_xboole_0(k2_relat_1('#skF_9'),C_261)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3011])).

tff(c_3467,plain,(
    ! [B_267] : r1_tarski(k2_relat_1('#skF_8'),k2_xboole_0(B_267,k2_relat_1('#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_3290])).

tff(c_3476,plain,
    ( r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_3467])).

tff(c_3488,plain,(
    r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3476])).

tff(c_1998,plain,(
    ! [A_204,C_205,B_206] :
      ( r1_tarski(k2_xboole_0(A_204,C_205),B_206)
      | ~ r1_tarski(C_205,B_206)
      | ~ r1_tarski(A_204,B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_11936,plain,(
    ! [A_476,B_477] :
      ( r1_tarski(k3_relat_1(A_476),B_477)
      | ~ r1_tarski(k2_relat_1(A_476),B_477)
      | ~ r1_tarski(k1_relat_1(A_476),B_477)
      | ~ v1_relat_1(A_476) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1998])).

tff(c_78,plain,(
    ~ r1_tarski(k3_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_11981,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_11936,c_78])).

tff(c_12003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3163,c_3488,c_11981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:38:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.79/2.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.98  
% 7.79/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.98  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 7.79/2.98  
% 7.79/2.98  %Foreground sorts:
% 7.79/2.98  
% 7.79/2.98  
% 7.79/2.98  %Background operators:
% 7.79/2.98  
% 7.79/2.98  
% 7.79/2.98  %Foreground operators:
% 7.79/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.79/2.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.79/2.98  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.79/2.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.79/2.98  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.79/2.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.79/2.98  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 7.79/2.98  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.79/2.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.79/2.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.79/2.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.79/2.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.79/2.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.79/2.98  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.79/2.98  tff('#skF_9', type, '#skF_9': $i).
% 7.79/2.98  tff('#skF_8', type, '#skF_8': $i).
% 7.79/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.79/2.98  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.79/2.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.79/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.79/2.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.79/2.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.79/2.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.79/2.98  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.79/2.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.79/2.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.79/2.98  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.79/2.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.79/2.98  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.79/2.98  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.79/2.98  
% 7.99/3.00  tff(f_152, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 7.99/3.00  tff(f_119, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 7.99/3.00  tff(f_71, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.99/3.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.99/3.00  tff(f_115, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 7.99/3.00  tff(f_87, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.99/3.00  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.99/3.00  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.99/3.00  tff(f_75, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.99/3.00  tff(f_85, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.99/3.00  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.99/3.00  tff(f_101, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.99/3.00  tff(f_126, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 7.99/3.00  tff(f_83, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 7.99/3.00  tff(f_95, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.99/3.00  tff(f_99, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.99/3.00  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.99/3.00  tff(f_107, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 7.99/3.00  tff(f_135, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 7.99/3.00  tff(f_142, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 7.99/3.00  tff(f_93, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 7.99/3.00  tff(c_84, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.99/3.00  tff(c_82, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.99/3.00  tff(c_70, plain, (![A_69]: (k2_xboole_0(k1_relat_1(A_69), k2_relat_1(A_69))=k3_relat_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.99/3.00  tff(c_30, plain, (![A_23]: (r1_tarski(k1_xboole_0, A_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.99/3.00  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.99/3.00  tff(c_2266, plain, (![C_223, A_224]: (r2_hidden(k4_tarski(C_223, '#skF_6'(A_224, k1_relat_1(A_224), C_223)), A_224) | ~r2_hidden(C_223, k1_relat_1(A_224)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.99/3.00  tff(c_42, plain, (![A_35]: (r1_xboole_0(A_35, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.99/3.00  tff(c_20, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.99/3.00  tff(c_185, plain, (![A_98, B_99]: (k4_xboole_0(A_98, B_99)=k1_xboole_0 | ~r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.99/3.00  tff(c_201, plain, (![B_14]: (k4_xboole_0(B_14, B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_185])).
% 7.99/3.00  tff(c_34, plain, (![A_26]: (k4_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.99/3.00  tff(c_385, plain, (![A_112, B_113]: (k4_xboole_0(A_112, k4_xboole_0(A_112, B_113))=k3_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.99/3.00  tff(c_426, plain, (![A_26]: (k4_xboole_0(A_26, A_26)=k3_xboole_0(A_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_385])).
% 7.99/3.00  tff(c_433, plain, (![A_26]: (k3_xboole_0(A_26, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_201, c_426])).
% 7.99/3.00  tff(c_637, plain, (![A_129, B_130, C_131]: (~r1_xboole_0(A_129, B_130) | ~r2_hidden(C_131, k3_xboole_0(A_129, B_130)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.99/3.00  tff(c_653, plain, (![A_26, C_131]: (~r1_xboole_0(A_26, k1_xboole_0) | ~r2_hidden(C_131, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_433, c_637])).
% 7.99/3.00  tff(c_664, plain, (![C_131]: (~r2_hidden(C_131, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_653])).
% 7.99/3.00  tff(c_2284, plain, (![C_225]: (~r2_hidden(C_225, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2266, c_664])).
% 7.99/3.00  tff(c_2313, plain, (![B_227]: (r1_tarski(k1_relat_1(k1_xboole_0), B_227))), inference(resolution, [status(thm)], [c_6, c_2284])).
% 7.99/3.00  tff(c_526, plain, (![B_119, A_120]: (B_119=A_120 | ~r1_tarski(B_119, A_120) | ~r1_tarski(A_120, B_119))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.99/3.00  tff(c_539, plain, (![A_23]: (k1_xboole_0=A_23 | ~r1_tarski(A_23, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_526])).
% 7.99/3.00  tff(c_2323, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2313, c_539])).
% 7.99/3.00  tff(c_80, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.99/3.00  tff(c_200, plain, (k4_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_185])).
% 7.99/3.00  tff(c_52, plain, (![A_45, B_46]: (k6_subset_1(A_45, B_46)=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.99/3.00  tff(c_72, plain, (![A_70, B_72]: (r1_tarski(k6_subset_1(k1_relat_1(A_70), k1_relat_1(B_72)), k1_relat_1(k6_subset_1(A_70, B_72))) | ~v1_relat_1(B_72) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.99/3.00  tff(c_2600, plain, (![A_234, B_235]: (r1_tarski(k4_xboole_0(k1_relat_1(A_234), k1_relat_1(B_235)), k1_relat_1(k4_xboole_0(A_234, B_235))) | ~v1_relat_1(B_235) | ~v1_relat_1(A_234))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_72])).
% 7.99/3.00  tff(c_2651, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'), k1_relat_1('#skF_9')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_200, c_2600])).
% 7.99/3.00  tff(c_2676, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'), k1_relat_1('#skF_9')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_2323, c_2651])).
% 7.99/3.00  tff(c_2695, plain, (k4_xboole_0(k1_relat_1('#skF_8'), k1_relat_1('#skF_9'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2676, c_539])).
% 7.99/3.00  tff(c_38, plain, (![A_30, B_31, C_32]: (r1_tarski(A_30, k2_xboole_0(B_31, C_32)) | ~r1_tarski(k4_xboole_0(A_30, B_31), C_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.99/3.00  tff(c_2723, plain, (![C_32]: (r1_tarski(k1_relat_1('#skF_8'), k2_xboole_0(k1_relat_1('#skF_9'), C_32)) | ~r1_tarski(k1_xboole_0, C_32))), inference(superposition, [status(thm), theory('equality')], [c_2695, c_38])).
% 7.99/3.00  tff(c_3142, plain, (![C_256]: (r1_tarski(k1_relat_1('#skF_8'), k2_xboole_0(k1_relat_1('#skF_9'), C_256)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2723])).
% 7.99/3.00  tff(c_3151, plain, (r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_70, c_3142])).
% 7.99/3.00  tff(c_3163, plain, (r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3151])).
% 7.99/3.00  tff(c_46, plain, (![B_40, A_39]: (k2_tarski(B_40, A_39)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.99/3.00  tff(c_314, plain, (![A_106, B_107]: (k3_tarski(k2_tarski(A_106, B_107))=k2_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.99/3.00  tff(c_921, plain, (![A_150, B_151]: (k3_tarski(k2_tarski(A_150, B_151))=k2_xboole_0(B_151, A_150))), inference(superposition, [status(thm), theory('equality')], [c_46, c_314])).
% 7.99/3.00  tff(c_50, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.99/3.00  tff(c_927, plain, (![B_151, A_150]: (k2_xboole_0(B_151, A_150)=k2_xboole_0(A_150, B_151))), inference(superposition, [status(thm), theory('equality')], [c_921, c_50])).
% 7.99/3.00  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.99/3.00  tff(c_91, plain, (![A_83]: (v1_relat_1(A_83) | ~v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.99/3.00  tff(c_95, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_91])).
% 7.99/3.00  tff(c_74, plain, (![A_73, B_74]: (r2_hidden('#skF_7'(A_73, B_74), k1_relat_1(B_74)) | ~r2_hidden(A_73, k2_relat_1(B_74)) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.99/3.00  tff(c_2292, plain, (![A_73]: (~r2_hidden(A_73, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_74, c_2284])).
% 7.99/3.00  tff(c_2302, plain, (![A_226]: (~r2_hidden(A_226, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_2292])).
% 7.99/3.00  tff(c_2363, plain, (![B_229]: (r1_tarski(k2_relat_1(k1_xboole_0), B_229))), inference(resolution, [status(thm)], [c_6, c_2302])).
% 7.99/3.00  tff(c_2373, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2363, c_539])).
% 7.99/3.00  tff(c_76, plain, (![A_76, B_78]: (r1_tarski(k6_subset_1(k2_relat_1(A_76), k2_relat_1(B_78)), k2_relat_1(k6_subset_1(A_76, B_78))) | ~v1_relat_1(B_78) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.99/3.00  tff(c_2820, plain, (![A_241, B_242]: (r1_tarski(k4_xboole_0(k2_relat_1(A_241), k2_relat_1(B_242)), k2_relat_1(k4_xboole_0(A_241, B_242))) | ~v1_relat_1(B_242) | ~v1_relat_1(A_241))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_76])).
% 7.99/3.00  tff(c_2874, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_8'), k2_relat_1('#skF_9')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_200, c_2820])).
% 7.99/3.00  tff(c_2900, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_8'), k2_relat_1('#skF_9')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_2373, c_2874])).
% 7.99/3.00  tff(c_2980, plain, (k4_xboole_0(k2_relat_1('#skF_8'), k2_relat_1('#skF_9'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2900, c_539])).
% 7.99/3.00  tff(c_3011, plain, (![C_32]: (r1_tarski(k2_relat_1('#skF_8'), k2_xboole_0(k2_relat_1('#skF_9'), C_32)) | ~r1_tarski(k1_xboole_0, C_32))), inference(superposition, [status(thm), theory('equality')], [c_2980, c_38])).
% 7.99/3.00  tff(c_3290, plain, (![C_261]: (r1_tarski(k2_relat_1('#skF_8'), k2_xboole_0(k2_relat_1('#skF_9'), C_261)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3011])).
% 7.99/3.00  tff(c_3467, plain, (![B_267]: (r1_tarski(k2_relat_1('#skF_8'), k2_xboole_0(B_267, k2_relat_1('#skF_9'))))), inference(superposition, [status(thm), theory('equality')], [c_927, c_3290])).
% 7.99/3.00  tff(c_3476, plain, (r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_70, c_3467])).
% 7.99/3.00  tff(c_3488, plain, (r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3476])).
% 7.99/3.00  tff(c_1998, plain, (![A_204, C_205, B_206]: (r1_tarski(k2_xboole_0(A_204, C_205), B_206) | ~r1_tarski(C_205, B_206) | ~r1_tarski(A_204, B_206))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.99/3.00  tff(c_11936, plain, (![A_476, B_477]: (r1_tarski(k3_relat_1(A_476), B_477) | ~r1_tarski(k2_relat_1(A_476), B_477) | ~r1_tarski(k1_relat_1(A_476), B_477) | ~v1_relat_1(A_476))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1998])).
% 7.99/3.00  tff(c_78, plain, (~r1_tarski(k3_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.99/3.00  tff(c_11981, plain, (~r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_11936, c_78])).
% 7.99/3.00  tff(c_12003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_3163, c_3488, c_11981])).
% 7.99/3.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.99/3.00  
% 7.99/3.00  Inference rules
% 7.99/3.00  ----------------------
% 7.99/3.00  #Ref     : 1
% 7.99/3.00  #Sup     : 2847
% 7.99/3.00  #Fact    : 0
% 7.99/3.00  #Define  : 0
% 7.99/3.00  #Split   : 5
% 7.99/3.00  #Chain   : 0
% 7.99/3.00  #Close   : 0
% 7.99/3.00  
% 7.99/3.00  Ordering : KBO
% 7.99/3.00  
% 7.99/3.00  Simplification rules
% 7.99/3.00  ----------------------
% 7.99/3.00  #Subsume      : 520
% 7.99/3.00  #Demod        : 1800
% 7.99/3.00  #Tautology    : 1393
% 7.99/3.00  #SimpNegUnit  : 30
% 7.99/3.00  #BackRed      : 10
% 7.99/3.00  
% 7.99/3.00  #Partial instantiations: 0
% 7.99/3.00  #Strategies tried      : 1
% 7.99/3.00  
% 7.99/3.00  Timing (in seconds)
% 7.99/3.00  ----------------------
% 7.99/3.00  Preprocessing        : 0.38
% 7.99/3.00  Parsing              : 0.20
% 7.99/3.00  CNF conversion       : 0.03
% 7.99/3.00  Main loop            : 1.79
% 7.99/3.00  Inferencing          : 0.43
% 7.99/3.00  Reduction            : 0.81
% 7.99/3.00  Demodulation         : 0.65
% 7.99/3.00  BG Simplification    : 0.05
% 7.99/3.00  Subsumption          : 0.37
% 7.99/3.00  Abstraction          : 0.06
% 7.99/3.00  MUC search           : 0.00
% 7.99/3.00  Cooper               : 0.00
% 7.99/3.00  Total                : 2.20
% 7.99/3.00  Index Insertion      : 0.00
% 7.99/3.00  Index Deletion       : 0.00
% 7.99/3.00  Index Matching       : 0.00
% 7.99/3.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
