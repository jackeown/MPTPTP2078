%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:28 EST 2020

% Result     : Theorem 16.83s
% Output     : CNFRefutation 16.99s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 179 expanded)
%              Number of leaves         :   53 (  84 expanded)
%              Depth                    :   17
%              Number of atoms          :  165 ( 305 expanded)
%              Number of equality atoms :   31 (  60 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_4 > #skF_11 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_7 > #skF_1 > #skF_5 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

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

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_201,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_168,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_76,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_164,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_150,axiom,(
    ! [A] :
    ? [B] :
      ( r2_hidden(A,B)
      & ! [C,D] :
          ( ( r2_hidden(C,B)
            & r1_tarski(D,C) )
         => r2_hidden(D,B) )
      & ! [C] :
          ~ ( r2_hidden(C,B)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & ! [E] :
                      ( r1_tarski(E,C)
                     => r2_hidden(E,D) ) ) )
      & ! [C] :
          ~ ( r1_tarski(C,B)
            & ~ r2_tarski(C,B)
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tarski)).

tff(f_117,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_90,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_152,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_175,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_104,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_156,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_184,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_191,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_92,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_90,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_78,plain,(
    ! [A_110] :
      ( k2_xboole_0(k1_relat_1(A_110),k2_relat_1(A_110)) = k3_relat_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_28,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_175,plain,(
    ! [A_135,B_136] :
      ( k4_xboole_0(A_135,B_136) = k1_xboole_0
      | ~ r1_tarski(A_135,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_191,plain,(
    ! [A_20] : k4_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_175])).

tff(c_12,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3459,plain,(
    ! [C_311,A_312] :
      ( r2_hidden(k4_tarski(C_311,'#skF_9'(A_312,k1_relat_1(A_312),C_311)),A_312)
      | ~ r2_hidden(C_311,k1_relat_1(A_312)) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_56,plain,(
    ! [A_47] : r2_hidden(A_47,'#skF_4'(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_3'(A_40,B_41),B_41)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    ! [A_28] : r1_xboole_0(A_28,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_602,plain,(
    ! [A_182,B_183,C_184] :
      ( ~ r1_xboole_0(A_182,B_183)
      | ~ r2_hidden(C_184,B_183)
      | ~ r2_hidden(C_184,A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_606,plain,(
    ! [C_185,A_186] :
      ( ~ r2_hidden(C_185,k1_xboole_0)
      | ~ r2_hidden(C_185,A_186) ) ),
    inference(resolution,[status(thm)],[c_36,c_602])).

tff(c_688,plain,(
    ! [A_191,A_192] :
      ( ~ r2_hidden('#skF_3'(A_191,k1_xboole_0),A_192)
      | ~ r2_hidden(A_191,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50,c_606])).

tff(c_697,plain,(
    ! [A_191] : ~ r2_hidden(A_191,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_56,c_688])).

tff(c_3478,plain,(
    ! [C_313] : ~ r2_hidden(C_313,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_3459,c_697])).

tff(c_3510,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_3478])).

tff(c_88,plain,(
    r1_tarski('#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_189,plain,(
    k4_xboole_0('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_175])).

tff(c_62,plain,(
    ! [A_88,B_89] : k6_subset_1(A_88,B_89) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_80,plain,(
    ! [A_111,B_113] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_111),k1_relat_1(B_113)),k1_relat_1(k6_subset_1(A_111,B_113)))
      | ~ v1_relat_1(B_113)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_4263,plain,(
    ! [A_331,B_332] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_331),k1_relat_1(B_332)),k1_relat_1(k4_xboole_0(A_331,B_332)))
      | ~ v1_relat_1(B_332)
      | ~ v1_relat_1(A_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_80])).

tff(c_4341,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_4263])).

tff(c_4376,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_3510,c_4341])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_429,plain,(
    ! [B_165,A_166] :
      ( B_165 = A_166
      | ~ r1_tarski(B_165,A_166)
      | ~ r1_tarski(A_166,B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_446,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | k4_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_429])).

tff(c_4405,plain,
    ( k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4376,c_446])).

tff(c_4427,plain,(
    k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_4405])).

tff(c_34,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_tarski(A_25,k2_xboole_0(B_26,C_27))
      | ~ r1_tarski(k4_xboole_0(A_25,B_26),C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4466,plain,(
    ! [C_27] :
      ( r1_tarski(k1_relat_1('#skF_11'),k2_xboole_0(k1_relat_1('#skF_12'),C_27))
      | ~ r1_tarski(k1_xboole_0,C_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4427,c_34])).

tff(c_4691,plain,(
    ! [C_339] : r1_tarski(k1_relat_1('#skF_11'),k2_xboole_0(k1_relat_1('#skF_12'),C_339)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4466])).

tff(c_4720,plain,
    ( r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4691])).

tff(c_4745,plain,(
    r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4720])).

tff(c_42,plain,(
    ! [B_35,A_34] : k2_tarski(B_35,A_34) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_196,plain,(
    ! [A_137,B_138] : k3_tarski(k2_tarski(A_137,B_138)) = k2_xboole_0(A_137,B_138) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_289,plain,(
    ! [A_150,B_151] : k3_tarski(k2_tarski(A_150,B_151)) = k2_xboole_0(B_151,A_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_196])).

tff(c_46,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_295,plain,(
    ! [B_151,A_150] : k2_xboole_0(B_151,A_150) = k2_xboole_0(A_150,B_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_46])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_99,plain,(
    ! [A_124] :
      ( v1_relat_1(A_124)
      | ~ v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_103,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_99])).

tff(c_82,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_10'(A_114,B_115),k1_relat_1(B_115))
      | ~ r2_hidden(A_114,k2_relat_1(B_115))
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_3486,plain,(
    ! [A_114] :
      ( ~ r2_hidden(A_114,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_82,c_3478])).

tff(c_3542,plain,(
    ! [A_314] : ~ r2_hidden(A_314,k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_3486])).

tff(c_3567,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_3542])).

tff(c_84,plain,(
    ! [A_117,B_119] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_117),k2_relat_1(B_119)),k2_relat_1(k6_subset_1(A_117,B_119)))
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_3979,plain,(
    ! [A_327,B_328] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_327),k2_relat_1(B_328)),k2_relat_1(k4_xboole_0(A_327,B_328)))
      | ~ v1_relat_1(B_328)
      | ~ v1_relat_1(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_84])).

tff(c_4054,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_11'),k2_relat_1('#skF_12')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_3979])).

tff(c_4088,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_11'),k2_relat_1('#skF_12')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_3567,c_4054])).

tff(c_4096,plain,
    ( k4_xboole_0(k2_relat_1('#skF_11'),k2_relat_1('#skF_12')) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1('#skF_11'),k2_relat_1('#skF_12'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4088,c_446])).

tff(c_4118,plain,(
    k4_xboole_0(k2_relat_1('#skF_11'),k2_relat_1('#skF_12')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_4096])).

tff(c_4154,plain,(
    ! [C_27] :
      ( r1_tarski(k2_relat_1('#skF_11'),k2_xboole_0(k2_relat_1('#skF_12'),C_27))
      | ~ r1_tarski(k1_xboole_0,C_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4118,c_34])).

tff(c_4218,plain,(
    ! [C_330] : r1_tarski(k2_relat_1('#skF_11'),k2_xboole_0(k2_relat_1('#skF_12'),C_330)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4154])).

tff(c_5003,plain,(
    ! [A_346] : r1_tarski(k2_relat_1('#skF_11'),k2_xboole_0(A_346,k2_relat_1('#skF_12'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_4218])).

tff(c_5024,plain,
    ( r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_5003])).

tff(c_5045,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_5024])).

tff(c_2108,plain,(
    ! [A_256,C_257,B_258] :
      ( r1_tarski(k2_xboole_0(A_256,C_257),B_258)
      | ~ r1_tarski(C_257,B_258)
      | ~ r1_tarski(A_256,B_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_21953,plain,(
    ! [A_552,B_553] :
      ( r1_tarski(k3_relat_1(A_552),B_553)
      | ~ r1_tarski(k2_relat_1(A_552),B_553)
      | ~ r1_tarski(k1_relat_1(A_552),B_553)
      | ~ v1_relat_1(A_552) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2108])).

tff(c_86,plain,(
    ~ r1_tarski(k3_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_22040,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_21953,c_86])).

tff(c_22076,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_4745,c_5045,c_22040])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.83/7.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.83/7.11  
% 16.83/7.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.83/7.11  %$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_4 > #skF_11 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_7 > #skF_1 > #skF_5 > #skF_12
% 16.83/7.11  
% 16.83/7.11  %Foreground sorts:
% 16.83/7.11  
% 16.83/7.11  
% 16.83/7.11  %Background operators:
% 16.83/7.11  
% 16.83/7.11  
% 16.83/7.11  %Foreground operators:
% 16.83/7.11  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 16.83/7.11  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 16.83/7.11  tff('#skF_2', type, '#skF_2': $i > $i).
% 16.83/7.11  tff('#skF_4', type, '#skF_4': $i > $i).
% 16.83/7.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.83/7.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.83/7.11  tff('#skF_11', type, '#skF_11': $i).
% 16.83/7.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.83/7.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.83/7.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.83/7.11  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 16.83/7.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.83/7.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.83/7.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.83/7.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.83/7.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.83/7.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.83/7.11  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 16.83/7.11  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 16.83/7.11  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 16.83/7.11  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 16.83/7.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.83/7.11  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.83/7.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.83/7.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.83/7.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.83/7.11  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 16.83/7.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.83/7.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.83/7.11  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 16.83/7.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.83/7.11  tff('#skF_12', type, '#skF_12': $i).
% 16.83/7.11  
% 16.99/7.14  tff(f_201, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 16.99/7.14  tff(f_168, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 16.99/7.14  tff(f_76, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.99/7.14  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 16.99/7.14  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 16.99/7.14  tff(f_164, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 16.99/7.14  tff(f_150, axiom, (![A]: (?[B]: (((r2_hidden(A, B) & (![C, D]: ((r2_hidden(C, B) & r1_tarski(D, C)) => r2_hidden(D, B)))) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & (![E]: (r1_tarski(E, C) => r2_hidden(E, D)))))))) & (![C]: ~((r1_tarski(C, B) & ~r2_tarski(C, B)) & ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tarski)).
% 16.99/7.14  tff(f_117, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 16.99/7.14  tff(f_90, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 16.99/7.14  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 16.99/7.14  tff(f_152, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 16.99/7.14  tff(f_175, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 16.99/7.14  tff(f_60, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.99/7.14  tff(f_88, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 16.99/7.14  tff(f_100, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 16.99/7.14  tff(f_104, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 16.99/7.14  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 16.99/7.14  tff(f_156, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 16.99/7.14  tff(f_184, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 16.99/7.14  tff(f_191, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 16.99/7.14  tff(f_98, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 16.99/7.14  tff(c_92, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_201])).
% 16.99/7.14  tff(c_90, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_201])).
% 16.99/7.14  tff(c_78, plain, (![A_110]: (k2_xboole_0(k1_relat_1(A_110), k2_relat_1(A_110))=k3_relat_1(A_110) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_168])).
% 16.99/7.14  tff(c_28, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 16.99/7.14  tff(c_175, plain, (![A_135, B_136]: (k4_xboole_0(A_135, B_136)=k1_xboole_0 | ~r1_tarski(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_64])).
% 16.99/7.14  tff(c_191, plain, (![A_20]: (k4_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_175])).
% 16.99/7.14  tff(c_12, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.99/7.14  tff(c_3459, plain, (![C_311, A_312]: (r2_hidden(k4_tarski(C_311, '#skF_9'(A_312, k1_relat_1(A_312), C_311)), A_312) | ~r2_hidden(C_311, k1_relat_1(A_312)))), inference(cnfTransformation, [status(thm)], [f_164])).
% 16.99/7.14  tff(c_56, plain, (![A_47]: (r2_hidden(A_47, '#skF_4'(A_47)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 16.99/7.14  tff(c_50, plain, (![A_40, B_41]: (r2_hidden('#skF_3'(A_40, B_41), B_41) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.99/7.14  tff(c_36, plain, (![A_28]: (r1_xboole_0(A_28, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.99/7.14  tff(c_602, plain, (![A_182, B_183, C_184]: (~r1_xboole_0(A_182, B_183) | ~r2_hidden(C_184, B_183) | ~r2_hidden(C_184, A_182))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.99/7.14  tff(c_606, plain, (![C_185, A_186]: (~r2_hidden(C_185, k1_xboole_0) | ~r2_hidden(C_185, A_186))), inference(resolution, [status(thm)], [c_36, c_602])).
% 16.99/7.14  tff(c_688, plain, (![A_191, A_192]: (~r2_hidden('#skF_3'(A_191, k1_xboole_0), A_192) | ~r2_hidden(A_191, k1_xboole_0))), inference(resolution, [status(thm)], [c_50, c_606])).
% 16.99/7.14  tff(c_697, plain, (![A_191]: (~r2_hidden(A_191, k1_xboole_0))), inference(resolution, [status(thm)], [c_56, c_688])).
% 16.99/7.14  tff(c_3478, plain, (![C_313]: (~r2_hidden(C_313, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_3459, c_697])).
% 16.99/7.14  tff(c_3510, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_3478])).
% 16.99/7.14  tff(c_88, plain, (r1_tarski('#skF_11', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_201])).
% 16.99/7.14  tff(c_189, plain, (k4_xboole_0('#skF_11', '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_175])).
% 16.99/7.14  tff(c_62, plain, (![A_88, B_89]: (k6_subset_1(A_88, B_89)=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_152])).
% 16.99/7.14  tff(c_80, plain, (![A_111, B_113]: (r1_tarski(k6_subset_1(k1_relat_1(A_111), k1_relat_1(B_113)), k1_relat_1(k6_subset_1(A_111, B_113))) | ~v1_relat_1(B_113) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_175])).
% 16.99/7.14  tff(c_4263, plain, (![A_331, B_332]: (r1_tarski(k4_xboole_0(k1_relat_1(A_331), k1_relat_1(B_332)), k1_relat_1(k4_xboole_0(A_331, B_332))) | ~v1_relat_1(B_332) | ~v1_relat_1(A_331))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_80])).
% 16.99/7.14  tff(c_4341, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_189, c_4263])).
% 16.99/7.14  tff(c_4376, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_3510, c_4341])).
% 16.99/7.14  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | k4_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 16.99/7.14  tff(c_429, plain, (![B_165, A_166]: (B_165=A_166 | ~r1_tarski(B_165, A_166) | ~r1_tarski(A_166, B_165))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.99/7.14  tff(c_446, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | k4_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_429])).
% 16.99/7.14  tff(c_4405, plain, (k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12'))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4376, c_446])).
% 16.99/7.14  tff(c_4427, plain, (k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_191, c_4405])).
% 16.99/7.14  tff(c_34, plain, (![A_25, B_26, C_27]: (r1_tarski(A_25, k2_xboole_0(B_26, C_27)) | ~r1_tarski(k4_xboole_0(A_25, B_26), C_27))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.99/7.14  tff(c_4466, plain, (![C_27]: (r1_tarski(k1_relat_1('#skF_11'), k2_xboole_0(k1_relat_1('#skF_12'), C_27)) | ~r1_tarski(k1_xboole_0, C_27))), inference(superposition, [status(thm), theory('equality')], [c_4427, c_34])).
% 16.99/7.14  tff(c_4691, plain, (![C_339]: (r1_tarski(k1_relat_1('#skF_11'), k2_xboole_0(k1_relat_1('#skF_12'), C_339)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4466])).
% 16.99/7.14  tff(c_4720, plain, (r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_78, c_4691])).
% 16.99/7.14  tff(c_4745, plain, (r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_4720])).
% 16.99/7.14  tff(c_42, plain, (![B_35, A_34]: (k2_tarski(B_35, A_34)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_100])).
% 16.99/7.14  tff(c_196, plain, (![A_137, B_138]: (k3_tarski(k2_tarski(A_137, B_138))=k2_xboole_0(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_104])).
% 16.99/7.14  tff(c_289, plain, (![A_150, B_151]: (k3_tarski(k2_tarski(A_150, B_151))=k2_xboole_0(B_151, A_150))), inference(superposition, [status(thm), theory('equality')], [c_42, c_196])).
% 16.99/7.14  tff(c_46, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_104])).
% 16.99/7.14  tff(c_295, plain, (![B_151, A_150]: (k2_xboole_0(B_151, A_150)=k2_xboole_0(A_150, B_151))), inference(superposition, [status(thm), theory('equality')], [c_289, c_46])).
% 16.99/7.14  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 16.99/7.14  tff(c_99, plain, (![A_124]: (v1_relat_1(A_124) | ~v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_156])).
% 16.99/7.14  tff(c_103, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_99])).
% 16.99/7.14  tff(c_82, plain, (![A_114, B_115]: (r2_hidden('#skF_10'(A_114, B_115), k1_relat_1(B_115)) | ~r2_hidden(A_114, k2_relat_1(B_115)) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_184])).
% 16.99/7.14  tff(c_3486, plain, (![A_114]: (~r2_hidden(A_114, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_82, c_3478])).
% 16.99/7.14  tff(c_3542, plain, (![A_314]: (~r2_hidden(A_314, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_3486])).
% 16.99/7.14  tff(c_3567, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_3542])).
% 16.99/7.14  tff(c_84, plain, (![A_117, B_119]: (r1_tarski(k6_subset_1(k2_relat_1(A_117), k2_relat_1(B_119)), k2_relat_1(k6_subset_1(A_117, B_119))) | ~v1_relat_1(B_119) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_191])).
% 16.99/7.14  tff(c_3979, plain, (![A_327, B_328]: (r1_tarski(k4_xboole_0(k2_relat_1(A_327), k2_relat_1(B_328)), k2_relat_1(k4_xboole_0(A_327, B_328))) | ~v1_relat_1(B_328) | ~v1_relat_1(A_327))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_84])).
% 16.99/7.14  tff(c_4054, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_11'), k2_relat_1('#skF_12')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_189, c_3979])).
% 16.99/7.14  tff(c_4088, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_11'), k2_relat_1('#skF_12')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_3567, c_4054])).
% 16.99/7.14  tff(c_4096, plain, (k4_xboole_0(k2_relat_1('#skF_11'), k2_relat_1('#skF_12'))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k4_xboole_0(k2_relat_1('#skF_11'), k2_relat_1('#skF_12')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4088, c_446])).
% 16.99/7.14  tff(c_4118, plain, (k4_xboole_0(k2_relat_1('#skF_11'), k2_relat_1('#skF_12'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_191, c_4096])).
% 16.99/7.14  tff(c_4154, plain, (![C_27]: (r1_tarski(k2_relat_1('#skF_11'), k2_xboole_0(k2_relat_1('#skF_12'), C_27)) | ~r1_tarski(k1_xboole_0, C_27))), inference(superposition, [status(thm), theory('equality')], [c_4118, c_34])).
% 16.99/7.14  tff(c_4218, plain, (![C_330]: (r1_tarski(k2_relat_1('#skF_11'), k2_xboole_0(k2_relat_1('#skF_12'), C_330)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4154])).
% 16.99/7.14  tff(c_5003, plain, (![A_346]: (r1_tarski(k2_relat_1('#skF_11'), k2_xboole_0(A_346, k2_relat_1('#skF_12'))))), inference(superposition, [status(thm), theory('equality')], [c_295, c_4218])).
% 16.99/7.14  tff(c_5024, plain, (r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_78, c_5003])).
% 16.99/7.14  tff(c_5045, plain, (r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_5024])).
% 16.99/7.14  tff(c_2108, plain, (![A_256, C_257, B_258]: (r1_tarski(k2_xboole_0(A_256, C_257), B_258) | ~r1_tarski(C_257, B_258) | ~r1_tarski(A_256, B_258))), inference(cnfTransformation, [status(thm)], [f_98])).
% 16.99/7.14  tff(c_21953, plain, (![A_552, B_553]: (r1_tarski(k3_relat_1(A_552), B_553) | ~r1_tarski(k2_relat_1(A_552), B_553) | ~r1_tarski(k1_relat_1(A_552), B_553) | ~v1_relat_1(A_552))), inference(superposition, [status(thm), theory('equality')], [c_78, c_2108])).
% 16.99/7.14  tff(c_86, plain, (~r1_tarski(k3_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 16.99/7.14  tff(c_22040, plain, (~r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_21953, c_86])).
% 16.99/7.14  tff(c_22076, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_4745, c_5045, c_22040])).
% 16.99/7.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.99/7.14  
% 16.99/7.14  Inference rules
% 16.99/7.14  ----------------------
% 16.99/7.14  #Ref     : 0
% 16.99/7.14  #Sup     : 5375
% 16.99/7.14  #Fact    : 0
% 16.99/7.14  #Define  : 0
% 16.99/7.14  #Split   : 5
% 16.99/7.14  #Chain   : 0
% 16.99/7.14  #Close   : 0
% 16.99/7.14  
% 16.99/7.14  Ordering : KBO
% 16.99/7.14  
% 16.99/7.14  Simplification rules
% 16.99/7.14  ----------------------
% 16.99/7.14  #Subsume      : 673
% 16.99/7.14  #Demod        : 3733
% 16.99/7.14  #Tautology    : 2674
% 16.99/7.14  #SimpNegUnit  : 2
% 16.99/7.14  #BackRed      : 26
% 16.99/7.14  
% 16.99/7.14  #Partial instantiations: 0
% 16.99/7.14  #Strategies tried      : 1
% 16.99/7.14  
% 16.99/7.14  Timing (in seconds)
% 16.99/7.14  ----------------------
% 16.99/7.15  Preprocessing        : 0.60
% 16.99/7.15  Parsing              : 0.31
% 16.99/7.15  CNF conversion       : 0.05
% 16.99/7.15  Main loop            : 5.67
% 16.99/7.15  Inferencing          : 1.08
% 16.99/7.15  Reduction            : 2.72
% 16.99/7.15  Demodulation         : 2.25
% 16.99/7.15  BG Simplification    : 0.14
% 16.99/7.15  Subsumption          : 1.39
% 16.99/7.15  Abstraction          : 0.15
% 16.99/7.15  MUC search           : 0.00
% 16.99/7.15  Cooper               : 0.00
% 16.99/7.15  Total                : 6.34
% 16.99/7.15  Index Insertion      : 0.00
% 16.99/7.15  Index Deletion       : 0.00
% 16.99/7.15  Index Matching       : 0.00
% 16.99/7.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
