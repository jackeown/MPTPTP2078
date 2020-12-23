%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0939+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:07 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 105 expanded)
%              Number of leaves         :   28 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  174 ( 270 expanded)
%              Number of equality atoms :    5 (  14 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r6_relat_2 > r2_hidden > r1_tarski > r1_ordinal1 > m1_subset_1 > v6_relat_2 > v3_ordinal1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r6_relat_2,type,(
    r6_relat_2: ( $i * $i ) > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v6_relat_2(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_wellord2)).

tff(f_82,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r6_relat_2(A,B)
        <=> ! [C,D] :
              ~ ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & C != D
                & ~ r2_hidden(k4_tarski(C,D),A)
                & ~ r2_hidden(k4_tarski(D,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => v3_ordinal1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> r6_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_2)).

tff(c_50,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    ! [A_32] : v1_relat_1(k1_wellord2(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_96,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_4'(A_49,B_50),B_50)
      | r6_relat_2(A_49,B_50)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_156,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1('#skF_4'(A_63,B_64),B_64)
      | r6_relat_2(A_63,B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(resolution,[status(thm)],[c_96,c_46])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_ordinal1(B_3)
      | ~ m1_subset_1(B_3,A_1)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [A_63,B_64] :
      ( v3_ordinal1('#skF_4'(A_63,B_64))
      | ~ v3_ordinal1(B_64)
      | r6_relat_2(A_63,B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_86,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_3'(A_46,B_47),B_47)
      | r6_relat_2(A_46,B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_136,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1('#skF_3'(A_60,B_61),B_61)
      | r6_relat_2(A_60,B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_86,c_46])).

tff(c_140,plain,(
    ! [A_60,B_61] :
      ( v3_ordinal1('#skF_3'(A_60,B_61))
      | ~ v3_ordinal1(B_61)
      | r6_relat_2(A_60,B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_36,plain,(
    ! [A_15,B_25] :
      ( r2_hidden('#skF_4'(A_15,B_25),B_25)
      | r6_relat_2(A_15,B_25)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ! [A_15,B_25] :
      ( r2_hidden('#skF_3'(A_15,B_25),B_25)
      | r6_relat_2(A_15,B_25)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( r1_ordinal1(B_5,A_4)
      | r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ r1_ordinal1(A_33,B_34)
      | ~ v3_ordinal1(B_34)
      | ~ v3_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [C_13,D_14,A_7] :
      ( r2_hidden(k4_tarski(C_13,D_14),k1_wellord2(A_7))
      | ~ r1_tarski(C_13,D_14)
      | ~ r2_hidden(D_14,A_7)
      | ~ r2_hidden(C_13,A_7)
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_230,plain,(
    ! [C_83,D_84,A_85] :
      ( r2_hidden(k4_tarski(C_83,D_84),k1_wellord2(A_85))
      | ~ r1_tarski(C_83,D_84)
      | ~ r2_hidden(D_84,A_85)
      | ~ r2_hidden(C_83,A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_24])).

tff(c_32,plain,(
    ! [A_15,B_25] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_15,B_25),'#skF_4'(A_15,B_25)),A_15)
      | r6_relat_2(A_15,B_25)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_241,plain,(
    ! [A_85,B_25] :
      ( r6_relat_2(k1_wellord2(A_85),B_25)
      | ~ v1_relat_1(k1_wellord2(A_85))
      | ~ r1_tarski('#skF_3'(k1_wellord2(A_85),B_25),'#skF_4'(k1_wellord2(A_85),B_25))
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_85),B_25),A_85)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_85),B_25),A_85) ) ),
    inference(resolution,[status(thm)],[c_230,c_32])).

tff(c_280,plain,(
    ! [A_98,B_99] :
      ( r6_relat_2(k1_wellord2(A_98),B_99)
      | ~ r1_tarski('#skF_3'(k1_wellord2(A_98),B_99),'#skF_4'(k1_wellord2(A_98),B_99))
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_98),B_99),A_98)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_98),B_99),A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_241])).

tff(c_940,plain,(
    ! [A_187,B_188] :
      ( r6_relat_2(k1_wellord2(A_187),B_188)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_187),B_188),A_187)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_187),B_188),A_187)
      | ~ r1_ordinal1('#skF_3'(k1_wellord2(A_187),B_188),'#skF_4'(k1_wellord2(A_187),B_188))
      | ~ v3_ordinal1('#skF_4'(k1_wellord2(A_187),B_188))
      | ~ v3_ordinal1('#skF_3'(k1_wellord2(A_187),B_188)) ) ),
    inference(resolution,[status(thm)],[c_44,c_280])).

tff(c_949,plain,(
    ! [A_189,B_190] :
      ( r6_relat_2(k1_wellord2(A_189),B_190)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_189),B_190),A_189)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_189),B_190),A_189)
      | r1_ordinal1('#skF_4'(k1_wellord2(A_189),B_190),'#skF_3'(k1_wellord2(A_189),B_190))
      | ~ v3_ordinal1('#skF_3'(k1_wellord2(A_189),B_190))
      | ~ v3_ordinal1('#skF_4'(k1_wellord2(A_189),B_190)) ) ),
    inference(resolution,[status(thm)],[c_4,c_940])).

tff(c_30,plain,(
    ! [A_15,B_25] :
      ( ~ r2_hidden(k4_tarski('#skF_4'(A_15,B_25),'#skF_3'(A_15,B_25)),A_15)
      | r6_relat_2(A_15,B_25)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_237,plain,(
    ! [A_85,B_25] :
      ( r6_relat_2(k1_wellord2(A_85),B_25)
      | ~ v1_relat_1(k1_wellord2(A_85))
      | ~ r1_tarski('#skF_4'(k1_wellord2(A_85),B_25),'#skF_3'(k1_wellord2(A_85),B_25))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_85),B_25),A_85)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_85),B_25),A_85) ) ),
    inference(resolution,[status(thm)],[c_230,c_30])).

tff(c_275,plain,(
    ! [A_96,B_97] :
      ( r6_relat_2(k1_wellord2(A_96),B_97)
      | ~ r1_tarski('#skF_4'(k1_wellord2(A_96),B_97),'#skF_3'(k1_wellord2(A_96),B_97))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_96),B_97),A_96)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_96),B_97),A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_237])).

tff(c_279,plain,(
    ! [A_96,B_97] :
      ( r6_relat_2(k1_wellord2(A_96),B_97)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_96),B_97),A_96)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_96),B_97),A_96)
      | ~ r1_ordinal1('#skF_4'(k1_wellord2(A_96),B_97),'#skF_3'(k1_wellord2(A_96),B_97))
      | ~ v3_ordinal1('#skF_3'(k1_wellord2(A_96),B_97))
      | ~ v3_ordinal1('#skF_4'(k1_wellord2(A_96),B_97)) ) ),
    inference(resolution,[status(thm)],[c_44,c_275])).

tff(c_954,plain,(
    ! [A_191,B_192] :
      ( r6_relat_2(k1_wellord2(A_191),B_192)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_191),B_192),A_191)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_191),B_192),A_191)
      | ~ v3_ordinal1('#skF_3'(k1_wellord2(A_191),B_192))
      | ~ v3_ordinal1('#skF_4'(k1_wellord2(A_191),B_192)) ) ),
    inference(resolution,[status(thm)],[c_949,c_279])).

tff(c_958,plain,(
    ! [B_25] :
      ( ~ r2_hidden('#skF_4'(k1_wellord2(B_25),B_25),B_25)
      | ~ v3_ordinal1('#skF_3'(k1_wellord2(B_25),B_25))
      | ~ v3_ordinal1('#skF_4'(k1_wellord2(B_25),B_25))
      | r6_relat_2(k1_wellord2(B_25),B_25)
      | ~ v1_relat_1(k1_wellord2(B_25)) ) ),
    inference(resolution,[status(thm)],[c_38,c_954])).

tff(c_962,plain,(
    ! [B_193] :
      ( ~ r2_hidden('#skF_4'(k1_wellord2(B_193),B_193),B_193)
      | ~ v3_ordinal1('#skF_3'(k1_wellord2(B_193),B_193))
      | ~ v3_ordinal1('#skF_4'(k1_wellord2(B_193),B_193))
      | r6_relat_2(k1_wellord2(B_193),B_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_958])).

tff(c_966,plain,(
    ! [B_25] :
      ( ~ v3_ordinal1('#skF_3'(k1_wellord2(B_25),B_25))
      | ~ v3_ordinal1('#skF_4'(k1_wellord2(B_25),B_25))
      | r6_relat_2(k1_wellord2(B_25),B_25)
      | ~ v1_relat_1(k1_wellord2(B_25)) ) ),
    inference(resolution,[status(thm)],[c_36,c_962])).

tff(c_970,plain,(
    ! [B_194] :
      ( ~ v3_ordinal1('#skF_3'(k1_wellord2(B_194),B_194))
      | ~ v3_ordinal1('#skF_4'(k1_wellord2(B_194),B_194))
      | r6_relat_2(k1_wellord2(B_194),B_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_966])).

tff(c_974,plain,(
    ! [B_61] :
      ( ~ v3_ordinal1('#skF_4'(k1_wellord2(B_61),B_61))
      | ~ v3_ordinal1(B_61)
      | r6_relat_2(k1_wellord2(B_61),B_61)
      | ~ v1_relat_1(k1_wellord2(B_61)) ) ),
    inference(resolution,[status(thm)],[c_140,c_970])).

tff(c_978,plain,(
    ! [B_195] :
      ( ~ v3_ordinal1('#skF_4'(k1_wellord2(B_195),B_195))
      | ~ v3_ordinal1(B_195)
      | r6_relat_2(k1_wellord2(B_195),B_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_974])).

tff(c_982,plain,(
    ! [B_64] :
      ( ~ v3_ordinal1(B_64)
      | r6_relat_2(k1_wellord2(B_64),B_64)
      | ~ v1_relat_1(k1_wellord2(B_64)) ) ),
    inference(resolution,[status(thm)],[c_160,c_978])).

tff(c_1063,plain,(
    ! [B_199] :
      ( ~ v3_ordinal1(B_199)
      | r6_relat_2(k1_wellord2(B_199),B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_982])).

tff(c_22,plain,(
    ! [A_7] :
      ( k3_relat_1(k1_wellord2(A_7)) = A_7
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_56,plain,(
    ! [A_7] : k3_relat_1(k1_wellord2(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_22])).

tff(c_76,plain,(
    ! [A_45] :
      ( v6_relat_2(A_45)
      | ~ r6_relat_2(A_45,k3_relat_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82,plain,(
    ! [A_7] :
      ( v6_relat_2(k1_wellord2(A_7))
      | ~ r6_relat_2(k1_wellord2(A_7),A_7)
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_76])).

tff(c_85,plain,(
    ! [A_7] :
      ( v6_relat_2(k1_wellord2(A_7))
      | ~ r6_relat_2(k1_wellord2(A_7),A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_82])).

tff(c_1078,plain,(
    ! [B_200] :
      ( v6_relat_2(k1_wellord2(B_200))
      | ~ v3_ordinal1(B_200) ) ),
    inference(resolution,[status(thm)],[c_1063,c_85])).

tff(c_48,plain,(
    ~ v6_relat_2(k1_wellord2('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1081,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1078,c_48])).

tff(c_1085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1081])).

%------------------------------------------------------------------------------
