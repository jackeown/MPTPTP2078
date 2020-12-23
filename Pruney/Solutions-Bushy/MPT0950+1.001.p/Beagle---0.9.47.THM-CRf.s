%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0950+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 17.99s
% Output     : CNFRefutation 18.13s
% Verified   : 
% Statistics : Number of formulae       :  140 (1852 expanded)
%              Number of leaves         :   44 ( 655 expanded)
%              Depth                    :   28
%              Number of atoms          :  430 (5367 expanded)
%              Number of equality atoms :   38 ( 421 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > m1_subset_1 > v3_ordinal1 > v2_wellord1 > v2_ordinal1 > v1_relat_1 > v1_ordinal1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k2_wellord2 > k1_zfmisc_1 > k1_wellord2 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_wellord2,type,(
    k2_wellord2: $i > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A,B] :
        ( v3_ordinal1(B)
       => ( r1_tarski(A,B)
         => r1_ordinal1(k2_wellord2(k1_wellord2(A)),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord2)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => r1_ordinal1(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).

tff(f_153,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( r1_tarski(B,A)
         => v2_wellord1(k1_wellord2(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_wellord2)).

tff(f_80,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v3_ordinal1(k2_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_30,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_146,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

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

tff(f_142,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r1_tarski(A,k3_relat_1(B))
          & v2_wellord1(B)
          & ~ r4_wellord1(B,k2_wellord1(B,A))
          & ! [C] :
              ~ ( r2_hidden(C,k3_relat_1(B))
                & r4_wellord1(k2_wellord1(B,k1_wellord1(B,C)),k2_wellord1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_wellord1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => v3_ordinal1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_ordinal1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( B = k2_wellord2(A)
            <=> r4_wellord1(A,k1_wellord2(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_wellord2)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_107,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(c_70,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_46,plain,(
    ! [A_26,B_27] :
      ( r1_ordinal1(A_26,A_26)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_121,plain,(
    ! [B_27] : ~ v3_ordinal1(B_27) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_70])).

tff(c_126,plain,(
    ! [A_26] :
      ( r1_ordinal1(A_26,A_26)
      | ~ v3_ordinal1(A_26) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_68,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_133,plain,(
    ! [B_65,A_66] :
      ( v2_wellord1(k1_wellord2(B_65))
      | ~ r1_tarski(B_65,A_66)
      | ~ v3_ordinal1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_135,plain,
    ( v2_wellord1(k1_wellord2('#skF_5'))
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_133])).

tff(c_138,plain,(
    v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_135])).

tff(c_38,plain,(
    ! [A_22] : v1_relat_1(k1_wellord2(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [A_23] :
      ( v3_ordinal1(k2_wellord2(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_206,plain,(
    ! [B_83,A_84] :
      ( r1_ordinal1(B_83,A_84)
      | r1_ordinal1(A_84,B_83)
      | ~ v3_ordinal1(B_83)
      | ~ v3_ordinal1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    ~ r1_ordinal1(k2_wellord2(k1_wellord2('#skF_5')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_209,plain,
    ( r1_ordinal1('#skF_6',k2_wellord2(k1_wellord2('#skF_5')))
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5')))
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_206,c_66])).

tff(c_215,plain,
    ( r1_ordinal1('#skF_6',k2_wellord2(k1_wellord2('#skF_5')))
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_209])).

tff(c_219,plain,(
    ~ v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_222,plain,(
    ~ v1_relat_1(k1_wellord2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_219])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_222])).

tff(c_228,plain,(
    v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_212,plain,
    ( r1_ordinal1('#skF_6',k2_wellord2(k1_wellord2('#skF_5')))
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_206,c_66])).

tff(c_218,plain,
    ( r1_ordinal1('#skF_6',k2_wellord2(k1_wellord2('#skF_5')))
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_212])).

tff(c_239,plain,(
    r1_ordinal1('#skF_6',k2_wellord2(k1_wellord2('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_218])).

tff(c_149,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | ~ r1_ordinal1(A_71,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_64,plain,(
    ! [B_46,A_44] :
      ( v2_wellord1(k1_wellord2(B_46))
      | ~ r1_tarski(B_46,A_44)
      | ~ v3_ordinal1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_241,plain,(
    ! [A_87,B_88] :
      ( v2_wellord1(k1_wellord2(A_87))
      | ~ r1_ordinal1(A_87,B_88)
      | ~ v3_ordinal1(B_88)
      | ~ v3_ordinal1(A_87) ) ),
    inference(resolution,[status(thm)],[c_149,c_64])).

tff(c_243,plain,
    ( v2_wellord1(k1_wellord2('#skF_6'))
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5')))
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_239,c_241])).

tff(c_252,plain,(
    v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_228,c_243])).

tff(c_78,plain,(
    ! [A_48] :
      ( v1_ordinal1(A_48)
      | ~ v3_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_82,plain,(
    v1_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_78])).

tff(c_44,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ r1_ordinal1(A_24,B_25)
      | ~ v3_ordinal1(B_25)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    ! [B_43,A_42] :
      ( k2_wellord1(k1_wellord2(B_43),A_42) = k1_wellord2(A_42)
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_22,plain,(
    ! [A_7] :
      ( k3_relat_1(k1_wellord2(A_7)) = A_7
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_76,plain,(
    ! [A_7] : k3_relat_1(k1_wellord2(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22])).

tff(c_384,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_4'(A_106,B_107),k3_relat_1(B_107))
      | r4_wellord1(B_107,k2_wellord1(B_107,A_106))
      | ~ v2_wellord1(B_107)
      | ~ r1_tarski(A_106,k3_relat_1(B_107))
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_392,plain,(
    ! [A_106,A_7] :
      ( r2_hidden('#skF_4'(A_106,k1_wellord2(A_7)),A_7)
      | r4_wellord1(k1_wellord2(A_7),k2_wellord1(k1_wellord2(A_7),A_106))
      | ~ v2_wellord1(k1_wellord2(A_7))
      | ~ r1_tarski(A_106,k3_relat_1(k1_wellord2(A_7)))
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_384])).

tff(c_800,plain,(
    ! [A_150,A_151] :
      ( r2_hidden('#skF_4'(A_150,k1_wellord2(A_151)),A_151)
      | r4_wellord1(k1_wellord2(A_151),k2_wellord1(k1_wellord2(A_151),A_150))
      | ~ v2_wellord1(k1_wellord2(A_151))
      | ~ r1_tarski(A_150,A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_76,c_392])).

tff(c_847,plain,(
    ! [A_164,B_165] :
      ( r2_hidden('#skF_4'(A_164,k1_wellord2(B_165)),B_165)
      | r4_wellord1(k1_wellord2(B_165),k1_wellord2(A_164))
      | ~ v2_wellord1(k1_wellord2(B_165))
      | ~ r1_tarski(A_164,B_165)
      | ~ r1_tarski(A_164,B_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_800])).

tff(c_52,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(A_31,k1_zfmisc_1(B_32))
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_170,plain,(
    ! [A_75,C_76,B_77] :
      ( m1_subset_1(A_75,C_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(C_76))
      | ~ r2_hidden(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_173,plain,(
    ! [A_75,B_32,A_31] :
      ( m1_subset_1(A_75,B_32)
      | ~ r2_hidden(A_75,A_31)
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_52,c_170])).

tff(c_1154,plain,(
    ! [A_191,B_192,B_193] :
      ( m1_subset_1('#skF_4'(A_191,k1_wellord2(B_192)),B_193)
      | ~ r1_tarski(B_192,B_193)
      | r4_wellord1(k1_wellord2(B_192),k1_wellord2(A_191))
      | ~ v2_wellord1(k1_wellord2(B_192))
      | ~ r1_tarski(A_191,B_192) ) ),
    inference(resolution,[status(thm)],[c_847,c_173])).

tff(c_6,plain,(
    ! [B_4,A_2] :
      ( v3_ordinal1(B_4)
      | ~ m1_subset_1(B_4,A_2)
      | ~ v3_ordinal1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1491,plain,(
    ! [A_226,B_227,B_228] :
      ( v3_ordinal1('#skF_4'(A_226,k1_wellord2(B_227)))
      | ~ v3_ordinal1(B_228)
      | ~ r1_tarski(B_227,B_228)
      | r4_wellord1(k1_wellord2(B_227),k1_wellord2(A_226))
      | ~ v2_wellord1(k1_wellord2(B_227))
      | ~ r1_tarski(A_226,B_227) ) ),
    inference(resolution,[status(thm)],[c_1154,c_6])).

tff(c_2294,plain,(
    ! [A_286,A_287,B_288] :
      ( v3_ordinal1('#skF_4'(A_286,k1_wellord2(A_287)))
      | r4_wellord1(k1_wellord2(A_287),k1_wellord2(A_286))
      | ~ v2_wellord1(k1_wellord2(A_287))
      | ~ r1_tarski(A_286,A_287)
      | ~ r1_ordinal1(A_287,B_288)
      | ~ v3_ordinal1(B_288)
      | ~ v3_ordinal1(A_287) ) ),
    inference(resolution,[status(thm)],[c_44,c_1491])).

tff(c_2300,plain,(
    ! [A_286] :
      ( v3_ordinal1('#skF_4'(A_286,k1_wellord2('#skF_6')))
      | r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2(A_286))
      | ~ v2_wellord1(k1_wellord2('#skF_6'))
      | ~ r1_tarski(A_286,'#skF_6')
      | ~ v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5')))
      | ~ v3_ordinal1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_239,c_2294])).

tff(c_2315,plain,(
    ! [A_289] :
      ( v3_ordinal1('#skF_4'(A_289,k1_wellord2('#skF_6')))
      | r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2(A_289))
      | ~ r1_tarski(A_289,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_228,c_252,c_2300])).

tff(c_56,plain,(
    ! [B_38,A_36] :
      ( r4_wellord1(B_38,A_36)
      | ~ r4_wellord1(A_36,B_38)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2320,plain,(
    ! [A_289] :
      ( r4_wellord1(k1_wellord2(A_289),k1_wellord2('#skF_6'))
      | ~ v1_relat_1(k1_wellord2(A_289))
      | ~ v1_relat_1(k1_wellord2('#skF_6'))
      | v3_ordinal1('#skF_4'(A_289,k1_wellord2('#skF_6')))
      | ~ r1_tarski(A_289,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2315,c_56])).

tff(c_2327,plain,(
    ! [A_290] :
      ( r4_wellord1(k1_wellord2(A_290),k1_wellord2('#skF_6'))
      | v3_ordinal1('#skF_4'(A_290,k1_wellord2('#skF_6')))
      | ~ r1_tarski(A_290,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_2320])).

tff(c_34,plain,(
    ! [A_19,B_21] :
      ( k2_wellord2(A_19) = B_21
      | ~ r4_wellord1(A_19,k1_wellord2(B_21))
      | ~ v3_ordinal1(B_21)
      | ~ v2_wellord1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2330,plain,(
    ! [A_290] :
      ( k2_wellord2(k1_wellord2(A_290)) = '#skF_6'
      | ~ v3_ordinal1('#skF_6')
      | ~ v2_wellord1(k1_wellord2(A_290))
      | ~ v1_relat_1(k1_wellord2(A_290))
      | v3_ordinal1('#skF_4'(A_290,k1_wellord2('#skF_6')))
      | ~ r1_tarski(A_290,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2327,c_34])).

tff(c_2335,plain,(
    ! [A_290] :
      ( k2_wellord2(k1_wellord2(A_290)) = '#skF_6'
      | ~ v2_wellord1(k1_wellord2(A_290))
      | v3_ordinal1('#skF_4'(A_290,k1_wellord2('#skF_6')))
      | ~ r1_tarski(A_290,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_70,c_2330])).

tff(c_28,plain,(
    ! [B_18,A_15] :
      ( r1_tarski(B_18,A_15)
      | ~ r2_hidden(B_18,A_15)
      | ~ v1_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_867,plain,(
    ! [A_164,B_165] :
      ( r1_tarski('#skF_4'(A_164,k1_wellord2(B_165)),B_165)
      | ~ v1_ordinal1(B_165)
      | r4_wellord1(k1_wellord2(B_165),k1_wellord2(A_164))
      | ~ v2_wellord1(k1_wellord2(B_165))
      | ~ r1_tarski(A_164,B_165) ) ),
    inference(resolution,[status(thm)],[c_847,c_28])).

tff(c_863,plain,(
    ! [A_164,B_165] :
      ( r4_wellord1(k1_wellord2(A_164),k1_wellord2(B_165))
      | ~ v1_relat_1(k1_wellord2(A_164))
      | ~ v1_relat_1(k1_wellord2(B_165))
      | r2_hidden('#skF_4'(A_164,k1_wellord2(B_165)),B_165)
      | ~ v2_wellord1(k1_wellord2(B_165))
      | ~ r1_tarski(A_164,B_165) ) ),
    inference(resolution,[status(thm)],[c_847,c_56])).

tff(c_874,plain,(
    ! [A_166,B_167] :
      ( r4_wellord1(k1_wellord2(A_166),k1_wellord2(B_167))
      | r2_hidden('#skF_4'(A_166,k1_wellord2(B_167)),B_167)
      | ~ v2_wellord1(k1_wellord2(B_167))
      | ~ r1_tarski(A_166,B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_863])).

tff(c_879,plain,(
    ! [B_167,A_166] :
      ( r4_wellord1(k1_wellord2(B_167),k1_wellord2(A_166))
      | ~ v1_relat_1(k1_wellord2(B_167))
      | ~ v1_relat_1(k1_wellord2(A_166))
      | r2_hidden('#skF_4'(A_166,k1_wellord2(B_167)),B_167)
      | ~ v2_wellord1(k1_wellord2(B_167))
      | ~ r1_tarski(A_166,B_167) ) ),
    inference(resolution,[status(thm)],[c_874,c_56])).

tff(c_896,plain,(
    ! [B_167,A_166] :
      ( r4_wellord1(k1_wellord2(B_167),k1_wellord2(A_166))
      | r2_hidden('#skF_4'(A_166,k1_wellord2(B_167)),B_167)
      | ~ v2_wellord1(k1_wellord2(B_167))
      | ~ r1_tarski(A_166,B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_879])).

tff(c_48,plain,(
    ! [B_30,A_28] :
      ( k1_wellord1(k1_wellord2(B_30),A_28) = A_28
      | ~ r2_hidden(A_28,B_30)
      | ~ v3_ordinal1(B_30)
      | ~ v3_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_438,plain,(
    ! [B_121,A_122] :
      ( r4_wellord1(k2_wellord1(B_121,k1_wellord1(B_121,'#skF_4'(A_122,B_121))),k2_wellord1(B_121,A_122))
      | r4_wellord1(B_121,k2_wellord1(B_121,A_122))
      | ~ v2_wellord1(B_121)
      | ~ r1_tarski(A_122,k3_relat_1(B_121))
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_451,plain,(
    ! [B_43,A_42] :
      ( r4_wellord1(k2_wellord1(k1_wellord2(B_43),k1_wellord1(k1_wellord2(B_43),'#skF_4'(A_42,k1_wellord2(B_43)))),k1_wellord2(A_42))
      | r4_wellord1(k1_wellord2(B_43),k2_wellord1(k1_wellord2(B_43),A_42))
      | ~ v2_wellord1(k1_wellord2(B_43))
      | ~ r1_tarski(A_42,k3_relat_1(k1_wellord2(B_43)))
      | ~ v1_relat_1(k1_wellord2(B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_438])).

tff(c_1111,plain,(
    ! [B_186,A_187] :
      ( r4_wellord1(k2_wellord1(k1_wellord2(B_186),k1_wellord1(k1_wellord2(B_186),'#skF_4'(A_187,k1_wellord2(B_186)))),k1_wellord2(A_187))
      | r4_wellord1(k1_wellord2(B_186),k2_wellord1(k1_wellord2(B_186),A_187))
      | ~ v2_wellord1(k1_wellord2(B_186))
      | ~ r1_tarski(A_187,B_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_76,c_451])).

tff(c_3630,plain,(
    ! [B_418,A_419] :
      ( r4_wellord1(k2_wellord1(k1_wellord2(B_418),'#skF_4'(A_419,k1_wellord2(B_418))),k1_wellord2(A_419))
      | r4_wellord1(k1_wellord2(B_418),k2_wellord1(k1_wellord2(B_418),A_419))
      | ~ v2_wellord1(k1_wellord2(B_418))
      | ~ r1_tarski(A_419,B_418)
      | ~ r2_hidden('#skF_4'(A_419,k1_wellord2(B_418)),B_418)
      | ~ v3_ordinal1(B_418)
      | ~ v3_ordinal1('#skF_4'(A_419,k1_wellord2(B_418))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1111])).

tff(c_8732,plain,(
    ! [A_701,B_702] :
      ( r4_wellord1(k1_wellord2('#skF_4'(A_701,k1_wellord2(B_702))),k1_wellord2(A_701))
      | r4_wellord1(k1_wellord2(B_702),k2_wellord1(k1_wellord2(B_702),A_701))
      | ~ v2_wellord1(k1_wellord2(B_702))
      | ~ r1_tarski(A_701,B_702)
      | ~ r2_hidden('#skF_4'(A_701,k1_wellord2(B_702)),B_702)
      | ~ v3_ordinal1(B_702)
      | ~ v3_ordinal1('#skF_4'(A_701,k1_wellord2(B_702)))
      | ~ r1_tarski('#skF_4'(A_701,k1_wellord2(B_702)),B_702) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_3630])).

tff(c_20848,plain,(
    ! [A_1252,B_1253] :
      ( r4_wellord1(k1_wellord2('#skF_4'(A_1252,k1_wellord2(B_1253))),k1_wellord2(A_1252))
      | r4_wellord1(k1_wellord2(B_1253),k1_wellord2(A_1252))
      | ~ v2_wellord1(k1_wellord2(B_1253))
      | ~ r1_tarski(A_1252,B_1253)
      | ~ r2_hidden('#skF_4'(A_1252,k1_wellord2(B_1253)),B_1253)
      | ~ v3_ordinal1(B_1253)
      | ~ v3_ordinal1('#skF_4'(A_1252,k1_wellord2(B_1253)))
      | ~ r1_tarski('#skF_4'(A_1252,k1_wellord2(B_1253)),B_1253)
      | ~ r1_tarski(A_1252,B_1253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_8732])).

tff(c_20864,plain,(
    ! [A_1254,B_1255] :
      ( r4_wellord1(k1_wellord2('#skF_4'(A_1254,k1_wellord2(B_1255))),k1_wellord2(A_1254))
      | ~ v3_ordinal1(B_1255)
      | ~ v3_ordinal1('#skF_4'(A_1254,k1_wellord2(B_1255)))
      | ~ r1_tarski('#skF_4'(A_1254,k1_wellord2(B_1255)),B_1255)
      | r4_wellord1(k1_wellord2(B_1255),k1_wellord2(A_1254))
      | ~ v2_wellord1(k1_wellord2(B_1255))
      | ~ r1_tarski(A_1254,B_1255) ) ),
    inference(resolution,[status(thm)],[c_896,c_20848])).

tff(c_20960,plain,(
    ! [A_1256,B_1257] :
      ( r4_wellord1(k1_wellord2('#skF_4'(A_1256,k1_wellord2(B_1257))),k1_wellord2(A_1256))
      | ~ v3_ordinal1(B_1257)
      | ~ v3_ordinal1('#skF_4'(A_1256,k1_wellord2(B_1257)))
      | ~ v1_ordinal1(B_1257)
      | r4_wellord1(k1_wellord2(B_1257),k1_wellord2(A_1256))
      | ~ v2_wellord1(k1_wellord2(B_1257))
      | ~ r1_tarski(A_1256,B_1257) ) ),
    inference(resolution,[status(thm)],[c_867,c_20864])).

tff(c_20965,plain,(
    ! [A_1256,B_1257] :
      ( r4_wellord1(k1_wellord2(A_1256),k1_wellord2('#skF_4'(A_1256,k1_wellord2(B_1257))))
      | ~ v1_relat_1(k1_wellord2(A_1256))
      | ~ v1_relat_1(k1_wellord2('#skF_4'(A_1256,k1_wellord2(B_1257))))
      | ~ v3_ordinal1(B_1257)
      | ~ v3_ordinal1('#skF_4'(A_1256,k1_wellord2(B_1257)))
      | ~ v1_ordinal1(B_1257)
      | r4_wellord1(k1_wellord2(B_1257),k1_wellord2(A_1256))
      | ~ v2_wellord1(k1_wellord2(B_1257))
      | ~ r1_tarski(A_1256,B_1257) ) ),
    inference(resolution,[status(thm)],[c_20960,c_56])).

tff(c_20972,plain,(
    ! [A_1258,B_1259] :
      ( r4_wellord1(k1_wellord2(A_1258),k1_wellord2('#skF_4'(A_1258,k1_wellord2(B_1259))))
      | ~ v3_ordinal1(B_1259)
      | ~ v3_ordinal1('#skF_4'(A_1258,k1_wellord2(B_1259)))
      | ~ v1_ordinal1(B_1259)
      | r4_wellord1(k1_wellord2(B_1259),k1_wellord2(A_1258))
      | ~ v2_wellord1(k1_wellord2(B_1259))
      | ~ r1_tarski(A_1258,B_1259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_20965])).

tff(c_20975,plain,(
    ! [A_1258,B_1259] :
      ( k2_wellord2(k1_wellord2(A_1258)) = '#skF_4'(A_1258,k1_wellord2(B_1259))
      | ~ v2_wellord1(k1_wellord2(A_1258))
      | ~ v1_relat_1(k1_wellord2(A_1258))
      | ~ v3_ordinal1(B_1259)
      | ~ v3_ordinal1('#skF_4'(A_1258,k1_wellord2(B_1259)))
      | ~ v1_ordinal1(B_1259)
      | r4_wellord1(k1_wellord2(B_1259),k1_wellord2(A_1258))
      | ~ v2_wellord1(k1_wellord2(B_1259))
      | ~ r1_tarski(A_1258,B_1259) ) ),
    inference(resolution,[status(thm)],[c_20972,c_34])).

tff(c_21241,plain,(
    ! [A_1264,B_1265] :
      ( k2_wellord2(k1_wellord2(A_1264)) = '#skF_4'(A_1264,k1_wellord2(B_1265))
      | ~ v2_wellord1(k1_wellord2(A_1264))
      | ~ v3_ordinal1(B_1265)
      | ~ v3_ordinal1('#skF_4'(A_1264,k1_wellord2(B_1265)))
      | ~ v1_ordinal1(B_1265)
      | r4_wellord1(k1_wellord2(B_1265),k1_wellord2(A_1264))
      | ~ v2_wellord1(k1_wellord2(B_1265))
      | ~ r1_tarski(A_1264,B_1265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20975])).

tff(c_21246,plain,(
    ! [A_1264,B_1265] :
      ( r4_wellord1(k1_wellord2(A_1264),k1_wellord2(B_1265))
      | ~ v1_relat_1(k1_wellord2(A_1264))
      | ~ v1_relat_1(k1_wellord2(B_1265))
      | k2_wellord2(k1_wellord2(A_1264)) = '#skF_4'(A_1264,k1_wellord2(B_1265))
      | ~ v2_wellord1(k1_wellord2(A_1264))
      | ~ v3_ordinal1(B_1265)
      | ~ v3_ordinal1('#skF_4'(A_1264,k1_wellord2(B_1265)))
      | ~ v1_ordinal1(B_1265)
      | ~ v2_wellord1(k1_wellord2(B_1265))
      | ~ r1_tarski(A_1264,B_1265) ) ),
    inference(resolution,[status(thm)],[c_21241,c_56])).

tff(c_21253,plain,(
    ! [A_1266,B_1267] :
      ( r4_wellord1(k1_wellord2(A_1266),k1_wellord2(B_1267))
      | k2_wellord2(k1_wellord2(A_1266)) = '#skF_4'(A_1266,k1_wellord2(B_1267))
      | ~ v2_wellord1(k1_wellord2(A_1266))
      | ~ v3_ordinal1(B_1267)
      | ~ v3_ordinal1('#skF_4'(A_1266,k1_wellord2(B_1267)))
      | ~ v1_ordinal1(B_1267)
      | ~ v2_wellord1(k1_wellord2(B_1267))
      | ~ r1_tarski(A_1266,B_1267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_21246])).

tff(c_21256,plain,(
    ! [A_1266,B_1267] :
      ( k2_wellord2(k1_wellord2(A_1266)) = B_1267
      | ~ v1_relat_1(k1_wellord2(A_1266))
      | k2_wellord2(k1_wellord2(A_1266)) = '#skF_4'(A_1266,k1_wellord2(B_1267))
      | ~ v2_wellord1(k1_wellord2(A_1266))
      | ~ v3_ordinal1(B_1267)
      | ~ v3_ordinal1('#skF_4'(A_1266,k1_wellord2(B_1267)))
      | ~ v1_ordinal1(B_1267)
      | ~ v2_wellord1(k1_wellord2(B_1267))
      | ~ r1_tarski(A_1266,B_1267) ) ),
    inference(resolution,[status(thm)],[c_21253,c_34])).

tff(c_21265,plain,(
    ! [A_1268,B_1269] :
      ( k2_wellord2(k1_wellord2(A_1268)) = B_1269
      | k2_wellord2(k1_wellord2(A_1268)) = '#skF_4'(A_1268,k1_wellord2(B_1269))
      | ~ v2_wellord1(k1_wellord2(A_1268))
      | ~ v3_ordinal1(B_1269)
      | ~ v3_ordinal1('#skF_4'(A_1268,k1_wellord2(B_1269)))
      | ~ v1_ordinal1(B_1269)
      | ~ v2_wellord1(k1_wellord2(B_1269))
      | ~ r1_tarski(A_1268,B_1269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_21256])).

tff(c_21280,plain,(
    ! [A_290] :
      ( k2_wellord2(k1_wellord2(A_290)) = '#skF_4'(A_290,k1_wellord2('#skF_6'))
      | ~ v3_ordinal1('#skF_6')
      | ~ v1_ordinal1('#skF_6')
      | ~ v2_wellord1(k1_wellord2('#skF_6'))
      | k2_wellord2(k1_wellord2(A_290)) = '#skF_6'
      | ~ v2_wellord1(k1_wellord2(A_290))
      | ~ r1_tarski(A_290,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2335,c_21265])).

tff(c_21321,plain,(
    ! [A_1273] :
      ( k2_wellord2(k1_wellord2(A_1273)) = '#skF_4'(A_1273,k1_wellord2('#skF_6'))
      | k2_wellord2(k1_wellord2(A_1273)) = '#skF_6'
      | ~ v2_wellord1(k1_wellord2(A_1273))
      | ~ r1_tarski(A_1273,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_82,c_70,c_21280])).

tff(c_21405,plain,
    ( k2_wellord2(k1_wellord2('#skF_5')) = '#skF_4'('#skF_5',k1_wellord2('#skF_6'))
    | k2_wellord2(k1_wellord2('#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_138,c_21321])).

tff(c_21435,plain,
    ( k2_wellord2(k1_wellord2('#skF_5')) = '#skF_4'('#skF_5',k1_wellord2('#skF_6'))
    | k2_wellord2(k1_wellord2('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_21405])).

tff(c_21436,plain,(
    k2_wellord2(k1_wellord2('#skF_5')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_21435])).

tff(c_21444,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21436,c_66])).

tff(c_21496,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_126,c_21444])).

tff(c_21500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_21496])).

tff(c_21501,plain,(
    k2_wellord2(k1_wellord2('#skF_5')) = '#skF_4'('#skF_5',k1_wellord2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_21435])).

tff(c_21502,plain,(
    k2_wellord2(k1_wellord2('#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_21435])).

tff(c_21503,plain,(
    '#skF_4'('#skF_5',k1_wellord2('#skF_6')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21501,c_21502])).

tff(c_21510,plain,(
    v3_ordinal1('#skF_4'('#skF_5',k1_wellord2('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21501,c_228])).

tff(c_877,plain,(
    ! [A_166,B_167] :
      ( k2_wellord2(k1_wellord2(A_166)) = B_167
      | ~ v3_ordinal1(B_167)
      | ~ v2_wellord1(k1_wellord2(A_166))
      | ~ v1_relat_1(k1_wellord2(A_166))
      | r2_hidden('#skF_4'(A_166,k1_wellord2(B_167)),B_167)
      | ~ v2_wellord1(k1_wellord2(B_167))
      | ~ r1_tarski(A_166,B_167) ) ),
    inference(resolution,[status(thm)],[c_874,c_34])).

tff(c_1595,plain,(
    ! [A_236,B_237] :
      ( k2_wellord2(k1_wellord2(A_236)) = B_237
      | ~ v3_ordinal1(B_237)
      | ~ v2_wellord1(k1_wellord2(A_236))
      | r2_hidden('#skF_4'(A_236,k1_wellord2(B_237)),B_237)
      | ~ v2_wellord1(k1_wellord2(B_237))
      | ~ r1_tarski(A_236,B_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_877])).

tff(c_2486,plain,(
    ! [A_320,B_321] :
      ( r1_tarski('#skF_4'(A_320,k1_wellord2(B_321)),B_321)
      | ~ v1_ordinal1(B_321)
      | k2_wellord2(k1_wellord2(A_320)) = B_321
      | ~ v3_ordinal1(B_321)
      | ~ v2_wellord1(k1_wellord2(A_320))
      | ~ v2_wellord1(k1_wellord2(B_321))
      | ~ r1_tarski(A_320,B_321) ) ),
    inference(resolution,[status(thm)],[c_1595,c_28])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( r1_ordinal1(A_24,B_25)
      | ~ r1_tarski(A_24,B_25)
      | ~ v3_ordinal1(B_25)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2537,plain,(
    ! [A_320,B_321] :
      ( r1_ordinal1('#skF_4'(A_320,k1_wellord2(B_321)),B_321)
      | ~ v3_ordinal1('#skF_4'(A_320,k1_wellord2(B_321)))
      | ~ v1_ordinal1(B_321)
      | k2_wellord2(k1_wellord2(A_320)) = B_321
      | ~ v3_ordinal1(B_321)
      | ~ v2_wellord1(k1_wellord2(A_320))
      | ~ v2_wellord1(k1_wellord2(B_321))
      | ~ r1_tarski(A_320,B_321) ) ),
    inference(resolution,[status(thm)],[c_2486,c_42])).

tff(c_21511,plain,(
    ~ r1_ordinal1('#skF_4'('#skF_5',k1_wellord2('#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21501,c_66])).

tff(c_21821,plain,
    ( ~ v3_ordinal1('#skF_4'('#skF_5',k1_wellord2('#skF_6')))
    | ~ v1_ordinal1('#skF_6')
    | k2_wellord2(k1_wellord2('#skF_5')) = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2537,c_21511])).

tff(c_21850,plain,(
    '#skF_4'('#skF_5',k1_wellord2('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_252,c_138,c_70,c_21501,c_82,c_21510,c_21821])).

tff(c_21852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21503,c_21850])).

%------------------------------------------------------------------------------
