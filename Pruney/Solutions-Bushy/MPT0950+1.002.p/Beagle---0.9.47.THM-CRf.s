%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0950+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:07 EST 2020

% Result     : Theorem 9.36s
% Output     : CNFRefutation 9.36s
% Verified   : 
% Statistics : Number of formulae       :  142 (1767 expanded)
%              Number of leaves         :   43 ( 635 expanded)
%              Depth                    :   28
%              Number of atoms          :  442 (5440 expanded)
%              Number of equality atoms :   44 ( 553 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > m1_subset_1 > v3_ordinal1 > v2_wellord1 > v2_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_ordinal1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k2_wellord2 > k1_zfmisc_1 > k1_wellord2 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_171,negated_conjecture,(
    ~ ! [A,B] :
        ( v3_ordinal1(B)
       => ( r1_tarski(A,B)
         => r1_ordinal1(k2_wellord2(k1_wellord2(A)),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord2)).

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

tff(f_80,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v3_ordinal1(k2_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord2)).

tff(f_164,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( r1_tarski(B,A)
         => v2_wellord1(k1_wellord2(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_wellord2)).

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

tff(f_157,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_140,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r1_tarski(A,k3_relat_1(B))
          & v2_wellord1(B)
          & ~ r4_wellord1(B,k2_wellord1(B,A))
          & ! [C] :
              ~ ( r2_hidden(C,k3_relat_1(B))
                & r4_wellord1(k2_wellord1(B,k1_wellord1(B,C)),k2_wellord1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_wellord1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => v3_ordinal1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_ordinal1)).

tff(f_124,axiom,(
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

tff(f_101,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(c_74,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_ordinal1(B_6,A_5)
      | r1_ordinal1(A_5,B_6)
      | ~ v3_ordinal1(B_6)
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_210,plain,(
    ! [B_6] :
      ( ~ v3_ordinal1(B_6)
      | r1_ordinal1(B_6,B_6) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_8])).

tff(c_44,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ r1_ordinal1(A_24,B_25)
      | ~ v3_ordinal1(B_25)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_82,plain,(
    ! [A_51] :
      ( v1_ordinal1(A_51)
      | ~ v3_ordinal1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_86,plain,(
    v1_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_82])).

tff(c_38,plain,(
    ! [A_22] : v1_relat_1(k1_wellord2(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [A_23] :
      ( v3_ordinal1(k2_wellord2(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_212,plain,(
    ! [B_88,A_89] :
      ( r1_ordinal1(B_88,A_89)
      | r1_ordinal1(A_89,B_88)
      | ~ v3_ordinal1(B_88)
      | ~ v3_ordinal1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    ~ r1_ordinal1(k2_wellord2(k1_wellord2('#skF_5')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_218,plain,
    ( r1_ordinal1('#skF_6',k2_wellord2(k1_wellord2('#skF_5')))
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_212,c_70])).

tff(c_224,plain,
    ( r1_ordinal1('#skF_6',k2_wellord2(k1_wellord2('#skF_5')))
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_218])).

tff(c_239,plain,(
    ~ v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_242,plain,(
    ~ v1_relat_1(k1_wellord2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_239])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_242])).

tff(c_248,plain,(
    v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_247,plain,(
    r1_ordinal1('#skF_6',k2_wellord2(k1_wellord2('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_226,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(A_91,B_92)
      | ~ r1_ordinal1(A_91,B_92)
      | ~ v3_ordinal1(B_92)
      | ~ v3_ordinal1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_68,plain,(
    ! [B_49,A_47] :
      ( v2_wellord1(k1_wellord2(B_49))
      | ~ r1_tarski(B_49,A_47)
      | ~ v3_ordinal1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_287,plain,(
    ! [A_96,B_97] :
      ( v2_wellord1(k1_wellord2(A_96))
      | ~ r1_ordinal1(A_96,B_97)
      | ~ v3_ordinal1(B_97)
      | ~ v3_ordinal1(A_96) ) ),
    inference(resolution,[status(thm)],[c_226,c_68])).

tff(c_289,plain,
    ( v2_wellord1(k1_wellord2('#skF_6'))
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2('#skF_5')))
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_247,c_287])).

tff(c_298,plain,(
    v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_248,c_289])).

tff(c_22,plain,(
    ! [A_7] :
      ( k3_relat_1(k1_wellord2(A_7)) = A_7
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    ! [A_7] : k3_relat_1(k1_wellord2(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22])).

tff(c_66,plain,(
    ! [B_46,A_45] :
      ( k2_wellord1(k1_wellord2(B_46),A_45) = k1_wellord2(A_45)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_523,plain,(
    ! [A_133,B_134] :
      ( r2_hidden('#skF_4'(A_133,B_134),k3_relat_1(B_134))
      | r4_wellord1(B_134,k2_wellord1(B_134,A_133))
      | ~ v2_wellord1(B_134)
      | ~ r1_tarski(A_133,k3_relat_1(B_134))
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_48,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7314,plain,(
    ! [A_9307,B_9308] :
      ( m1_subset_1('#skF_4'(A_9307,B_9308),k3_relat_1(B_9308))
      | r4_wellord1(B_9308,k2_wellord1(B_9308,A_9307))
      | ~ v2_wellord1(B_9308)
      | ~ r1_tarski(A_9307,k3_relat_1(B_9308))
      | ~ v1_relat_1(B_9308) ) ),
    inference(resolution,[status(thm)],[c_523,c_48])).

tff(c_6,plain,(
    ! [B_4,A_2] :
      ( v3_ordinal1(B_4)
      | ~ m1_subset_1(B_4,A_2)
      | ~ v3_ordinal1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7436,plain,(
    ! [A_9321,B_9322] :
      ( v3_ordinal1('#skF_4'(A_9321,B_9322))
      | ~ v3_ordinal1(k3_relat_1(B_9322))
      | r4_wellord1(B_9322,k2_wellord1(B_9322,A_9321))
      | ~ v2_wellord1(B_9322)
      | ~ r1_tarski(A_9321,k3_relat_1(B_9322))
      | ~ v1_relat_1(B_9322) ) ),
    inference(resolution,[status(thm)],[c_7314,c_6])).

tff(c_7441,plain,(
    ! [A_45,B_46] :
      ( v3_ordinal1('#skF_4'(A_45,k1_wellord2(B_46)))
      | ~ v3_ordinal1(k3_relat_1(k1_wellord2(B_46)))
      | r4_wellord1(k1_wellord2(B_46),k1_wellord2(A_45))
      | ~ v2_wellord1(k1_wellord2(B_46))
      | ~ r1_tarski(A_45,k3_relat_1(k1_wellord2(B_46)))
      | ~ v1_relat_1(k1_wellord2(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_7436])).

tff(c_7445,plain,(
    ! [A_9323,B_9324] :
      ( v3_ordinal1('#skF_4'(A_9323,k1_wellord2(B_9324)))
      | ~ v3_ordinal1(B_9324)
      | r4_wellord1(k1_wellord2(B_9324),k1_wellord2(A_9323))
      | ~ v2_wellord1(k1_wellord2(B_9324))
      | ~ r1_tarski(A_9323,B_9324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80,c_80,c_7441])).

tff(c_56,plain,(
    ! [B_37,A_35] :
      ( r4_wellord1(B_37,A_35)
      | ~ r4_wellord1(A_35,B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7450,plain,(
    ! [A_9323,B_9324] :
      ( r4_wellord1(k1_wellord2(A_9323),k1_wellord2(B_9324))
      | ~ v1_relat_1(k1_wellord2(A_9323))
      | ~ v1_relat_1(k1_wellord2(B_9324))
      | v3_ordinal1('#skF_4'(A_9323,k1_wellord2(B_9324)))
      | ~ v3_ordinal1(B_9324)
      | ~ v2_wellord1(k1_wellord2(B_9324))
      | ~ r1_tarski(A_9323,B_9324) ) ),
    inference(resolution,[status(thm)],[c_7445,c_56])).

tff(c_7457,plain,(
    ! [A_9325,B_9326] :
      ( r4_wellord1(k1_wellord2(A_9325),k1_wellord2(B_9326))
      | v3_ordinal1('#skF_4'(A_9325,k1_wellord2(B_9326)))
      | ~ v3_ordinal1(B_9326)
      | ~ v2_wellord1(k1_wellord2(B_9326))
      | ~ r1_tarski(A_9325,B_9326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_7450])).

tff(c_34,plain,(
    ! [A_19,B_21] :
      ( k2_wellord2(A_19) = B_21
      | ~ r4_wellord1(A_19,k1_wellord2(B_21))
      | ~ v3_ordinal1(B_21)
      | ~ v2_wellord1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7460,plain,(
    ! [A_9325,B_9326] :
      ( k2_wellord2(k1_wellord2(A_9325)) = B_9326
      | ~ v2_wellord1(k1_wellord2(A_9325))
      | ~ v1_relat_1(k1_wellord2(A_9325))
      | v3_ordinal1('#skF_4'(A_9325,k1_wellord2(B_9326)))
      | ~ v3_ordinal1(B_9326)
      | ~ v2_wellord1(k1_wellord2(B_9326))
      | ~ r1_tarski(A_9325,B_9326) ) ),
    inference(resolution,[status(thm)],[c_7457,c_34])).

tff(c_7465,plain,(
    ! [A_9325,B_9326] :
      ( k2_wellord2(k1_wellord2(A_9325)) = B_9326
      | ~ v2_wellord1(k1_wellord2(A_9325))
      | v3_ordinal1('#skF_4'(A_9325,k1_wellord2(B_9326)))
      | ~ v3_ordinal1(B_9326)
      | ~ v2_wellord1(k1_wellord2(B_9326))
      | ~ r1_tarski(A_9325,B_9326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7460])).

tff(c_535,plain,(
    ! [A_133,A_7] :
      ( r2_hidden('#skF_4'(A_133,k1_wellord2(A_7)),A_7)
      | r4_wellord1(k1_wellord2(A_7),k2_wellord1(k1_wellord2(A_7),A_133))
      | ~ v2_wellord1(k1_wellord2(A_7))
      | ~ r1_tarski(A_133,k3_relat_1(k1_wellord2(A_7)))
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_523])).

tff(c_6741,plain,(
    ! [A_9093,A_9094] :
      ( r2_hidden('#skF_4'(A_9093,k1_wellord2(A_9094)),A_9094)
      | r4_wellord1(k1_wellord2(A_9094),k2_wellord1(k1_wellord2(A_9094),A_9093))
      | ~ v2_wellord1(k1_wellord2(A_9094))
      | ~ r1_tarski(A_9093,A_9094) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80,c_535])).

tff(c_7519,plain,(
    ! [A_9338,B_9339] :
      ( r2_hidden('#skF_4'(A_9338,k1_wellord2(B_9339)),B_9339)
      | r4_wellord1(k1_wellord2(B_9339),k1_wellord2(A_9338))
      | ~ v2_wellord1(k1_wellord2(B_9339))
      | ~ r1_tarski(A_9338,B_9339)
      | ~ r1_tarski(A_9338,B_9339) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6741])).

tff(c_28,plain,(
    ! [B_18,A_15] :
      ( r1_tarski(B_18,A_15)
      | ~ r2_hidden(B_18,A_15)
      | ~ v1_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7534,plain,(
    ! [A_9338,B_9339] :
      ( r1_tarski('#skF_4'(A_9338,k1_wellord2(B_9339)),B_9339)
      | ~ v1_ordinal1(B_9339)
      | r4_wellord1(k1_wellord2(B_9339),k1_wellord2(A_9338))
      | ~ v2_wellord1(k1_wellord2(B_9339))
      | ~ r1_tarski(A_9338,B_9339) ) ),
    inference(resolution,[status(thm)],[c_7519,c_28])).

tff(c_7533,plain,(
    ! [A_9338,B_9339] :
      ( r4_wellord1(k1_wellord2(A_9338),k1_wellord2(B_9339))
      | ~ v1_relat_1(k1_wellord2(A_9338))
      | ~ v1_relat_1(k1_wellord2(B_9339))
      | r2_hidden('#skF_4'(A_9338,k1_wellord2(B_9339)),B_9339)
      | ~ v2_wellord1(k1_wellord2(B_9339))
      | ~ r1_tarski(A_9338,B_9339) ) ),
    inference(resolution,[status(thm)],[c_7519,c_56])).

tff(c_7567,plain,(
    ! [A_9342,B_9343] :
      ( r4_wellord1(k1_wellord2(A_9342),k1_wellord2(B_9343))
      | r2_hidden('#skF_4'(A_9342,k1_wellord2(B_9343)),B_9343)
      | ~ v2_wellord1(k1_wellord2(B_9343))
      | ~ r1_tarski(A_9342,B_9343) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_7533])).

tff(c_7572,plain,(
    ! [B_9343,A_9342] :
      ( r4_wellord1(k1_wellord2(B_9343),k1_wellord2(A_9342))
      | ~ v1_relat_1(k1_wellord2(B_9343))
      | ~ v1_relat_1(k1_wellord2(A_9342))
      | r2_hidden('#skF_4'(A_9342,k1_wellord2(B_9343)),B_9343)
      | ~ v2_wellord1(k1_wellord2(B_9343))
      | ~ r1_tarski(A_9342,B_9343) ) ),
    inference(resolution,[status(thm)],[c_7567,c_56])).

tff(c_7587,plain,(
    ! [B_9343,A_9342] :
      ( r4_wellord1(k1_wellord2(B_9343),k1_wellord2(A_9342))
      | r2_hidden('#skF_4'(A_9342,k1_wellord2(B_9343)),B_9343)
      | ~ v2_wellord1(k1_wellord2(B_9343))
      | ~ r1_tarski(A_9342,B_9343) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_7572])).

tff(c_46,plain,(
    ! [B_28,A_26] :
      ( k1_wellord1(k1_wellord2(B_28),A_26) = A_26
      | ~ r2_hidden(A_26,B_28)
      | ~ v3_ordinal1(B_28)
      | ~ v3_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_588,plain,(
    ! [B_145,A_146] :
      ( r4_wellord1(k2_wellord1(B_145,k1_wellord1(B_145,'#skF_4'(A_146,B_145))),k2_wellord1(B_145,A_146))
      | r4_wellord1(B_145,k2_wellord1(B_145,A_146))
      | ~ v2_wellord1(B_145)
      | ~ r1_tarski(A_146,k3_relat_1(B_145))
      | ~ v1_relat_1(B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_601,plain,(
    ! [B_46,A_45] :
      ( r4_wellord1(k2_wellord1(k1_wellord2(B_46),k1_wellord1(k1_wellord2(B_46),'#skF_4'(A_45,k1_wellord2(B_46)))),k1_wellord2(A_45))
      | r4_wellord1(k1_wellord2(B_46),k2_wellord1(k1_wellord2(B_46),A_45))
      | ~ v2_wellord1(k1_wellord2(B_46))
      | ~ r1_tarski(A_45,k3_relat_1(k1_wellord2(B_46)))
      | ~ v1_relat_1(k1_wellord2(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_588])).

tff(c_7352,plain,(
    ! [B_9313,A_9314] :
      ( r4_wellord1(k2_wellord1(k1_wellord2(B_9313),k1_wellord1(k1_wellord2(B_9313),'#skF_4'(A_9314,k1_wellord2(B_9313)))),k1_wellord2(A_9314))
      | r4_wellord1(k1_wellord2(B_9313),k2_wellord1(k1_wellord2(B_9313),A_9314))
      | ~ v2_wellord1(k1_wellord2(B_9313))
      | ~ r1_tarski(A_9314,B_9313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80,c_601])).

tff(c_8304,plain,(
    ! [B_9451,A_9452] :
      ( r4_wellord1(k2_wellord1(k1_wellord2(B_9451),'#skF_4'(A_9452,k1_wellord2(B_9451))),k1_wellord2(A_9452))
      | r4_wellord1(k1_wellord2(B_9451),k2_wellord1(k1_wellord2(B_9451),A_9452))
      | ~ v2_wellord1(k1_wellord2(B_9451))
      | ~ r1_tarski(A_9452,B_9451)
      | ~ r2_hidden('#skF_4'(A_9452,k1_wellord2(B_9451)),B_9451)
      | ~ v3_ordinal1(B_9451)
      | ~ v3_ordinal1('#skF_4'(A_9452,k1_wellord2(B_9451))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_7352])).

tff(c_8634,plain,(
    ! [A_9512,B_9513] :
      ( r4_wellord1(k1_wellord2('#skF_4'(A_9512,k1_wellord2(B_9513))),k1_wellord2(A_9512))
      | r4_wellord1(k1_wellord2(B_9513),k2_wellord1(k1_wellord2(B_9513),A_9512))
      | ~ v2_wellord1(k1_wellord2(B_9513))
      | ~ r1_tarski(A_9512,B_9513)
      | ~ r2_hidden('#skF_4'(A_9512,k1_wellord2(B_9513)),B_9513)
      | ~ v3_ordinal1(B_9513)
      | ~ v3_ordinal1('#skF_4'(A_9512,k1_wellord2(B_9513)))
      | ~ r1_tarski('#skF_4'(A_9512,k1_wellord2(B_9513)),B_9513) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_8304])).

tff(c_9165,plain,(
    ! [A_9547,B_9548] :
      ( r4_wellord1(k1_wellord2('#skF_4'(A_9547,k1_wellord2(B_9548))),k1_wellord2(A_9547))
      | r4_wellord1(k1_wellord2(B_9548),k1_wellord2(A_9547))
      | ~ v2_wellord1(k1_wellord2(B_9548))
      | ~ r1_tarski(A_9547,B_9548)
      | ~ r2_hidden('#skF_4'(A_9547,k1_wellord2(B_9548)),B_9548)
      | ~ v3_ordinal1(B_9548)
      | ~ v3_ordinal1('#skF_4'(A_9547,k1_wellord2(B_9548)))
      | ~ r1_tarski('#skF_4'(A_9547,k1_wellord2(B_9548)),B_9548)
      | ~ r1_tarski(A_9547,B_9548) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_8634])).

tff(c_9185,plain,(
    ! [A_9549,B_9550] :
      ( r4_wellord1(k1_wellord2('#skF_4'(A_9549,k1_wellord2(B_9550))),k1_wellord2(A_9549))
      | ~ v3_ordinal1(B_9550)
      | ~ v3_ordinal1('#skF_4'(A_9549,k1_wellord2(B_9550)))
      | ~ r1_tarski('#skF_4'(A_9549,k1_wellord2(B_9550)),B_9550)
      | r4_wellord1(k1_wellord2(B_9550),k1_wellord2(A_9549))
      | ~ v2_wellord1(k1_wellord2(B_9550))
      | ~ r1_tarski(A_9549,B_9550) ) ),
    inference(resolution,[status(thm)],[c_7587,c_9165])).

tff(c_9219,plain,(
    ! [A_9553,B_9554] :
      ( r4_wellord1(k1_wellord2('#skF_4'(A_9553,k1_wellord2(B_9554))),k1_wellord2(A_9553))
      | ~ v3_ordinal1(B_9554)
      | ~ v3_ordinal1('#skF_4'(A_9553,k1_wellord2(B_9554)))
      | ~ v1_ordinal1(B_9554)
      | r4_wellord1(k1_wellord2(B_9554),k1_wellord2(A_9553))
      | ~ v2_wellord1(k1_wellord2(B_9554))
      | ~ r1_tarski(A_9553,B_9554) ) ),
    inference(resolution,[status(thm)],[c_7534,c_9185])).

tff(c_9224,plain,(
    ! [A_9553,B_9554] :
      ( r4_wellord1(k1_wellord2(A_9553),k1_wellord2('#skF_4'(A_9553,k1_wellord2(B_9554))))
      | ~ v1_relat_1(k1_wellord2(A_9553))
      | ~ v1_relat_1(k1_wellord2('#skF_4'(A_9553,k1_wellord2(B_9554))))
      | ~ v3_ordinal1(B_9554)
      | ~ v3_ordinal1('#skF_4'(A_9553,k1_wellord2(B_9554)))
      | ~ v1_ordinal1(B_9554)
      | r4_wellord1(k1_wellord2(B_9554),k1_wellord2(A_9553))
      | ~ v2_wellord1(k1_wellord2(B_9554))
      | ~ r1_tarski(A_9553,B_9554) ) ),
    inference(resolution,[status(thm)],[c_9219,c_56])).

tff(c_9231,plain,(
    ! [A_9555,B_9556] :
      ( r4_wellord1(k1_wellord2(A_9555),k1_wellord2('#skF_4'(A_9555,k1_wellord2(B_9556))))
      | ~ v3_ordinal1(B_9556)
      | ~ v3_ordinal1('#skF_4'(A_9555,k1_wellord2(B_9556)))
      | ~ v1_ordinal1(B_9556)
      | r4_wellord1(k1_wellord2(B_9556),k1_wellord2(A_9555))
      | ~ v2_wellord1(k1_wellord2(B_9556))
      | ~ r1_tarski(A_9555,B_9556) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_9224])).

tff(c_9234,plain,(
    ! [A_9555,B_9556] :
      ( k2_wellord2(k1_wellord2(A_9555)) = '#skF_4'(A_9555,k1_wellord2(B_9556))
      | ~ v2_wellord1(k1_wellord2(A_9555))
      | ~ v1_relat_1(k1_wellord2(A_9555))
      | ~ v3_ordinal1(B_9556)
      | ~ v3_ordinal1('#skF_4'(A_9555,k1_wellord2(B_9556)))
      | ~ v1_ordinal1(B_9556)
      | r4_wellord1(k1_wellord2(B_9556),k1_wellord2(A_9555))
      | ~ v2_wellord1(k1_wellord2(B_9556))
      | ~ r1_tarski(A_9555,B_9556) ) ),
    inference(resolution,[status(thm)],[c_9231,c_34])).

tff(c_9243,plain,(
    ! [A_9557,B_9558] :
      ( k2_wellord2(k1_wellord2(A_9557)) = '#skF_4'(A_9557,k1_wellord2(B_9558))
      | ~ v2_wellord1(k1_wellord2(A_9557))
      | ~ v3_ordinal1(B_9558)
      | ~ v3_ordinal1('#skF_4'(A_9557,k1_wellord2(B_9558)))
      | ~ v1_ordinal1(B_9558)
      | r4_wellord1(k1_wellord2(B_9558),k1_wellord2(A_9557))
      | ~ v2_wellord1(k1_wellord2(B_9558))
      | ~ r1_tarski(A_9557,B_9558) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_9234])).

tff(c_9248,plain,(
    ! [A_9557,B_9558] :
      ( r4_wellord1(k1_wellord2(A_9557),k1_wellord2(B_9558))
      | ~ v1_relat_1(k1_wellord2(A_9557))
      | ~ v1_relat_1(k1_wellord2(B_9558))
      | k2_wellord2(k1_wellord2(A_9557)) = '#skF_4'(A_9557,k1_wellord2(B_9558))
      | ~ v2_wellord1(k1_wellord2(A_9557))
      | ~ v3_ordinal1(B_9558)
      | ~ v3_ordinal1('#skF_4'(A_9557,k1_wellord2(B_9558)))
      | ~ v1_ordinal1(B_9558)
      | ~ v2_wellord1(k1_wellord2(B_9558))
      | ~ r1_tarski(A_9557,B_9558) ) ),
    inference(resolution,[status(thm)],[c_9243,c_56])).

tff(c_9283,plain,(
    ! [A_9561,B_9562] :
      ( r4_wellord1(k1_wellord2(A_9561),k1_wellord2(B_9562))
      | k2_wellord2(k1_wellord2(A_9561)) = '#skF_4'(A_9561,k1_wellord2(B_9562))
      | ~ v2_wellord1(k1_wellord2(A_9561))
      | ~ v3_ordinal1(B_9562)
      | ~ v3_ordinal1('#skF_4'(A_9561,k1_wellord2(B_9562)))
      | ~ v1_ordinal1(B_9562)
      | ~ v2_wellord1(k1_wellord2(B_9562))
      | ~ r1_tarski(A_9561,B_9562) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_9248])).

tff(c_9286,plain,(
    ! [A_9561,B_9562] :
      ( k2_wellord2(k1_wellord2(A_9561)) = B_9562
      | ~ v1_relat_1(k1_wellord2(A_9561))
      | k2_wellord2(k1_wellord2(A_9561)) = '#skF_4'(A_9561,k1_wellord2(B_9562))
      | ~ v2_wellord1(k1_wellord2(A_9561))
      | ~ v3_ordinal1(B_9562)
      | ~ v3_ordinal1('#skF_4'(A_9561,k1_wellord2(B_9562)))
      | ~ v1_ordinal1(B_9562)
      | ~ v2_wellord1(k1_wellord2(B_9562))
      | ~ r1_tarski(A_9561,B_9562) ) ),
    inference(resolution,[status(thm)],[c_9283,c_34])).

tff(c_9295,plain,(
    ! [A_9563,B_9564] :
      ( k2_wellord2(k1_wellord2(A_9563)) = B_9564
      | k2_wellord2(k1_wellord2(A_9563)) = '#skF_4'(A_9563,k1_wellord2(B_9564))
      | ~ v2_wellord1(k1_wellord2(A_9563))
      | ~ v3_ordinal1(B_9564)
      | ~ v3_ordinal1('#skF_4'(A_9563,k1_wellord2(B_9564)))
      | ~ v1_ordinal1(B_9564)
      | ~ v2_wellord1(k1_wellord2(B_9564))
      | ~ r1_tarski(A_9563,B_9564) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_9286])).

tff(c_9308,plain,(
    ! [A_9565,B_9566] :
      ( k2_wellord2(k1_wellord2(A_9565)) = '#skF_4'(A_9565,k1_wellord2(B_9566))
      | ~ v1_ordinal1(B_9566)
      | k2_wellord2(k1_wellord2(A_9565)) = B_9566
      | ~ v2_wellord1(k1_wellord2(A_9565))
      | ~ v3_ordinal1(B_9566)
      | ~ v2_wellord1(k1_wellord2(B_9566))
      | ~ r1_tarski(A_9565,B_9566) ) ),
    inference(resolution,[status(thm)],[c_7465,c_9295])).

tff(c_9372,plain,(
    ! [B_9567] :
      ( k2_wellord2(k1_wellord2('#skF_6')) = '#skF_4'('#skF_6',k1_wellord2(B_9567))
      | ~ v1_ordinal1(B_9567)
      | k2_wellord2(k1_wellord2('#skF_6')) = B_9567
      | ~ v3_ordinal1(B_9567)
      | ~ v2_wellord1(k1_wellord2(B_9567))
      | ~ r1_tarski('#skF_6',B_9567) ) ),
    inference(resolution,[status(thm)],[c_298,c_9308])).

tff(c_9432,plain,
    ( k2_wellord2(k1_wellord2('#skF_6')) = '#skF_4'('#skF_6',k1_wellord2('#skF_6'))
    | ~ v1_ordinal1('#skF_6')
    | k2_wellord2(k1_wellord2('#skF_6')) = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_298,c_9372])).

tff(c_9457,plain,
    ( k2_wellord2(k1_wellord2('#skF_6')) = '#skF_4'('#skF_6',k1_wellord2('#skF_6'))
    | k2_wellord2(k1_wellord2('#skF_6')) = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_86,c_9432])).

tff(c_9459,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9457])).

tff(c_9474,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_6')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_9459])).

tff(c_9481,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9474])).

tff(c_9487,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_210,c_9481])).

tff(c_9497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9487])).

tff(c_9499,plain,(
    r1_tarski('#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_9457])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( r1_ordinal1(A_24,B_25)
      | ~ r1_tarski(A_24,B_25)
      | ~ v3_ordinal1(B_25)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9502,plain,
    ( r1_ordinal1('#skF_6','#skF_6')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_9499,c_42])).

tff(c_9507,plain,(
    r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9502])).

tff(c_72,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_147,plain,(
    ! [B_73,A_74] :
      ( v2_wellord1(k1_wellord2(B_73))
      | ~ r1_tarski(B_73,A_74)
      | ~ v3_ordinal1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_149,plain,
    ( v2_wellord1(k1_wellord2('#skF_5'))
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_147])).

tff(c_152,plain,(
    v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_149])).

tff(c_9511,plain,(
    ! [B_9570] :
      ( k2_wellord2(k1_wellord2('#skF_5')) = '#skF_4'('#skF_5',k1_wellord2(B_9570))
      | ~ v1_ordinal1(B_9570)
      | k2_wellord2(k1_wellord2('#skF_5')) = B_9570
      | ~ v3_ordinal1(B_9570)
      | ~ v2_wellord1(k1_wellord2(B_9570))
      | ~ r1_tarski('#skF_5',B_9570) ) ),
    inference(resolution,[status(thm)],[c_152,c_9308])).

tff(c_9571,plain,
    ( k2_wellord2(k1_wellord2('#skF_5')) = '#skF_4'('#skF_5',k1_wellord2('#skF_6'))
    | ~ v1_ordinal1('#skF_6')
    | k2_wellord2(k1_wellord2('#skF_5')) = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_298,c_9511])).

tff(c_9596,plain,
    ( k2_wellord2(k1_wellord2('#skF_5')) = '#skF_4'('#skF_5',k1_wellord2('#skF_6'))
    | k2_wellord2(k1_wellord2('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_86,c_9571])).

tff(c_10058,plain,(
    k2_wellord2(k1_wellord2('#skF_5')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_9596])).

tff(c_10066,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10058,c_70])).

tff(c_10073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9507,c_10066])).

tff(c_10074,plain,(
    k2_wellord2(k1_wellord2('#skF_5')) = '#skF_4'('#skF_5',k1_wellord2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_9596])).

tff(c_10075,plain,(
    k2_wellord2(k1_wellord2('#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9596])).

tff(c_10077,plain,(
    '#skF_4'('#skF_5',k1_wellord2('#skF_6')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10074,c_10075])).

tff(c_10084,plain,(
    v3_ordinal1('#skF_4'('#skF_5',k1_wellord2('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10074,c_248])).

tff(c_7570,plain,(
    ! [A_9342,B_9343] :
      ( k2_wellord2(k1_wellord2(A_9342)) = B_9343
      | ~ v3_ordinal1(B_9343)
      | ~ v2_wellord1(k1_wellord2(A_9342))
      | ~ v1_relat_1(k1_wellord2(A_9342))
      | r2_hidden('#skF_4'(A_9342,k1_wellord2(B_9343)),B_9343)
      | ~ v2_wellord1(k1_wellord2(B_9343))
      | ~ r1_tarski(A_9342,B_9343) ) ),
    inference(resolution,[status(thm)],[c_7567,c_34])).

tff(c_7865,plain,(
    ! [A_9382,B_9383] :
      ( k2_wellord2(k1_wellord2(A_9382)) = B_9383
      | ~ v3_ordinal1(B_9383)
      | ~ v2_wellord1(k1_wellord2(A_9382))
      | r2_hidden('#skF_4'(A_9382,k1_wellord2(B_9383)),B_9383)
      | ~ v2_wellord1(k1_wellord2(B_9383))
      | ~ r1_tarski(A_9382,B_9383) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7570])).

tff(c_8021,plain,(
    ! [A_9402,B_9403] :
      ( r1_tarski('#skF_4'(A_9402,k1_wellord2(B_9403)),B_9403)
      | ~ v1_ordinal1(B_9403)
      | k2_wellord2(k1_wellord2(A_9402)) = B_9403
      | ~ v3_ordinal1(B_9403)
      | ~ v2_wellord1(k1_wellord2(A_9402))
      | ~ v2_wellord1(k1_wellord2(B_9403))
      | ~ r1_tarski(A_9402,B_9403) ) ),
    inference(resolution,[status(thm)],[c_7865,c_28])).

tff(c_8031,plain,(
    ! [A_9402,B_9403] :
      ( r1_ordinal1('#skF_4'(A_9402,k1_wellord2(B_9403)),B_9403)
      | ~ v3_ordinal1('#skF_4'(A_9402,k1_wellord2(B_9403)))
      | ~ v1_ordinal1(B_9403)
      | k2_wellord2(k1_wellord2(A_9402)) = B_9403
      | ~ v3_ordinal1(B_9403)
      | ~ v2_wellord1(k1_wellord2(A_9402))
      | ~ v2_wellord1(k1_wellord2(B_9403))
      | ~ r1_tarski(A_9402,B_9403) ) ),
    inference(resolution,[status(thm)],[c_8021,c_42])).

tff(c_10085,plain,(
    ~ r1_ordinal1('#skF_4'('#skF_5',k1_wellord2('#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10074,c_70])).

tff(c_10164,plain,
    ( ~ v3_ordinal1('#skF_4'('#skF_5',k1_wellord2('#skF_6')))
    | ~ v1_ordinal1('#skF_6')
    | k2_wellord2(k1_wellord2('#skF_5')) = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_8031,c_10085])).

tff(c_10184,plain,(
    '#skF_4'('#skF_5',k1_wellord2('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_298,c_152,c_74,c_10074,c_86,c_10084,c_10164])).

tff(c_10186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10077,c_10184])).

%------------------------------------------------------------------------------
