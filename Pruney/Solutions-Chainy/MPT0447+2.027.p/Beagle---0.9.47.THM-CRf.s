%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:31 EST 2020

% Result     : Theorem 8.63s
% Output     : CNFRefutation 8.80s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 229 expanded)
%              Number of leaves         :   48 (  96 expanded)
%              Depth                    :   20
%              Number of atoms          :  188 ( 382 expanded)
%              Number of equality atoms :   51 (  97 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_77,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_99,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_111,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_87,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_103,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_129,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

tff(c_66,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_611,plain,(
    ! [A_125] :
      ( k2_xboole_0(k1_relat_1(A_125),k2_relat_1(A_125)) = k3_relat_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_16,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,k2_xboole_0(C_14,B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_626,plain,(
    ! [A_12,A_125] :
      ( r1_tarski(A_12,k3_relat_1(A_125))
      | ~ r1_tarski(A_12,k2_relat_1(A_125))
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_16])).

tff(c_56,plain,(
    ! [A_63] :
      ( k2_xboole_0(k1_relat_1(A_63),k2_relat_1(A_63)) = k3_relat_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_24,plain,(
    ! [A_23] : r1_tarski(k1_xboole_0,A_23) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [A_33,C_35,B_34] :
      ( r1_tarski(k2_xboole_0(A_33,C_35),B_34)
      | ~ r1_tarski(C_35,B_34)
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_361,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | ~ r1_tarski(B_102,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3434,plain,(
    ! [A_287,B_288] :
      ( k2_xboole_0(A_287,B_288) = A_287
      | ~ r1_tarski(k2_xboole_0(A_287,B_288),A_287) ) ),
    inference(resolution,[status(thm)],[c_32,c_361])).

tff(c_3453,plain,(
    ! [B_34,C_35] :
      ( k2_xboole_0(B_34,C_35) = B_34
      | ~ r1_tarski(C_35,B_34)
      | ~ r1_tarski(B_34,B_34) ) ),
    inference(resolution,[status(thm)],[c_34,c_3434])).

tff(c_3479,plain,(
    ! [B_289,C_290] :
      ( k2_xboole_0(B_289,C_290) = B_289
      | ~ r1_tarski(C_290,B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3453])).

tff(c_4084,plain,(
    ! [A_293] : k2_xboole_0(A_293,k1_xboole_0) = A_293 ),
    inference(resolution,[status(thm)],[c_24,c_3479])).

tff(c_36,plain,(
    ! [B_37,A_36] : k2_tarski(B_37,A_36) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_208,plain,(
    ! [A_92,B_93] : k3_tarski(k2_tarski(A_92,B_93)) = k2_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_448,plain,(
    ! [A_111,B_112] : k3_tarski(k2_tarski(A_111,B_112)) = k2_xboole_0(B_112,A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_208])).

tff(c_38,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_454,plain,(
    ! [B_112,A_111] : k2_xboole_0(B_112,A_111) = k2_xboole_0(A_111,B_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_38])).

tff(c_4236,plain,(
    ! [A_293] : k2_xboole_0(k1_xboole_0,A_293) = A_293 ),
    inference(superposition,[status(thm),theory(equality)],[c_4084,c_454])).

tff(c_68,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2152,plain,(
    ! [C_217,A_218] :
      ( r2_hidden(k4_tarski(C_217,'#skF_6'(A_218,k1_relat_1(A_218),C_217)),A_218)
      | ~ r2_hidden(C_217,k1_relat_1(A_218)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    ! [A_30] : r1_xboole_0(A_30,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_117,plain,(
    ! [B_80,A_81] :
      ( r1_xboole_0(B_80,A_81)
      | ~ r1_xboole_0(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    ! [A_30] : r1_xboole_0(k1_xboole_0,A_30) ),
    inference(resolution,[status(thm)],[c_30,c_117])).

tff(c_127,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_143,plain,(
    ! [A_23] : k3_xboole_0(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_127])).

tff(c_396,plain,(
    ! [A_105,B_106,C_107] :
      ( ~ r1_xboole_0(A_105,B_106)
      | ~ r2_hidden(C_107,k3_xboole_0(A_105,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_414,plain,(
    ! [A_23,C_107] :
      ( ~ r1_xboole_0(k1_xboole_0,A_23)
      | ~ r2_hidden(C_107,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_396])).

tff(c_428,plain,(
    ! [C_107] : ~ r2_hidden(C_107,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_414])).

tff(c_2172,plain,(
    ! [C_219] : ~ r2_hidden(C_219,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2152,c_428])).

tff(c_2187,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_2172])).

tff(c_64,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_153,plain,(
    ! [A_87,B_88] : k1_setfam_1(k2_tarski(A_87,B_88)) = k3_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_223,plain,(
    ! [A_94,B_95] : k1_setfam_1(k2_tarski(A_94,B_95)) = k3_xboole_0(B_95,A_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_153])).

tff(c_42,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_246,plain,(
    ! [B_96,A_97] : k3_xboole_0(B_96,A_97) = k3_xboole_0(A_97,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_42])).

tff(c_262,plain,(
    ! [B_96] : k3_xboole_0(B_96,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_143])).

tff(c_3609,plain,(
    ! [A_23] : k2_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(resolution,[status(thm)],[c_24,c_3479])).

tff(c_773,plain,(
    ! [A_141,B_142,C_143] :
      ( r1_tarski(k4_xboole_0(A_141,B_142),C_143)
      | ~ r1_tarski(A_141,k2_xboole_0(B_142,C_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9896,plain,(
    ! [A_374,B_375,C_376] :
      ( k3_xboole_0(k4_xboole_0(A_374,B_375),C_376) = k4_xboole_0(A_374,B_375)
      | ~ r1_tarski(A_374,k2_xboole_0(B_375,C_376)) ) ),
    inference(resolution,[status(thm)],[c_773,c_22])).

tff(c_9962,plain,(
    ! [A_374,A_23] :
      ( k3_xboole_0(k4_xboole_0(A_374,A_23),k1_xboole_0) = k4_xboole_0(A_374,A_23)
      | ~ r1_tarski(A_374,A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3609,c_9896])).

tff(c_10106,plain,(
    ! [A_377,A_378] :
      ( k4_xboole_0(A_377,A_378) = k1_xboole_0
      | ~ r1_tarski(A_377,A_378) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_9962])).

tff(c_10321,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_10106])).

tff(c_40,plain,(
    ! [A_40,B_41] : k6_subset_1(A_40,B_41) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58,plain,(
    ! [A_64,B_66] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_64),k1_relat_1(B_66)),k1_relat_1(k6_subset_1(A_64,B_66)))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_69,plain,(
    ! [A_64,B_66] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_64),k1_relat_1(B_66)),k1_relat_1(k4_xboole_0(A_64,B_66)))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_58])).

tff(c_10424,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_7'),k1_relat_1('#skF_8')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10321,c_69])).

tff(c_10452,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_7'),k1_relat_1('#skF_8')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2187,c_10424])).

tff(c_8109,plain,(
    ! [C_354,B_355,A_356] :
      ( k2_xboole_0(C_354,B_355) = A_356
      | ~ r1_tarski(k2_xboole_0(C_354,B_355),A_356)
      | ~ r1_tarski(A_356,B_355) ) ),
    inference(resolution,[status(thm)],[c_16,c_361])).

tff(c_8161,plain,(
    ! [A_23,A_356] :
      ( k2_xboole_0(A_23,k1_xboole_0) = A_356
      | ~ r1_tarski(A_23,A_356)
      | ~ r1_tarski(A_356,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3609,c_8109])).

tff(c_8268,plain,(
    ! [A_356,A_23] :
      ( A_356 = A_23
      | ~ r1_tarski(A_23,A_356)
      | ~ r1_tarski(A_356,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3609,c_8161])).

tff(c_11988,plain,
    ( k4_xboole_0(k1_relat_1('#skF_7'),k1_relat_1('#skF_8')) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10452,c_8268])).

tff(c_12015,plain,(
    k4_xboole_0(k1_relat_1('#skF_7'),k1_relat_1('#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_11988])).

tff(c_1110,plain,(
    ! [A_173,B_174,C_175] :
      ( r1_tarski(A_173,k2_xboole_0(B_174,C_175))
      | ~ r1_tarski(k4_xboole_0(A_173,B_174),C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1162,plain,(
    ! [A_173,B_174,B_32] : r1_tarski(A_173,k2_xboole_0(B_174,k2_xboole_0(k4_xboole_0(A_173,B_174),B_32))) ),
    inference(resolution,[status(thm)],[c_32,c_1110])).

tff(c_12065,plain,(
    ! [B_32] : r1_tarski(k1_relat_1('#skF_7'),k2_xboole_0(k1_relat_1('#skF_8'),k2_xboole_0(k1_xboole_0,B_32))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12015,c_1162])).

tff(c_12684,plain,(
    ! [B_408] : r1_tarski(k1_relat_1('#skF_7'),k2_xboole_0(k1_relat_1('#skF_8'),B_408)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4236,c_12065])).

tff(c_12737,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),k3_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_12684])).

tff(c_12764,plain,(
    r1_tarski(k1_relat_1('#skF_7'),k3_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_12737])).

tff(c_1513,plain,(
    ! [A_189,C_190,B_191] :
      ( r1_tarski(k2_xboole_0(A_189,C_190),B_191)
      | ~ r1_tarski(C_190,B_191)
      | ~ r1_tarski(A_189,B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12584,plain,(
    ! [A_406,B_407] :
      ( r1_tarski(k3_relat_1(A_406),B_407)
      | ~ r1_tarski(k2_relat_1(A_406),B_407)
      | ~ r1_tarski(k1_relat_1(A_406),B_407)
      | ~ v1_relat_1(A_406) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1513])).

tff(c_62,plain,(
    ~ r1_tarski(k3_relat_1('#skF_7'),k3_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_12655,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),k3_relat_1('#skF_8'))
    | ~ r1_tarski(k1_relat_1('#skF_7'),k3_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12584,c_62])).

tff(c_12683,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),k3_relat_1('#skF_8'))
    | ~ r1_tarski(k1_relat_1('#skF_7'),k3_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12655])).

tff(c_13086,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),k3_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12764,c_12683])).

tff(c_13089,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),k2_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_626,c_13086])).

tff(c_13092,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_13089])).

tff(c_488,plain,(
    ! [B_116,A_117] : k2_xboole_0(B_116,A_117) = k2_xboole_0(A_117,B_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_38])).

tff(c_521,plain,(
    ! [A_117,B_116] : r1_tarski(A_117,k2_xboole_0(B_116,A_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_32])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14833,plain,(
    ! [A_432,C_433,B_434] :
      ( k2_xboole_0(A_432,C_433) = B_434
      | ~ r1_tarski(B_434,k2_xboole_0(A_432,C_433))
      | ~ r1_tarski(C_433,B_434)
      | ~ r1_tarski(A_432,B_434) ) ),
    inference(resolution,[status(thm)],[c_1513,c_10])).

tff(c_14993,plain,(
    ! [B_116,A_117] :
      ( k2_xboole_0(B_116,A_117) = A_117
      | ~ r1_tarski(A_117,A_117)
      | ~ r1_tarski(B_116,A_117) ) ),
    inference(resolution,[status(thm)],[c_521,c_14833])).

tff(c_15087,plain,(
    ! [B_435,A_436] :
      ( k2_xboole_0(B_435,A_436) = A_436
      | ~ r1_tarski(B_435,A_436) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14993])).

tff(c_15311,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_64,c_15087])).

tff(c_1735,plain,(
    ! [A_198,B_199] :
      ( k2_xboole_0(k2_relat_1(A_198),k2_relat_1(B_199)) = k2_relat_1(k2_xboole_0(A_198,B_199))
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1791,plain,(
    ! [A_198,B_199] :
      ( r1_tarski(k2_relat_1(A_198),k2_relat_1(k2_xboole_0(A_198,B_199)))
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(A_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1735,c_32])).

tff(c_15398,plain,
    ( r1_tarski(k2_relat_1('#skF_7'),k2_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_15311,c_1791])).

tff(c_15571,plain,(
    r1_tarski(k2_relat_1('#skF_7'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_15398])).

tff(c_15573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13092,c_15571])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 09:36:27 EST 2020
% 0.17/0.33  % CPUTime    : 
% 0.17/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.63/3.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.63/3.71  
% 8.63/3.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.63/3.71  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 8.63/3.71  
% 8.63/3.71  %Foreground sorts:
% 8.63/3.71  
% 8.63/3.71  
% 8.63/3.71  %Background operators:
% 8.63/3.71  
% 8.63/3.71  
% 8.63/3.71  %Foreground operators:
% 8.63/3.71  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.63/3.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.63/3.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.63/3.71  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.63/3.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.63/3.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.63/3.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.63/3.71  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 8.63/3.71  tff('#skF_7', type, '#skF_7': $i).
% 8.63/3.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.63/3.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.63/3.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.63/3.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.63/3.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.63/3.71  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.63/3.71  tff('#skF_8', type, '#skF_8': $i).
% 8.63/3.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.63/3.71  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.63/3.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.63/3.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.63/3.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.63/3.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.63/3.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.63/3.71  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.63/3.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.63/3.71  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.63/3.71  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.63/3.71  
% 8.80/3.73  tff(f_139, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 8.80/3.73  tff(f_115, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 8.80/3.73  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 8.80/3.73  tff(f_77, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.80/3.73  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.80/3.73  tff(f_95, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 8.80/3.73  tff(f_89, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.80/3.73  tff(f_97, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.80/3.73  tff(f_99, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.80/3.73  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.80/3.73  tff(f_111, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 8.80/3.73  tff(f_87, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.80/3.73  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.80/3.73  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.80/3.73  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.80/3.73  tff(f_103, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.80/3.73  tff(f_81, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.80/3.73  tff(f_101, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.80/3.73  tff(f_122, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 8.80/3.73  tff(f_85, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 8.80/3.73  tff(f_129, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 8.80/3.73  tff(c_66, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.80/3.73  tff(c_611, plain, (![A_125]: (k2_xboole_0(k1_relat_1(A_125), k2_relat_1(A_125))=k3_relat_1(A_125) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.80/3.73  tff(c_16, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, k2_xboole_0(C_14, B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.80/3.73  tff(c_626, plain, (![A_12, A_125]: (r1_tarski(A_12, k3_relat_1(A_125)) | ~r1_tarski(A_12, k2_relat_1(A_125)) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_611, c_16])).
% 8.80/3.73  tff(c_56, plain, (![A_63]: (k2_xboole_0(k1_relat_1(A_63), k2_relat_1(A_63))=k3_relat_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.80/3.73  tff(c_24, plain, (![A_23]: (r1_tarski(k1_xboole_0, A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.80/3.73  tff(c_14, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.80/3.73  tff(c_34, plain, (![A_33, C_35, B_34]: (r1_tarski(k2_xboole_0(A_33, C_35), B_34) | ~r1_tarski(C_35, B_34) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.80/3.73  tff(c_32, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.80/3.73  tff(c_361, plain, (![B_102, A_103]: (B_102=A_103 | ~r1_tarski(B_102, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.80/3.73  tff(c_3434, plain, (![A_287, B_288]: (k2_xboole_0(A_287, B_288)=A_287 | ~r1_tarski(k2_xboole_0(A_287, B_288), A_287))), inference(resolution, [status(thm)], [c_32, c_361])).
% 8.80/3.73  tff(c_3453, plain, (![B_34, C_35]: (k2_xboole_0(B_34, C_35)=B_34 | ~r1_tarski(C_35, B_34) | ~r1_tarski(B_34, B_34))), inference(resolution, [status(thm)], [c_34, c_3434])).
% 8.80/3.73  tff(c_3479, plain, (![B_289, C_290]: (k2_xboole_0(B_289, C_290)=B_289 | ~r1_tarski(C_290, B_289))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3453])).
% 8.80/3.73  tff(c_4084, plain, (![A_293]: (k2_xboole_0(A_293, k1_xboole_0)=A_293)), inference(resolution, [status(thm)], [c_24, c_3479])).
% 8.80/3.73  tff(c_36, plain, (![B_37, A_36]: (k2_tarski(B_37, A_36)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.80/3.73  tff(c_208, plain, (![A_92, B_93]: (k3_tarski(k2_tarski(A_92, B_93))=k2_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.80/3.73  tff(c_448, plain, (![A_111, B_112]: (k3_tarski(k2_tarski(A_111, B_112))=k2_xboole_0(B_112, A_111))), inference(superposition, [status(thm), theory('equality')], [c_36, c_208])).
% 8.80/3.73  tff(c_38, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.80/3.73  tff(c_454, plain, (![B_112, A_111]: (k2_xboole_0(B_112, A_111)=k2_xboole_0(A_111, B_112))), inference(superposition, [status(thm), theory('equality')], [c_448, c_38])).
% 8.80/3.73  tff(c_4236, plain, (![A_293]: (k2_xboole_0(k1_xboole_0, A_293)=A_293)), inference(superposition, [status(thm), theory('equality')], [c_4084, c_454])).
% 8.80/3.73  tff(c_68, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.80/3.73  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.80/3.73  tff(c_2152, plain, (![C_217, A_218]: (r2_hidden(k4_tarski(C_217, '#skF_6'(A_218, k1_relat_1(A_218), C_217)), A_218) | ~r2_hidden(C_217, k1_relat_1(A_218)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.80/3.73  tff(c_30, plain, (![A_30]: (r1_xboole_0(A_30, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.80/3.73  tff(c_117, plain, (![B_80, A_81]: (r1_xboole_0(B_80, A_81) | ~r1_xboole_0(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.80/3.73  tff(c_120, plain, (![A_30]: (r1_xboole_0(k1_xboole_0, A_30))), inference(resolution, [status(thm)], [c_30, c_117])).
% 8.80/3.73  tff(c_127, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.80/3.73  tff(c_143, plain, (![A_23]: (k3_xboole_0(k1_xboole_0, A_23)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_127])).
% 8.80/3.73  tff(c_396, plain, (![A_105, B_106, C_107]: (~r1_xboole_0(A_105, B_106) | ~r2_hidden(C_107, k3_xboole_0(A_105, B_106)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.80/3.73  tff(c_414, plain, (![A_23, C_107]: (~r1_xboole_0(k1_xboole_0, A_23) | ~r2_hidden(C_107, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_143, c_396])).
% 8.80/3.73  tff(c_428, plain, (![C_107]: (~r2_hidden(C_107, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_414])).
% 8.80/3.73  tff(c_2172, plain, (![C_219]: (~r2_hidden(C_219, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2152, c_428])).
% 8.80/3.73  tff(c_2187, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_2172])).
% 8.80/3.73  tff(c_64, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.80/3.73  tff(c_153, plain, (![A_87, B_88]: (k1_setfam_1(k2_tarski(A_87, B_88))=k3_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.80/3.73  tff(c_223, plain, (![A_94, B_95]: (k1_setfam_1(k2_tarski(A_94, B_95))=k3_xboole_0(B_95, A_94))), inference(superposition, [status(thm), theory('equality')], [c_36, c_153])).
% 8.80/3.73  tff(c_42, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.80/3.73  tff(c_246, plain, (![B_96, A_97]: (k3_xboole_0(B_96, A_97)=k3_xboole_0(A_97, B_96))), inference(superposition, [status(thm), theory('equality')], [c_223, c_42])).
% 8.80/3.73  tff(c_262, plain, (![B_96]: (k3_xboole_0(B_96, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_246, c_143])).
% 8.80/3.73  tff(c_3609, plain, (![A_23]: (k2_xboole_0(A_23, k1_xboole_0)=A_23)), inference(resolution, [status(thm)], [c_24, c_3479])).
% 8.80/3.73  tff(c_773, plain, (![A_141, B_142, C_143]: (r1_tarski(k4_xboole_0(A_141, B_142), C_143) | ~r1_tarski(A_141, k2_xboole_0(B_142, C_143)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.80/3.73  tff(c_22, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.80/3.73  tff(c_9896, plain, (![A_374, B_375, C_376]: (k3_xboole_0(k4_xboole_0(A_374, B_375), C_376)=k4_xboole_0(A_374, B_375) | ~r1_tarski(A_374, k2_xboole_0(B_375, C_376)))), inference(resolution, [status(thm)], [c_773, c_22])).
% 8.80/3.73  tff(c_9962, plain, (![A_374, A_23]: (k3_xboole_0(k4_xboole_0(A_374, A_23), k1_xboole_0)=k4_xboole_0(A_374, A_23) | ~r1_tarski(A_374, A_23))), inference(superposition, [status(thm), theory('equality')], [c_3609, c_9896])).
% 8.80/3.73  tff(c_10106, plain, (![A_377, A_378]: (k4_xboole_0(A_377, A_378)=k1_xboole_0 | ~r1_tarski(A_377, A_378))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_9962])).
% 8.80/3.73  tff(c_10321, plain, (k4_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_10106])).
% 8.80/3.73  tff(c_40, plain, (![A_40, B_41]: (k6_subset_1(A_40, B_41)=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.80/3.73  tff(c_58, plain, (![A_64, B_66]: (r1_tarski(k6_subset_1(k1_relat_1(A_64), k1_relat_1(B_66)), k1_relat_1(k6_subset_1(A_64, B_66))) | ~v1_relat_1(B_66) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.80/3.73  tff(c_69, plain, (![A_64, B_66]: (r1_tarski(k4_xboole_0(k1_relat_1(A_64), k1_relat_1(B_66)), k1_relat_1(k4_xboole_0(A_64, B_66))) | ~v1_relat_1(B_66) | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_58])).
% 8.80/3.73  tff(c_10424, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_7'), k1_relat_1('#skF_8')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10321, c_69])).
% 8.80/3.73  tff(c_10452, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_7'), k1_relat_1('#skF_8')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2187, c_10424])).
% 8.80/3.73  tff(c_8109, plain, (![C_354, B_355, A_356]: (k2_xboole_0(C_354, B_355)=A_356 | ~r1_tarski(k2_xboole_0(C_354, B_355), A_356) | ~r1_tarski(A_356, B_355))), inference(resolution, [status(thm)], [c_16, c_361])).
% 8.80/3.73  tff(c_8161, plain, (![A_23, A_356]: (k2_xboole_0(A_23, k1_xboole_0)=A_356 | ~r1_tarski(A_23, A_356) | ~r1_tarski(A_356, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3609, c_8109])).
% 8.80/3.73  tff(c_8268, plain, (![A_356, A_23]: (A_356=A_23 | ~r1_tarski(A_23, A_356) | ~r1_tarski(A_356, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3609, c_8161])).
% 8.80/3.73  tff(c_11988, plain, (k4_xboole_0(k1_relat_1('#skF_7'), k1_relat_1('#skF_8'))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_10452, c_8268])).
% 8.80/3.73  tff(c_12015, plain, (k4_xboole_0(k1_relat_1('#skF_7'), k1_relat_1('#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_11988])).
% 8.80/3.73  tff(c_1110, plain, (![A_173, B_174, C_175]: (r1_tarski(A_173, k2_xboole_0(B_174, C_175)) | ~r1_tarski(k4_xboole_0(A_173, B_174), C_175))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.80/3.73  tff(c_1162, plain, (![A_173, B_174, B_32]: (r1_tarski(A_173, k2_xboole_0(B_174, k2_xboole_0(k4_xboole_0(A_173, B_174), B_32))))), inference(resolution, [status(thm)], [c_32, c_1110])).
% 8.80/3.73  tff(c_12065, plain, (![B_32]: (r1_tarski(k1_relat_1('#skF_7'), k2_xboole_0(k1_relat_1('#skF_8'), k2_xboole_0(k1_xboole_0, B_32))))), inference(superposition, [status(thm), theory('equality')], [c_12015, c_1162])).
% 8.80/3.73  tff(c_12684, plain, (![B_408]: (r1_tarski(k1_relat_1('#skF_7'), k2_xboole_0(k1_relat_1('#skF_8'), B_408)))), inference(demodulation, [status(thm), theory('equality')], [c_4236, c_12065])).
% 8.80/3.73  tff(c_12737, plain, (r1_tarski(k1_relat_1('#skF_7'), k3_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_56, c_12684])).
% 8.80/3.73  tff(c_12764, plain, (r1_tarski(k1_relat_1('#skF_7'), k3_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_12737])).
% 8.80/3.73  tff(c_1513, plain, (![A_189, C_190, B_191]: (r1_tarski(k2_xboole_0(A_189, C_190), B_191) | ~r1_tarski(C_190, B_191) | ~r1_tarski(A_189, B_191))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.80/3.73  tff(c_12584, plain, (![A_406, B_407]: (r1_tarski(k3_relat_1(A_406), B_407) | ~r1_tarski(k2_relat_1(A_406), B_407) | ~r1_tarski(k1_relat_1(A_406), B_407) | ~v1_relat_1(A_406))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1513])).
% 8.80/3.73  tff(c_62, plain, (~r1_tarski(k3_relat_1('#skF_7'), k3_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.80/3.73  tff(c_12655, plain, (~r1_tarski(k2_relat_1('#skF_7'), k3_relat_1('#skF_8')) | ~r1_tarski(k1_relat_1('#skF_7'), k3_relat_1('#skF_8')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_12584, c_62])).
% 8.80/3.73  tff(c_12683, plain, (~r1_tarski(k2_relat_1('#skF_7'), k3_relat_1('#skF_8')) | ~r1_tarski(k1_relat_1('#skF_7'), k3_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_12655])).
% 8.80/3.73  tff(c_13086, plain, (~r1_tarski(k2_relat_1('#skF_7'), k3_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_12764, c_12683])).
% 8.80/3.73  tff(c_13089, plain, (~r1_tarski(k2_relat_1('#skF_7'), k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_626, c_13086])).
% 8.80/3.73  tff(c_13092, plain, (~r1_tarski(k2_relat_1('#skF_7'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_13089])).
% 8.80/3.73  tff(c_488, plain, (![B_116, A_117]: (k2_xboole_0(B_116, A_117)=k2_xboole_0(A_117, B_116))), inference(superposition, [status(thm), theory('equality')], [c_448, c_38])).
% 8.80/3.73  tff(c_521, plain, (![A_117, B_116]: (r1_tarski(A_117, k2_xboole_0(B_116, A_117)))), inference(superposition, [status(thm), theory('equality')], [c_488, c_32])).
% 8.80/3.73  tff(c_10, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.80/3.73  tff(c_14833, plain, (![A_432, C_433, B_434]: (k2_xboole_0(A_432, C_433)=B_434 | ~r1_tarski(B_434, k2_xboole_0(A_432, C_433)) | ~r1_tarski(C_433, B_434) | ~r1_tarski(A_432, B_434))), inference(resolution, [status(thm)], [c_1513, c_10])).
% 8.80/3.73  tff(c_14993, plain, (![B_116, A_117]: (k2_xboole_0(B_116, A_117)=A_117 | ~r1_tarski(A_117, A_117) | ~r1_tarski(B_116, A_117))), inference(resolution, [status(thm)], [c_521, c_14833])).
% 8.80/3.73  tff(c_15087, plain, (![B_435, A_436]: (k2_xboole_0(B_435, A_436)=A_436 | ~r1_tarski(B_435, A_436))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14993])).
% 8.80/3.73  tff(c_15311, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_64, c_15087])).
% 8.80/3.73  tff(c_1735, plain, (![A_198, B_199]: (k2_xboole_0(k2_relat_1(A_198), k2_relat_1(B_199))=k2_relat_1(k2_xboole_0(A_198, B_199)) | ~v1_relat_1(B_199) | ~v1_relat_1(A_198))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.80/3.73  tff(c_1791, plain, (![A_198, B_199]: (r1_tarski(k2_relat_1(A_198), k2_relat_1(k2_xboole_0(A_198, B_199))) | ~v1_relat_1(B_199) | ~v1_relat_1(A_198))), inference(superposition, [status(thm), theory('equality')], [c_1735, c_32])).
% 8.80/3.73  tff(c_15398, plain, (r1_tarski(k2_relat_1('#skF_7'), k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_15311, c_1791])).
% 8.80/3.73  tff(c_15571, plain, (r1_tarski(k2_relat_1('#skF_7'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_15398])).
% 8.80/3.73  tff(c_15573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13092, c_15571])).
% 8.80/3.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.80/3.73  
% 8.80/3.73  Inference rules
% 8.80/3.73  ----------------------
% 8.80/3.73  #Ref     : 0
% 8.80/3.73  #Sup     : 3871
% 8.80/3.73  #Fact    : 0
% 8.80/3.73  #Define  : 0
% 8.80/3.73  #Split   : 9
% 8.80/3.73  #Chain   : 0
% 8.80/3.73  #Close   : 0
% 8.80/3.73  
% 8.80/3.73  Ordering : KBO
% 8.80/3.73  
% 8.80/3.73  Simplification rules
% 8.80/3.73  ----------------------
% 8.80/3.73  #Subsume      : 696
% 8.80/3.73  #Demod        : 1977
% 8.80/3.73  #Tautology    : 1472
% 8.80/3.73  #SimpNegUnit  : 13
% 8.80/3.73  #BackRed      : 25
% 8.80/3.73  
% 8.80/3.73  #Partial instantiations: 0
% 8.80/3.73  #Strategies tried      : 1
% 8.80/3.73  
% 8.80/3.73  Timing (in seconds)
% 8.80/3.73  ----------------------
% 8.80/3.74  Preprocessing        : 0.55
% 8.80/3.74  Parsing              : 0.28
% 8.80/3.74  CNF conversion       : 0.04
% 8.80/3.74  Main loop            : 2.31
% 8.80/3.74  Inferencing          : 0.49
% 8.80/3.74  Reduction            : 1.03
% 8.80/3.74  Demodulation         : 0.84
% 8.80/3.74  BG Simplification    : 0.07
% 8.80/3.74  Subsumption          : 0.57
% 8.80/3.74  Abstraction          : 0.09
% 8.80/3.74  MUC search           : 0.00
% 8.80/3.74  Cooper               : 0.00
% 8.80/3.74  Total                : 2.90
% 8.80/3.74  Index Insertion      : 0.00
% 8.80/3.74  Index Deletion       : 0.00
% 8.80/3.74  Index Matching       : 0.00
% 8.80/3.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
