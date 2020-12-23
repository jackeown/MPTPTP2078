%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:23 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 335 expanded)
%              Number of leaves         :   34 ( 125 expanded)
%              Depth                    :   12
%              Number of atoms          :  185 ( 717 expanded)
%              Number of equality atoms :   28 ( 104 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1636,plain,(
    ! [C_284,A_285,B_286] :
      ( v1_relat_1(C_284)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1649,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1636])).

tff(c_121,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_134,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_121])).

tff(c_155,plain,(
    ! [C_68,A_69,B_70] :
      ( v4_relat_1(C_68,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_168,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_155])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1('#skF_1'(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_13] :
      ( v1_xboole_0(k2_relat_1(A_13))
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_43,plain,(
    ! [A_41] :
      ( v1_xboole_0(k2_relat_1(A_41))
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_42] :
      ( k2_relat_1(A_42) = k1_xboole_0
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_53,plain,(
    ! [A_43] :
      ( k2_relat_1(k2_relat_1(A_43)) = k1_xboole_0
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_62,plain,(
    ! [A_43] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_43))
      | ~ v1_xboole_0(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_18])).

tff(c_96,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(k2_relat_1(A_53))
      | ~ v1_xboole_0(A_53) ) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_103,plain,(
    ! [A_13] : ~ v1_xboole_0(A_13) ),
    inference(resolution,[status(thm)],[c_18,c_96])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_104,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_6])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_208,plain,(
    ! [A_81,C_82,B_83] :
      ( m1_subset_1(A_81,C_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(C_82))
      | ~ r2_hidden(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_410,plain,(
    ! [A_105,B_106,A_107] :
      ( m1_subset_1(A_105,B_106)
      | ~ r2_hidden(A_105,A_107)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(resolution,[status(thm)],[c_10,c_208])).

tff(c_416,plain,(
    ! [A_110,B_111,B_112] :
      ( m1_subset_1(A_110,B_111)
      | ~ r1_tarski(B_112,B_111)
      | ~ m1_subset_1(A_110,B_112) ) ),
    inference(resolution,[status(thm)],[c_104,c_410])).

tff(c_975,plain,(
    ! [A_174,A_175,B_176] :
      ( m1_subset_1(A_174,A_175)
      | ~ m1_subset_1(A_174,k1_relat_1(B_176))
      | ~ v4_relat_1(B_176,A_175)
      | ~ v1_relat_1(B_176) ) ),
    inference(resolution,[status(thm)],[c_16,c_416])).

tff(c_1005,plain,(
    ! [B_177,A_178] :
      ( m1_subset_1('#skF_1'(k1_relat_1(B_177)),A_178)
      | ~ v4_relat_1(B_177,A_178)
      | ~ v1_relat_1(B_177) ) ),
    inference(resolution,[status(thm)],[c_4,c_975])).

tff(c_221,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_234,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_221])).

tff(c_89,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | v1_xboole_0(B_52)
      | ~ m1_subset_1(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [D_38] :
      ( ~ r2_hidden(D_38,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_38,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_94,plain,(
    ! [A_51] :
      ( ~ m1_subset_1(A_51,'#skF_3')
      | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(A_51,k1_relset_1('#skF_3','#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_89,c_32])).

tff(c_109,plain,(
    ! [A_55] :
      ( ~ m1_subset_1(A_55,'#skF_3')
      | ~ m1_subset_1(A_55,k1_relset_1('#skF_3','#skF_2','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_94])).

tff(c_114,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_236,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_114])).

tff(c_1027,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1005,c_236])).

tff(c_1059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_168,c_1027])).

tff(c_1060,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1193,plain,(
    ! [A_209,B_210,C_211] :
      ( k2_relset_1(A_209,B_210,C_211) = k2_relat_1(C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1206,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1193])).

tff(c_34,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1208,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1206,c_34])).

tff(c_73,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_1180,plain,(
    ! [A_203,C_204,B_205] :
      ( m1_subset_1(A_203,C_204)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(C_204))
      | ~ r2_hidden(A_203,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1236,plain,(
    ! [A_217,B_218,A_219] :
      ( m1_subset_1(A_217,B_218)
      | ~ r2_hidden(A_217,A_219)
      | ~ r1_tarski(A_219,B_218) ) ),
    inference(resolution,[status(thm)],[c_10,c_1180])).

tff(c_1337,plain,(
    ! [A_243,B_244,B_245] :
      ( m1_subset_1(A_243,B_244)
      | ~ r1_tarski(B_245,B_244)
      | v1_xboole_0(B_245)
      | ~ m1_subset_1(A_243,B_245) ) ),
    inference(resolution,[status(thm)],[c_6,c_1236])).

tff(c_1346,plain,(
    ! [A_243] :
      ( m1_subset_1(A_243,k2_zfmisc_1('#skF_3','#skF_2'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_243,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_81,c_1337])).

tff(c_1347,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1346])).

tff(c_47,plain,(
    ! [A_41] :
      ( k2_relat_1(A_41) = k1_xboole_0
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_1350,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1347,c_47])).

tff(c_1357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1208,c_1350])).

tff(c_1359,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1346])).

tff(c_1085,plain,(
    ! [C_179,A_180,B_181] :
      ( v1_relat_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1098,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1085])).

tff(c_1114,plain,(
    ! [C_187,A_188,B_189] :
      ( v4_relat_1(C_187,A_188)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1127,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1114])).

tff(c_1542,plain,(
    ! [A_279,A_280,B_281] :
      ( m1_subset_1(A_279,A_280)
      | v1_xboole_0(k1_relat_1(B_281))
      | ~ m1_subset_1(A_279,k1_relat_1(B_281))
      | ~ v4_relat_1(B_281,A_280)
      | ~ v1_relat_1(B_281) ) ),
    inference(resolution,[status(thm)],[c_16,c_1337])).

tff(c_1551,plain,(
    ! [B_282,A_283] :
      ( m1_subset_1('#skF_1'(k1_relat_1(B_282)),A_283)
      | v1_xboole_0(k1_relat_1(B_282))
      | ~ v4_relat_1(B_282,A_283)
      | ~ v1_relat_1(B_282) ) ),
    inference(resolution,[status(thm)],[c_4,c_1542])).

tff(c_1240,plain,(
    ! [A_220,B_221,C_222] :
      ( k1_relset_1(A_220,B_221,C_222) = k1_relat_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1253,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1240])).

tff(c_1142,plain,(
    ! [A_195] :
      ( ~ m1_subset_1(A_195,'#skF_3')
      | ~ m1_subset_1(A_195,k1_relset_1('#skF_3','#skF_2','#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_1147,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_1142])).

tff(c_1255,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1253,c_1147])).

tff(c_1565,plain,
    ( v1_xboole_0(k1_relat_1('#skF_4'))
    | ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1551,c_1255])).

tff(c_1598,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_1127,c_1565])).

tff(c_20,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(k1_relat_1(A_14))
      | ~ v1_relat_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1608,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1598,c_20])).

tff(c_1617,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_1608])).

tff(c_1619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1359,c_1617])).

tff(c_1620,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_1628,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1620,c_2])).

tff(c_1763,plain,(
    ! [A_317,B_318,C_319] :
      ( k1_relset_1(A_317,B_318,C_319) = k1_relat_1(C_319)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_317,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1770,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1763])).

tff(c_1777,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1628,c_1770])).

tff(c_1788,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1777,c_20])).

tff(c_1796,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1060,c_1788])).

tff(c_1805,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1796,c_2])).

tff(c_1813,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1805,c_34])).

tff(c_1067,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1060,c_47])).

tff(c_1809,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1805,c_1805,c_1067])).

tff(c_1863,plain,(
    ! [A_321,B_322,C_323] :
      ( k2_relset_1(A_321,B_322,C_323) = k2_relat_1(C_323)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1870,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1863])).

tff(c_1877,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1809,c_1870])).

tff(c_1879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1813,c_1877])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:06:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.62  
% 3.71/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.62  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.71/1.62  
% 3.71/1.62  %Foreground sorts:
% 3.71/1.62  
% 3.71/1.62  
% 3.71/1.62  %Background operators:
% 3.71/1.62  
% 3.71/1.62  
% 3.71/1.62  %Foreground operators:
% 3.71/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.71/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.71/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.71/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.71/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.71/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.71/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.71/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.71/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.71/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.71/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.71/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.71/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.71/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.71/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.71/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.71/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.71/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.71/1.62  
% 3.71/1.64  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 3.71/1.64  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.71/1.64  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.71/1.64  tff(f_32, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.71/1.64  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.71/1.64  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 3.71/1.64  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.71/1.64  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.71/1.64  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.71/1.64  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.71/1.64  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.71/1.64  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.71/1.64  tff(f_66, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.71/1.64  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.71/1.64  tff(c_1636, plain, (![C_284, A_285, B_286]: (v1_relat_1(C_284) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.64  tff(c_1649, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1636])).
% 3.71/1.64  tff(c_121, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.64  tff(c_134, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_121])).
% 3.71/1.64  tff(c_155, plain, (![C_68, A_69, B_70]: (v4_relat_1(C_68, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.71/1.64  tff(c_168, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_155])).
% 3.71/1.64  tff(c_4, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.71/1.64  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.71/1.64  tff(c_18, plain, (![A_13]: (v1_xboole_0(k2_relat_1(A_13)) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.71/1.64  tff(c_43, plain, (![A_41]: (v1_xboole_0(k2_relat_1(A_41)) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.71/1.64  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.71/1.64  tff(c_48, plain, (![A_42]: (k2_relat_1(A_42)=k1_xboole_0 | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_43, c_2])).
% 3.71/1.64  tff(c_53, plain, (![A_43]: (k2_relat_1(k2_relat_1(A_43))=k1_xboole_0 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_18, c_48])).
% 3.71/1.64  tff(c_62, plain, (![A_43]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_43)) | ~v1_xboole_0(A_43))), inference(superposition, [status(thm), theory('equality')], [c_53, c_18])).
% 3.71/1.64  tff(c_96, plain, (![A_53]: (~v1_xboole_0(k2_relat_1(A_53)) | ~v1_xboole_0(A_53))), inference(splitLeft, [status(thm)], [c_62])).
% 3.71/1.64  tff(c_103, plain, (![A_13]: (~v1_xboole_0(A_13))), inference(resolution, [status(thm)], [c_18, c_96])).
% 3.71/1.64  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.71/1.64  tff(c_104, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | ~m1_subset_1(A_4, B_5))), inference(negUnitSimplification, [status(thm)], [c_103, c_6])).
% 3.71/1.64  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.71/1.64  tff(c_208, plain, (![A_81, C_82, B_83]: (m1_subset_1(A_81, C_82) | ~m1_subset_1(B_83, k1_zfmisc_1(C_82)) | ~r2_hidden(A_81, B_83))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.71/1.64  tff(c_410, plain, (![A_105, B_106, A_107]: (m1_subset_1(A_105, B_106) | ~r2_hidden(A_105, A_107) | ~r1_tarski(A_107, B_106))), inference(resolution, [status(thm)], [c_10, c_208])).
% 3.71/1.64  tff(c_416, plain, (![A_110, B_111, B_112]: (m1_subset_1(A_110, B_111) | ~r1_tarski(B_112, B_111) | ~m1_subset_1(A_110, B_112))), inference(resolution, [status(thm)], [c_104, c_410])).
% 3.71/1.64  tff(c_975, plain, (![A_174, A_175, B_176]: (m1_subset_1(A_174, A_175) | ~m1_subset_1(A_174, k1_relat_1(B_176)) | ~v4_relat_1(B_176, A_175) | ~v1_relat_1(B_176))), inference(resolution, [status(thm)], [c_16, c_416])).
% 3.71/1.64  tff(c_1005, plain, (![B_177, A_178]: (m1_subset_1('#skF_1'(k1_relat_1(B_177)), A_178) | ~v4_relat_1(B_177, A_178) | ~v1_relat_1(B_177))), inference(resolution, [status(thm)], [c_4, c_975])).
% 3.71/1.64  tff(c_221, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.71/1.64  tff(c_234, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_221])).
% 3.71/1.64  tff(c_89, plain, (![A_51, B_52]: (r2_hidden(A_51, B_52) | v1_xboole_0(B_52) | ~m1_subset_1(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.71/1.64  tff(c_32, plain, (![D_38]: (~r2_hidden(D_38, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_38, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.71/1.64  tff(c_94, plain, (![A_51]: (~m1_subset_1(A_51, '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(A_51, k1_relset_1('#skF_3', '#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_89, c_32])).
% 3.71/1.64  tff(c_109, plain, (![A_55]: (~m1_subset_1(A_55, '#skF_3') | ~m1_subset_1(A_55, k1_relset_1('#skF_3', '#skF_2', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_103, c_94])).
% 3.71/1.64  tff(c_114, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_4, c_109])).
% 3.71/1.64  tff(c_236, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_114])).
% 3.71/1.64  tff(c_1027, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1005, c_236])).
% 3.71/1.64  tff(c_1059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_168, c_1027])).
% 3.71/1.64  tff(c_1060, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_62])).
% 3.71/1.64  tff(c_1193, plain, (![A_209, B_210, C_211]: (k2_relset_1(A_209, B_210, C_211)=k2_relat_1(C_211) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.71/1.64  tff(c_1206, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1193])).
% 3.71/1.64  tff(c_34, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.71/1.64  tff(c_1208, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1206, c_34])).
% 3.71/1.64  tff(c_73, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.71/1.64  tff(c_81, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_73])).
% 3.71/1.64  tff(c_1180, plain, (![A_203, C_204, B_205]: (m1_subset_1(A_203, C_204) | ~m1_subset_1(B_205, k1_zfmisc_1(C_204)) | ~r2_hidden(A_203, B_205))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.71/1.64  tff(c_1236, plain, (![A_217, B_218, A_219]: (m1_subset_1(A_217, B_218) | ~r2_hidden(A_217, A_219) | ~r1_tarski(A_219, B_218))), inference(resolution, [status(thm)], [c_10, c_1180])).
% 3.71/1.64  tff(c_1337, plain, (![A_243, B_244, B_245]: (m1_subset_1(A_243, B_244) | ~r1_tarski(B_245, B_244) | v1_xboole_0(B_245) | ~m1_subset_1(A_243, B_245))), inference(resolution, [status(thm)], [c_6, c_1236])).
% 3.71/1.64  tff(c_1346, plain, (![A_243]: (m1_subset_1(A_243, k2_zfmisc_1('#skF_3', '#skF_2')) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_243, '#skF_4'))), inference(resolution, [status(thm)], [c_81, c_1337])).
% 3.71/1.64  tff(c_1347, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1346])).
% 3.71/1.64  tff(c_47, plain, (![A_41]: (k2_relat_1(A_41)=k1_xboole_0 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_43, c_2])).
% 3.71/1.64  tff(c_1350, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1347, c_47])).
% 3.71/1.64  tff(c_1357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1208, c_1350])).
% 3.71/1.64  tff(c_1359, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1346])).
% 3.71/1.64  tff(c_1085, plain, (![C_179, A_180, B_181]: (v1_relat_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.64  tff(c_1098, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1085])).
% 3.71/1.64  tff(c_1114, plain, (![C_187, A_188, B_189]: (v4_relat_1(C_187, A_188) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.71/1.64  tff(c_1127, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_1114])).
% 3.71/1.64  tff(c_1542, plain, (![A_279, A_280, B_281]: (m1_subset_1(A_279, A_280) | v1_xboole_0(k1_relat_1(B_281)) | ~m1_subset_1(A_279, k1_relat_1(B_281)) | ~v4_relat_1(B_281, A_280) | ~v1_relat_1(B_281))), inference(resolution, [status(thm)], [c_16, c_1337])).
% 3.71/1.64  tff(c_1551, plain, (![B_282, A_283]: (m1_subset_1('#skF_1'(k1_relat_1(B_282)), A_283) | v1_xboole_0(k1_relat_1(B_282)) | ~v4_relat_1(B_282, A_283) | ~v1_relat_1(B_282))), inference(resolution, [status(thm)], [c_4, c_1542])).
% 3.71/1.64  tff(c_1240, plain, (![A_220, B_221, C_222]: (k1_relset_1(A_220, B_221, C_222)=k1_relat_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.71/1.64  tff(c_1253, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1240])).
% 3.71/1.64  tff(c_1142, plain, (![A_195]: (~m1_subset_1(A_195, '#skF_3') | ~m1_subset_1(A_195, k1_relset_1('#skF_3', '#skF_2', '#skF_4')))), inference(splitLeft, [status(thm)], [c_94])).
% 3.71/1.64  tff(c_1147, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_4, c_1142])).
% 3.71/1.64  tff(c_1255, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1253, c_1147])).
% 3.71/1.64  tff(c_1565, plain, (v1_xboole_0(k1_relat_1('#skF_4')) | ~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1551, c_1255])).
% 3.71/1.64  tff(c_1598, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_1127, c_1565])).
% 3.71/1.64  tff(c_20, plain, (![A_14]: (~v1_xboole_0(k1_relat_1(A_14)) | ~v1_relat_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.71/1.64  tff(c_1608, plain, (~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1598, c_20])).
% 3.71/1.64  tff(c_1617, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_1608])).
% 3.71/1.64  tff(c_1619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1359, c_1617])).
% 3.71/1.64  tff(c_1620, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_94])).
% 3.71/1.64  tff(c_1628, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1620, c_2])).
% 3.71/1.64  tff(c_1763, plain, (![A_317, B_318, C_319]: (k1_relset_1(A_317, B_318, C_319)=k1_relat_1(C_319) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_317, B_318))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.71/1.64  tff(c_1770, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1763])).
% 3.71/1.64  tff(c_1777, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1628, c_1770])).
% 3.71/1.64  tff(c_1788, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1777, c_20])).
% 3.71/1.64  tff(c_1796, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_1060, c_1788])).
% 3.71/1.64  tff(c_1805, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1796, c_2])).
% 3.71/1.64  tff(c_1813, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1805, c_34])).
% 3.71/1.64  tff(c_1067, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1060, c_47])).
% 3.71/1.64  tff(c_1809, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1805, c_1805, c_1067])).
% 3.71/1.64  tff(c_1863, plain, (![A_321, B_322, C_323]: (k2_relset_1(A_321, B_322, C_323)=k2_relat_1(C_323) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.71/1.64  tff(c_1870, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1863])).
% 3.71/1.64  tff(c_1877, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1809, c_1870])).
% 3.71/1.64  tff(c_1879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1813, c_1877])).
% 3.71/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.64  
% 3.71/1.64  Inference rules
% 3.71/1.64  ----------------------
% 3.71/1.64  #Ref     : 0
% 3.71/1.64  #Sup     : 356
% 3.71/1.64  #Fact    : 0
% 3.71/1.64  #Define  : 0
% 3.71/1.64  #Split   : 5
% 3.71/1.64  #Chain   : 0
% 3.71/1.64  #Close   : 0
% 3.71/1.64  
% 3.71/1.64  Ordering : KBO
% 3.71/1.64  
% 3.71/1.64  Simplification rules
% 3.71/1.64  ----------------------
% 3.71/1.64  #Subsume      : 19
% 3.71/1.64  #Demod        : 117
% 3.71/1.64  #Tautology    : 85
% 3.71/1.64  #SimpNegUnit  : 7
% 3.71/1.64  #BackRed      : 20
% 3.71/1.64  
% 3.71/1.64  #Partial instantiations: 0
% 3.71/1.64  #Strategies tried      : 1
% 3.71/1.64  
% 3.71/1.64  Timing (in seconds)
% 3.71/1.64  ----------------------
% 3.71/1.64  Preprocessing        : 0.32
% 3.71/1.64  Parsing              : 0.17
% 3.71/1.64  CNF conversion       : 0.02
% 3.71/1.64  Main loop            : 0.52
% 3.71/1.64  Inferencing          : 0.20
% 3.71/1.64  Reduction            : 0.16
% 3.71/1.64  Demodulation         : 0.11
% 3.71/1.64  BG Simplification    : 0.03
% 3.71/1.64  Subsumption          : 0.08
% 3.71/1.64  Abstraction          : 0.03
% 3.71/1.64  MUC search           : 0.00
% 3.71/1.64  Cooper               : 0.00
% 3.71/1.64  Total                : 0.88
% 3.71/1.64  Index Insertion      : 0.00
% 3.71/1.64  Index Deletion       : 0.00
% 3.71/1.64  Index Matching       : 0.00
% 3.71/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
