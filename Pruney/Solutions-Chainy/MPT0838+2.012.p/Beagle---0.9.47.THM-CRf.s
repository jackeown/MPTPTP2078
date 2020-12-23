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
% DateTime   : Thu Dec  3 10:08:11 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 240 expanded)
%              Number of leaves         :   34 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  182 ( 512 expanded)
%              Number of equality atoms :   25 (  61 expanded)
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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1774,plain,(
    ! [A_319,B_320,C_321] :
      ( k1_relset_1(A_319,B_320,C_321) = k1_relat_1(C_321)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_319,B_320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1787,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1774])).

tff(c_34,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1789,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_34])).

tff(c_1642,plain,(
    ! [C_284,A_285,B_286] :
      ( v1_relat_1(C_284)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1655,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1642])).

tff(c_121,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_134,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_121])).

tff(c_193,plain,(
    ! [C_78,B_79,A_80] :
      ( v5_relat_1(C_78,B_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_206,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_193])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1('#skF_1'(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_13] :
      ( v1_xboole_0(k1_relat_1(A_13))
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_43,plain,(
    ! [A_41] :
      ( v1_xboole_0(k1_relat_1(A_41))
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_42] :
      ( k1_relat_1(A_42) = k1_xboole_0
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_53,plain,(
    ! [A_43] :
      ( k1_relat_1(k1_relat_1(A_43)) = k1_xboole_0
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_62,plain,(
    ! [A_43] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_43))
      | ~ v1_xboole_0(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_18])).

tff(c_96,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(k1_relat_1(A_53))
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

tff(c_980,plain,(
    ! [A_174,A_175,B_176] :
      ( m1_subset_1(A_174,A_175)
      | ~ m1_subset_1(A_174,k2_relat_1(B_176))
      | ~ v5_relat_1(B_176,A_175)
      | ~ v1_relat_1(B_176) ) ),
    inference(resolution,[status(thm)],[c_16,c_416])).

tff(c_1010,plain,(
    ! [B_177,A_178] :
      ( m1_subset_1('#skF_1'(k2_relat_1(B_177)),A_178)
      | ~ v5_relat_1(B_177,A_178)
      | ~ v1_relat_1(B_177) ) ),
    inference(resolution,[status(thm)],[c_4,c_980])).

tff(c_270,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_relset_1(A_97,B_98,C_99) = k2_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_283,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_270])).

tff(c_89,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | v1_xboole_0(B_52)
      | ~ m1_subset_1(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [D_38] :
      ( ~ r2_hidden(D_38,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_38,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_94,plain,(
    ! [A_51] :
      ( ~ m1_subset_1(A_51,'#skF_3')
      | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(A_51,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_89,c_32])).

tff(c_109,plain,(
    ! [A_55] :
      ( ~ m1_subset_1(A_55,'#skF_3')
      | ~ m1_subset_1(A_55,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_94])).

tff(c_114,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_285,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_114])).

tff(c_1024,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1010,c_285])).

tff(c_1062,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_206,c_1024])).

tff(c_1063,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1236,plain,(
    ! [A_216,B_217,C_218] :
      ( k1_relset_1(A_216,B_217,C_218) = k1_relat_1(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1249,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1236])).

tff(c_1251,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_34])).

tff(c_73,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_1183,plain,(
    ! [A_203,C_204,B_205] :
      ( m1_subset_1(A_203,C_204)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(C_204))
      | ~ r2_hidden(A_203,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1273,plain,(
    ! [A_222,B_223,A_224] :
      ( m1_subset_1(A_222,B_223)
      | ~ r2_hidden(A_222,A_224)
      | ~ r1_tarski(A_224,B_223) ) ),
    inference(resolution,[status(thm)],[c_10,c_1183])).

tff(c_1343,plain,(
    ! [A_248,B_249,B_250] :
      ( m1_subset_1(A_248,B_249)
      | ~ r1_tarski(B_250,B_249)
      | v1_xboole_0(B_250)
      | ~ m1_subset_1(A_248,B_250) ) ),
    inference(resolution,[status(thm)],[c_6,c_1273])).

tff(c_1352,plain,(
    ! [A_248] :
      ( m1_subset_1(A_248,k2_zfmisc_1('#skF_2','#skF_3'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_248,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_81,c_1343])).

tff(c_1374,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1352])).

tff(c_47,plain,(
    ! [A_41] :
      ( k1_relat_1(A_41) = k1_xboole_0
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_1377,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1374,c_47])).

tff(c_1384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1251,c_1377])).

tff(c_1386,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1352])).

tff(c_1088,plain,(
    ! [C_179,A_180,B_181] :
      ( v1_relat_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1101,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1088])).

tff(c_1168,plain,(
    ! [C_200,B_201,A_202] :
      ( v5_relat_1(C_200,B_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1181,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1168])).

tff(c_1547,plain,(
    ! [A_279,A_280,B_281] :
      ( m1_subset_1(A_279,A_280)
      | v1_xboole_0(k2_relat_1(B_281))
      | ~ m1_subset_1(A_279,k2_relat_1(B_281))
      | ~ v5_relat_1(B_281,A_280)
      | ~ v1_relat_1(B_281) ) ),
    inference(resolution,[status(thm)],[c_16,c_1343])).

tff(c_1556,plain,(
    ! [B_282,A_283] :
      ( m1_subset_1('#skF_1'(k2_relat_1(B_282)),A_283)
      | v1_xboole_0(k2_relat_1(B_282))
      | ~ v5_relat_1(B_282,A_283)
      | ~ v1_relat_1(B_282) ) ),
    inference(resolution,[status(thm)],[c_4,c_1547])).

tff(c_1196,plain,(
    ! [A_209,B_210,C_211] :
      ( k2_relset_1(A_209,B_210,C_211) = k2_relat_1(C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1209,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1196])).

tff(c_1145,plain,(
    ! [A_195] :
      ( ~ m1_subset_1(A_195,'#skF_3')
      | ~ m1_subset_1(A_195,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_1150,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_1145])).

tff(c_1211,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1209,c_1150])).

tff(c_1574,plain,
    ( v1_xboole_0(k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1556,c_1211])).

tff(c_1604,plain,(
    v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_1181,c_1574])).

tff(c_20,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(k2_relat_1(A_14))
      | ~ v1_relat_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1613,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1604,c_20])).

tff(c_1622,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_1613])).

tff(c_1624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1386,c_1622])).

tff(c_1625,plain,(
    v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_1633,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1625,c_2])).

tff(c_1798,plain,(
    ! [A_325,B_326,C_327] :
      ( k2_relset_1(A_325,B_326,C_327) = k2_relat_1(C_327)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1805,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1798])).

tff(c_1812,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_1805])).

tff(c_1823,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1812,c_20])).

tff(c_1831,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1655,c_1063,c_1823])).

tff(c_1835,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1831,c_47])).

tff(c_1842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1789,c_1835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:40:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.62  
% 3.39/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.62  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.39/1.62  
% 3.39/1.62  %Foreground sorts:
% 3.39/1.62  
% 3.39/1.62  
% 3.39/1.62  %Background operators:
% 3.39/1.62  
% 3.39/1.62  
% 3.39/1.62  %Foreground operators:
% 3.39/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.39/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.39/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.39/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.39/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.39/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.39/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.39/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.39/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.62  
% 3.72/1.64  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.72/1.64  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.72/1.64  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.72/1.64  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.72/1.64  tff(f_32, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.72/1.64  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.72/1.64  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.72/1.64  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.72/1.64  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.72/1.64  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.72/1.64  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.72/1.64  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.72/1.64  tff(f_66, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.72/1.64  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.72/1.64  tff(c_1774, plain, (![A_319, B_320, C_321]: (k1_relset_1(A_319, B_320, C_321)=k1_relat_1(C_321) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_319, B_320))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.72/1.64  tff(c_1787, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1774])).
% 3.72/1.64  tff(c_34, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.72/1.64  tff(c_1789, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_34])).
% 3.72/1.64  tff(c_1642, plain, (![C_284, A_285, B_286]: (v1_relat_1(C_284) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.72/1.64  tff(c_1655, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1642])).
% 3.72/1.64  tff(c_121, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.72/1.64  tff(c_134, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_121])).
% 3.72/1.64  tff(c_193, plain, (![C_78, B_79, A_80]: (v5_relat_1(C_78, B_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.72/1.64  tff(c_206, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_193])).
% 3.72/1.64  tff(c_4, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.72/1.64  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.72/1.64  tff(c_18, plain, (![A_13]: (v1_xboole_0(k1_relat_1(A_13)) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.72/1.64  tff(c_43, plain, (![A_41]: (v1_xboole_0(k1_relat_1(A_41)) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.72/1.64  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.72/1.64  tff(c_48, plain, (![A_42]: (k1_relat_1(A_42)=k1_xboole_0 | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_43, c_2])).
% 3.72/1.64  tff(c_53, plain, (![A_43]: (k1_relat_1(k1_relat_1(A_43))=k1_xboole_0 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_18, c_48])).
% 3.72/1.64  tff(c_62, plain, (![A_43]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_43)) | ~v1_xboole_0(A_43))), inference(superposition, [status(thm), theory('equality')], [c_53, c_18])).
% 3.72/1.64  tff(c_96, plain, (![A_53]: (~v1_xboole_0(k1_relat_1(A_53)) | ~v1_xboole_0(A_53))), inference(splitLeft, [status(thm)], [c_62])).
% 3.72/1.64  tff(c_103, plain, (![A_13]: (~v1_xboole_0(A_13))), inference(resolution, [status(thm)], [c_18, c_96])).
% 3.72/1.64  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.72/1.64  tff(c_104, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | ~m1_subset_1(A_4, B_5))), inference(negUnitSimplification, [status(thm)], [c_103, c_6])).
% 3.72/1.64  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.72/1.64  tff(c_208, plain, (![A_81, C_82, B_83]: (m1_subset_1(A_81, C_82) | ~m1_subset_1(B_83, k1_zfmisc_1(C_82)) | ~r2_hidden(A_81, B_83))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.72/1.64  tff(c_410, plain, (![A_105, B_106, A_107]: (m1_subset_1(A_105, B_106) | ~r2_hidden(A_105, A_107) | ~r1_tarski(A_107, B_106))), inference(resolution, [status(thm)], [c_10, c_208])).
% 3.72/1.64  tff(c_416, plain, (![A_110, B_111, B_112]: (m1_subset_1(A_110, B_111) | ~r1_tarski(B_112, B_111) | ~m1_subset_1(A_110, B_112))), inference(resolution, [status(thm)], [c_104, c_410])).
% 3.72/1.64  tff(c_980, plain, (![A_174, A_175, B_176]: (m1_subset_1(A_174, A_175) | ~m1_subset_1(A_174, k2_relat_1(B_176)) | ~v5_relat_1(B_176, A_175) | ~v1_relat_1(B_176))), inference(resolution, [status(thm)], [c_16, c_416])).
% 3.72/1.64  tff(c_1010, plain, (![B_177, A_178]: (m1_subset_1('#skF_1'(k2_relat_1(B_177)), A_178) | ~v5_relat_1(B_177, A_178) | ~v1_relat_1(B_177))), inference(resolution, [status(thm)], [c_4, c_980])).
% 3.72/1.64  tff(c_270, plain, (![A_97, B_98, C_99]: (k2_relset_1(A_97, B_98, C_99)=k2_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.72/1.64  tff(c_283, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_270])).
% 3.72/1.64  tff(c_89, plain, (![A_51, B_52]: (r2_hidden(A_51, B_52) | v1_xboole_0(B_52) | ~m1_subset_1(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.72/1.64  tff(c_32, plain, (![D_38]: (~r2_hidden(D_38, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_38, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.72/1.64  tff(c_94, plain, (![A_51]: (~m1_subset_1(A_51, '#skF_3') | v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(A_51, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_89, c_32])).
% 3.72/1.64  tff(c_109, plain, (![A_55]: (~m1_subset_1(A_55, '#skF_3') | ~m1_subset_1(A_55, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_103, c_94])).
% 3.72/1.64  tff(c_114, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_4, c_109])).
% 3.72/1.64  tff(c_285, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_114])).
% 3.72/1.64  tff(c_1024, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1010, c_285])).
% 3.72/1.64  tff(c_1062, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_206, c_1024])).
% 3.72/1.64  tff(c_1063, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_62])).
% 3.72/1.64  tff(c_1236, plain, (![A_216, B_217, C_218]: (k1_relset_1(A_216, B_217, C_218)=k1_relat_1(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.72/1.64  tff(c_1249, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1236])).
% 3.72/1.64  tff(c_1251, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_34])).
% 3.72/1.64  tff(c_73, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.72/1.64  tff(c_81, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_73])).
% 3.72/1.64  tff(c_1183, plain, (![A_203, C_204, B_205]: (m1_subset_1(A_203, C_204) | ~m1_subset_1(B_205, k1_zfmisc_1(C_204)) | ~r2_hidden(A_203, B_205))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.72/1.64  tff(c_1273, plain, (![A_222, B_223, A_224]: (m1_subset_1(A_222, B_223) | ~r2_hidden(A_222, A_224) | ~r1_tarski(A_224, B_223))), inference(resolution, [status(thm)], [c_10, c_1183])).
% 3.72/1.64  tff(c_1343, plain, (![A_248, B_249, B_250]: (m1_subset_1(A_248, B_249) | ~r1_tarski(B_250, B_249) | v1_xboole_0(B_250) | ~m1_subset_1(A_248, B_250))), inference(resolution, [status(thm)], [c_6, c_1273])).
% 3.72/1.64  tff(c_1352, plain, (![A_248]: (m1_subset_1(A_248, k2_zfmisc_1('#skF_2', '#skF_3')) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_248, '#skF_4'))), inference(resolution, [status(thm)], [c_81, c_1343])).
% 3.72/1.64  tff(c_1374, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1352])).
% 3.72/1.64  tff(c_47, plain, (![A_41]: (k1_relat_1(A_41)=k1_xboole_0 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_43, c_2])).
% 3.72/1.64  tff(c_1377, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1374, c_47])).
% 3.72/1.64  tff(c_1384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1251, c_1377])).
% 3.72/1.64  tff(c_1386, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1352])).
% 3.72/1.64  tff(c_1088, plain, (![C_179, A_180, B_181]: (v1_relat_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.72/1.64  tff(c_1101, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1088])).
% 3.72/1.64  tff(c_1168, plain, (![C_200, B_201, A_202]: (v5_relat_1(C_200, B_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.72/1.64  tff(c_1181, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_1168])).
% 3.72/1.64  tff(c_1547, plain, (![A_279, A_280, B_281]: (m1_subset_1(A_279, A_280) | v1_xboole_0(k2_relat_1(B_281)) | ~m1_subset_1(A_279, k2_relat_1(B_281)) | ~v5_relat_1(B_281, A_280) | ~v1_relat_1(B_281))), inference(resolution, [status(thm)], [c_16, c_1343])).
% 3.72/1.64  tff(c_1556, plain, (![B_282, A_283]: (m1_subset_1('#skF_1'(k2_relat_1(B_282)), A_283) | v1_xboole_0(k2_relat_1(B_282)) | ~v5_relat_1(B_282, A_283) | ~v1_relat_1(B_282))), inference(resolution, [status(thm)], [c_4, c_1547])).
% 3.72/1.64  tff(c_1196, plain, (![A_209, B_210, C_211]: (k2_relset_1(A_209, B_210, C_211)=k2_relat_1(C_211) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.72/1.64  tff(c_1209, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1196])).
% 3.72/1.64  tff(c_1145, plain, (![A_195]: (~m1_subset_1(A_195, '#skF_3') | ~m1_subset_1(A_195, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_94])).
% 3.72/1.64  tff(c_1150, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_4, c_1145])).
% 3.72/1.64  tff(c_1211, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1209, c_1150])).
% 3.72/1.64  tff(c_1574, plain, (v1_xboole_0(k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1556, c_1211])).
% 3.72/1.64  tff(c_1604, plain, (v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_1181, c_1574])).
% 3.72/1.64  tff(c_20, plain, (![A_14]: (~v1_xboole_0(k2_relat_1(A_14)) | ~v1_relat_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.72/1.64  tff(c_1613, plain, (~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1604, c_20])).
% 3.72/1.64  tff(c_1622, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_1613])).
% 3.72/1.64  tff(c_1624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1386, c_1622])).
% 3.72/1.64  tff(c_1625, plain, (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_94])).
% 3.72/1.64  tff(c_1633, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1625, c_2])).
% 3.72/1.64  tff(c_1798, plain, (![A_325, B_326, C_327]: (k2_relset_1(A_325, B_326, C_327)=k2_relat_1(C_327) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.72/1.64  tff(c_1805, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1798])).
% 3.72/1.64  tff(c_1812, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_1805])).
% 3.72/1.64  tff(c_1823, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1812, c_20])).
% 3.72/1.64  tff(c_1831, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1655, c_1063, c_1823])).
% 3.72/1.64  tff(c_1835, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1831, c_47])).
% 3.72/1.64  tff(c_1842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1789, c_1835])).
% 3.72/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.64  
% 3.72/1.64  Inference rules
% 3.72/1.64  ----------------------
% 3.72/1.64  #Ref     : 0
% 3.72/1.64  #Sup     : 346
% 3.72/1.64  #Fact    : 0
% 3.72/1.64  #Define  : 0
% 3.72/1.64  #Split   : 4
% 3.72/1.64  #Chain   : 0
% 3.72/1.64  #Close   : 0
% 3.72/1.64  
% 3.72/1.64  Ordering : KBO
% 3.72/1.64  
% 3.72/1.64  Simplification rules
% 3.72/1.64  ----------------------
% 3.72/1.64  #Subsume      : 19
% 3.72/1.64  #Demod        : 97
% 3.72/1.64  #Tautology    : 74
% 3.72/1.64  #SimpNegUnit  : 7
% 3.72/1.64  #BackRed      : 12
% 3.72/1.64  
% 3.72/1.64  #Partial instantiations: 0
% 3.72/1.64  #Strategies tried      : 1
% 3.72/1.64  
% 3.72/1.64  Timing (in seconds)
% 3.72/1.64  ----------------------
% 3.72/1.65  Preprocessing        : 0.32
% 3.72/1.65  Parsing              : 0.17
% 3.72/1.65  CNF conversion       : 0.02
% 3.72/1.65  Main loop            : 0.54
% 3.72/1.65  Inferencing          : 0.22
% 3.72/1.65  Reduction            : 0.16
% 3.72/1.65  Demodulation         : 0.10
% 3.72/1.65  BG Simplification    : 0.03
% 3.72/1.65  Subsumption          : 0.08
% 3.72/1.65  Abstraction          : 0.03
% 3.72/1.65  MUC search           : 0.00
% 3.72/1.65  Cooper               : 0.00
% 3.72/1.65  Total                : 0.90
% 3.72/1.65  Index Insertion      : 0.00
% 3.72/1.65  Index Deletion       : 0.00
% 3.72/1.65  Index Matching       : 0.00
% 3.72/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
