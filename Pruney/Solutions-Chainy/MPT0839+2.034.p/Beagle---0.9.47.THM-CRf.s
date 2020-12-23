%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:26 EST 2020

% Result     : Theorem 5.56s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 259 expanded)
%              Number of leaves         :   35 ( 102 expanded)
%              Depth                    :   12
%              Number of atoms          :  175 ( 539 expanded)
%              Number of equality atoms :   42 ( 120 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2607,plain,(
    ! [A_279,B_280,C_281] :
      ( k2_relset_1(A_279,B_280,C_281) = k2_relat_1(C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2627,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_2607])).

tff(c_48,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2628,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_48])).

tff(c_34,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_102,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_108,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_102])).

tff(c_112,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_108])).

tff(c_58,plain,(
    ! [B_47] : k2_zfmisc_1(k1_xboole_0,B_47) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_34])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_160,plain,(
    ! [C_66,B_67,A_68] :
      ( v5_relat_1(C_66,B_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_194,plain,(
    ! [A_76,B_77,A_78] :
      ( v5_relat_1(A_76,B_77)
      | ~ r1_tarski(A_76,k2_zfmisc_1(A_78,B_77)) ) ),
    inference(resolution,[status(thm)],[c_22,c_160])).

tff(c_216,plain,(
    ! [A_79,B_80] : v5_relat_1(k2_zfmisc_1(A_79,B_80),B_80) ),
    inference(resolution,[status(thm)],[c_6,c_194])).

tff(c_222,plain,(
    ! [B_5] : v5_relat_1(k1_xboole_0,B_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_216])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_215,plain,(
    ! [A_78,B_77] : v5_relat_1(k2_zfmisc_1(A_78,B_77),B_77) ),
    inference(resolution,[status(thm)],[c_6,c_194])).

tff(c_225,plain,(
    ! [B_82,A_83] :
      ( r1_tarski(k2_relat_1(B_82),A_83)
      | ~ v5_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_243,plain,(
    ! [B_84] :
      ( k2_relat_1(B_84) = k1_xboole_0
      | ~ v5_relat_1(B_84,k1_xboole_0)
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_225,c_8])).

tff(c_251,plain,(
    ! [A_78] :
      ( k2_relat_1(k2_zfmisc_1(A_78,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_78,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_215,c_243])).

tff(c_261,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12,c_251])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_266,plain,(
    ! [A_16] :
      ( r1_tarski(k1_xboole_0,A_16)
      | ~ v5_relat_1(k1_xboole_0,A_16)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_32])).

tff(c_270,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_222,c_266])).

tff(c_575,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_595,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_575])).

tff(c_596,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_48])).

tff(c_340,plain,(
    ! [C_90,A_91,B_92] :
      ( v4_relat_1(C_90,A_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_355,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_340])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_642,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_662,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_642])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1('#skF_1'(A_6,B_7),A_6)
      | k1_xboole_0 = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_356,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_1'(A_93,B_94),B_94)
      | k1_xboole_0 = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    ! [D_43] :
      ( ~ r2_hidden(D_43,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_43,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_361,plain,(
    ! [A_93] :
      ( ~ m1_subset_1('#skF_1'(A_93,k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
      | k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0
      | ~ m1_subset_1(k1_relset_1('#skF_3','#skF_2','#skF_4'),k1_zfmisc_1(A_93)) ) ),
    inference(resolution,[status(thm)],[c_356,c_46])).

tff(c_526,plain,(
    ! [A_110] :
      ( ~ m1_subset_1('#skF_1'(A_110,k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
      | ~ m1_subset_1(k1_relset_1('#skF_3','#skF_2','#skF_4'),k1_zfmisc_1(A_110)) ) ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_531,plain,
    ( k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k1_relset_1('#skF_3','#skF_2','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_526])).

tff(c_610,plain,(
    ~ m1_subset_1(k1_relset_1('#skF_3','#skF_2','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_531])).

tff(c_614,plain,(
    ~ r1_tarski(k1_relset_1('#skF_3','#skF_2','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_610])).

tff(c_663,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_614])).

tff(c_673,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_663])).

tff(c_677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_355,c_673])).

tff(c_678,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_531])).

tff(c_740,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_751,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_740])).

tff(c_761,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_751])).

tff(c_807,plain,(
    ! [C_137,A_138,B_139] :
      ( m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ r1_tarski(k2_relat_1(C_137),B_139)
      | ~ r1_tarski(k1_relat_1(C_137),A_138)
      | ~ v1_relat_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2304,plain,(
    ! [C_259,B_260] :
      ( m1_subset_1(C_259,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_259),B_260)
      | ~ r1_tarski(k1_relat_1(C_259),k1_xboole_0)
      | ~ v1_relat_1(C_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_807])).

tff(c_2333,plain,(
    ! [C_261] :
      ( m1_subset_1(C_261,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(C_261),k1_xboole_0)
      | ~ v1_relat_1(C_261) ) ),
    inference(resolution,[status(thm)],[c_6,c_2304])).

tff(c_2336,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_2333])).

tff(c_2345,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_270,c_2336])).

tff(c_173,plain,(
    ! [C_66,B_5] :
      ( v5_relat_1(C_66,B_5)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_160])).

tff(c_2381,plain,(
    ! [B_262] : v5_relat_1('#skF_4',B_262) ),
    inference(resolution,[status(thm)],[c_2345,c_173])).

tff(c_242,plain,(
    ! [B_82] :
      ( k2_relat_1(B_82) = k1_xboole_0
      | ~ v5_relat_1(B_82,k1_xboole_0)
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_225,c_8])).

tff(c_2394,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2381,c_242])).

tff(c_2406,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_2394])).

tff(c_2408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_596,c_2406])).

tff(c_2409,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_2643,plain,(
    ! [A_284,B_285,C_286] :
      ( k1_relset_1(A_284,B_285,C_286) = k1_relat_1(C_286)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2654,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_2643])).

tff(c_2664,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2409,c_2654])).

tff(c_2738,plain,(
    ! [C_292,A_293,B_294] :
      ( m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294)))
      | ~ r1_tarski(k2_relat_1(C_292),B_294)
      | ~ r1_tarski(k1_relat_1(C_292),A_293)
      | ~ v1_relat_1(C_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4268,plain,(
    ! [C_409,B_410] :
      ( m1_subset_1(C_409,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_409),B_410)
      | ~ r1_tarski(k1_relat_1(C_409),k1_xboole_0)
      | ~ v1_relat_1(C_409) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2738])).

tff(c_4282,plain,(
    ! [C_411] :
      ( m1_subset_1(C_411,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(C_411),k1_xboole_0)
      | ~ v1_relat_1(C_411) ) ),
    inference(resolution,[status(thm)],[c_6,c_4268])).

tff(c_4288,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2664,c_4282])).

tff(c_4299,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_270,c_4288])).

tff(c_4335,plain,(
    ! [B_412] : v5_relat_1('#skF_4',B_412) ),
    inference(resolution,[status(thm)],[c_4299,c_173])).

tff(c_4348,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4335,c_242])).

tff(c_4360,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_4348])).

tff(c_4362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2628,c_4360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:33:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.56/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.08  
% 5.71/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.08  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.71/2.08  
% 5.71/2.08  %Foreground sorts:
% 5.71/2.08  
% 5.71/2.08  
% 5.71/2.08  %Background operators:
% 5.71/2.08  
% 5.71/2.08  
% 5.71/2.08  %Foreground operators:
% 5.71/2.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.71/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.71/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.71/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.71/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.71/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.71/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.71/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.71/2.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.71/2.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.71/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.71/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.71/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.71/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.71/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.71/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.71/2.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.71/2.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.71/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.71/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.71/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.71/2.08  
% 5.71/2.10  tff(f_121, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 5.71/2.10  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.71/2.10  tff(f_78, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.71/2.10  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.71/2.10  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.71/2.10  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.71/2.10  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.71/2.10  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.71/2.10  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.71/2.10  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.71/2.10  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.71/2.10  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.71/2.10  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 5.71/2.10  tff(f_100, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.71/2.10  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.71/2.10  tff(c_2607, plain, (![A_279, B_280, C_281]: (k2_relset_1(A_279, B_280, C_281)=k2_relat_1(C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.71/2.10  tff(c_2627, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_2607])).
% 5.71/2.10  tff(c_48, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.71/2.10  tff(c_2628, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_48])).
% 5.71/2.10  tff(c_34, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.71/2.10  tff(c_102, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.71/2.10  tff(c_108, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_102])).
% 5.71/2.10  tff(c_112, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_108])).
% 5.71/2.10  tff(c_58, plain, (![B_47]: (k2_zfmisc_1(k1_xboole_0, B_47)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.71/2.10  tff(c_62, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_34])).
% 5.71/2.10  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.71/2.10  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.71/2.10  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.71/2.10  tff(c_160, plain, (![C_66, B_67, A_68]: (v5_relat_1(C_66, B_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_67))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.71/2.10  tff(c_194, plain, (![A_76, B_77, A_78]: (v5_relat_1(A_76, B_77) | ~r1_tarski(A_76, k2_zfmisc_1(A_78, B_77)))), inference(resolution, [status(thm)], [c_22, c_160])).
% 5.71/2.10  tff(c_216, plain, (![A_79, B_80]: (v5_relat_1(k2_zfmisc_1(A_79, B_80), B_80))), inference(resolution, [status(thm)], [c_6, c_194])).
% 5.71/2.10  tff(c_222, plain, (![B_5]: (v5_relat_1(k1_xboole_0, B_5))), inference(superposition, [status(thm), theory('equality')], [c_14, c_216])).
% 5.71/2.10  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.71/2.10  tff(c_215, plain, (![A_78, B_77]: (v5_relat_1(k2_zfmisc_1(A_78, B_77), B_77))), inference(resolution, [status(thm)], [c_6, c_194])).
% 5.71/2.10  tff(c_225, plain, (![B_82, A_83]: (r1_tarski(k2_relat_1(B_82), A_83) | ~v5_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.71/2.10  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.71/2.10  tff(c_243, plain, (![B_84]: (k2_relat_1(B_84)=k1_xboole_0 | ~v5_relat_1(B_84, k1_xboole_0) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_225, c_8])).
% 5.71/2.10  tff(c_251, plain, (![A_78]: (k2_relat_1(k2_zfmisc_1(A_78, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_78, k1_xboole_0)))), inference(resolution, [status(thm)], [c_215, c_243])).
% 5.71/2.10  tff(c_261, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12, c_251])).
% 5.71/2.10  tff(c_32, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.71/2.10  tff(c_266, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16) | ~v5_relat_1(k1_xboole_0, A_16) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_261, c_32])).
% 5.71/2.10  tff(c_270, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_222, c_266])).
% 5.71/2.10  tff(c_575, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.71/2.10  tff(c_595, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_575])).
% 5.71/2.10  tff(c_596, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_595, c_48])).
% 5.71/2.10  tff(c_340, plain, (![C_90, A_91, B_92]: (v4_relat_1(C_90, A_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.71/2.10  tff(c_355, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_340])).
% 5.71/2.10  tff(c_28, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.71/2.10  tff(c_642, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.71/2.10  tff(c_662, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_642])).
% 5.71/2.10  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1('#skF_1'(A_6, B_7), A_6) | k1_xboole_0=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.71/2.10  tff(c_356, plain, (![A_93, B_94]: (r2_hidden('#skF_1'(A_93, B_94), B_94) | k1_xboole_0=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.71/2.10  tff(c_46, plain, (![D_43]: (~r2_hidden(D_43, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_43, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.71/2.10  tff(c_361, plain, (![A_93]: (~m1_subset_1('#skF_1'(A_93, k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0 | ~m1_subset_1(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), k1_zfmisc_1(A_93)))), inference(resolution, [status(thm)], [c_356, c_46])).
% 5.71/2.10  tff(c_526, plain, (![A_110]: (~m1_subset_1('#skF_1'(A_110, k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | ~m1_subset_1(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), k1_zfmisc_1(A_110)))), inference(splitLeft, [status(thm)], [c_361])).
% 5.71/2.10  tff(c_531, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0 | ~m1_subset_1(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_526])).
% 5.71/2.10  tff(c_610, plain, (~m1_subset_1(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_531])).
% 5.71/2.10  tff(c_614, plain, (~r1_tarski(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_22, c_610])).
% 5.71/2.10  tff(c_663, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_662, c_614])).
% 5.71/2.10  tff(c_673, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_663])).
% 5.71/2.10  tff(c_677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_355, c_673])).
% 5.71/2.10  tff(c_678, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_531])).
% 5.71/2.10  tff(c_740, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.71/2.10  tff(c_751, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_740])).
% 5.71/2.10  tff(c_761, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_678, c_751])).
% 5.71/2.10  tff(c_807, plain, (![C_137, A_138, B_139]: (m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~r1_tarski(k2_relat_1(C_137), B_139) | ~r1_tarski(k1_relat_1(C_137), A_138) | ~v1_relat_1(C_137))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.71/2.10  tff(c_2304, plain, (![C_259, B_260]: (m1_subset_1(C_259, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_259), B_260) | ~r1_tarski(k1_relat_1(C_259), k1_xboole_0) | ~v1_relat_1(C_259))), inference(superposition, [status(thm), theory('equality')], [c_14, c_807])).
% 5.71/2.10  tff(c_2333, plain, (![C_261]: (m1_subset_1(C_261, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(C_261), k1_xboole_0) | ~v1_relat_1(C_261))), inference(resolution, [status(thm)], [c_6, c_2304])).
% 5.71/2.10  tff(c_2336, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_761, c_2333])).
% 5.71/2.10  tff(c_2345, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_270, c_2336])).
% 5.71/2.10  tff(c_173, plain, (![C_66, B_5]: (v5_relat_1(C_66, B_5) | ~m1_subset_1(C_66, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_160])).
% 5.71/2.10  tff(c_2381, plain, (![B_262]: (v5_relat_1('#skF_4', B_262))), inference(resolution, [status(thm)], [c_2345, c_173])).
% 5.71/2.10  tff(c_242, plain, (![B_82]: (k2_relat_1(B_82)=k1_xboole_0 | ~v5_relat_1(B_82, k1_xboole_0) | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_225, c_8])).
% 5.71/2.10  tff(c_2394, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2381, c_242])).
% 5.71/2.10  tff(c_2406, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_112, c_2394])).
% 5.71/2.10  tff(c_2408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_596, c_2406])).
% 5.71/2.10  tff(c_2409, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_361])).
% 5.71/2.10  tff(c_2643, plain, (![A_284, B_285, C_286]: (k1_relset_1(A_284, B_285, C_286)=k1_relat_1(C_286) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.71/2.10  tff(c_2654, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_2643])).
% 5.71/2.10  tff(c_2664, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2409, c_2654])).
% 5.71/2.10  tff(c_2738, plain, (![C_292, A_293, B_294]: (m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))) | ~r1_tarski(k2_relat_1(C_292), B_294) | ~r1_tarski(k1_relat_1(C_292), A_293) | ~v1_relat_1(C_292))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.71/2.10  tff(c_4268, plain, (![C_409, B_410]: (m1_subset_1(C_409, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_409), B_410) | ~r1_tarski(k1_relat_1(C_409), k1_xboole_0) | ~v1_relat_1(C_409))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2738])).
% 5.71/2.10  tff(c_4282, plain, (![C_411]: (m1_subset_1(C_411, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(C_411), k1_xboole_0) | ~v1_relat_1(C_411))), inference(resolution, [status(thm)], [c_6, c_4268])).
% 5.71/2.10  tff(c_4288, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2664, c_4282])).
% 5.71/2.10  tff(c_4299, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_270, c_4288])).
% 5.71/2.10  tff(c_4335, plain, (![B_412]: (v5_relat_1('#skF_4', B_412))), inference(resolution, [status(thm)], [c_4299, c_173])).
% 5.71/2.10  tff(c_4348, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4335, c_242])).
% 5.71/2.10  tff(c_4360, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_112, c_4348])).
% 5.71/2.10  tff(c_4362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2628, c_4360])).
% 5.71/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.10  
% 5.71/2.10  Inference rules
% 5.71/2.10  ----------------------
% 5.71/2.10  #Ref     : 0
% 5.71/2.10  #Sup     : 901
% 5.71/2.10  #Fact    : 0
% 5.71/2.10  #Define  : 0
% 5.71/2.10  #Split   : 15
% 5.71/2.10  #Chain   : 0
% 5.71/2.10  #Close   : 0
% 5.71/2.11  
% 5.71/2.11  Ordering : KBO
% 5.71/2.11  
% 5.71/2.11  Simplification rules
% 5.71/2.11  ----------------------
% 5.71/2.11  #Subsume      : 162
% 5.71/2.11  #Demod        : 807
% 5.71/2.11  #Tautology    : 352
% 5.71/2.11  #SimpNegUnit  : 51
% 5.71/2.11  #BackRed      : 37
% 5.71/2.11  
% 5.71/2.11  #Partial instantiations: 0
% 5.71/2.11  #Strategies tried      : 1
% 5.71/2.11  
% 5.71/2.11  Timing (in seconds)
% 5.71/2.11  ----------------------
% 5.71/2.11  Preprocessing        : 0.32
% 5.71/2.11  Parsing              : 0.16
% 5.71/2.11  CNF conversion       : 0.02
% 5.71/2.11  Main loop            : 0.98
% 5.71/2.11  Inferencing          : 0.35
% 5.71/2.11  Reduction            : 0.33
% 5.71/2.11  Demodulation         : 0.24
% 5.71/2.11  BG Simplification    : 0.04
% 5.71/2.11  Subsumption          : 0.19
% 5.71/2.11  Abstraction          : 0.05
% 5.71/2.11  MUC search           : 0.00
% 5.71/2.11  Cooper               : 0.00
% 5.71/2.11  Total                : 1.34
% 5.71/2.11  Index Insertion      : 0.00
% 5.71/2.11  Index Deletion       : 0.00
% 5.71/2.11  Index Matching       : 0.00
% 5.71/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
