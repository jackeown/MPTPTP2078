%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:15 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 205 expanded)
%              Number of leaves         :   41 (  86 expanded)
%              Depth                    :    9
%              Number of atoms          :  182 ( 438 expanded)
%              Number of equality atoms :   56 ( 101 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_134,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2706,plain,(
    ! [A_359,B_360,C_361] :
      ( k1_relset_1(A_359,B_360,C_361) = k1_relat_1(C_361)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2735,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_2706])).

tff(c_48,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2736,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2735,c_48])).

tff(c_28,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_99,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_106,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_99])).

tff(c_110,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_106])).

tff(c_465,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_499,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_465])).

tff(c_500,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_48])).

tff(c_263,plain,(
    ! [C_100,B_101,A_102] :
      ( v5_relat_1(C_100,B_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_287,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_263])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_250,plain,(
    ! [C_97,B_98,A_99] :
      ( r2_hidden(C_97,B_98)
      | ~ r2_hidden(C_97,A_99)
      | ~ r1_tarski(A_99,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_288,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_3'(A_103),B_104)
      | ~ r1_tarski(A_103,B_104)
      | k1_xboole_0 = A_103 ) ),
    inference(resolution,[status(thm)],[c_14,c_250])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_300,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1('#skF_3'(A_103),B_104)
      | ~ r1_tarski(A_103,B_104)
      | k1_xboole_0 = A_103 ) ),
    inference(resolution,[status(thm)],[c_288,c_16])).

tff(c_600,plain,(
    ! [A_147,B_148,C_149] :
      ( k2_relset_1(A_147,B_148,C_149) = k2_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_644,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_600])).

tff(c_68,plain,(
    ! [D_59] :
      ( ~ r2_hidden(D_59,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_59,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_78,plain,
    ( ~ m1_subset_1('#skF_3'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_68])).

tff(c_131,plain,(
    ~ m1_subset_1('#skF_3'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_653,plain,(
    ~ m1_subset_1('#skF_3'(k2_relat_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_131])).

tff(c_709,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_300,c_653])).

tff(c_781,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_709])).

tff(c_784,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_781])).

tff(c_788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_287,c_784])).

tff(c_789,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_709])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_111,plain,(
    ! [A_66,B_67] :
      ( ~ r2_hidden('#skF_1'(A_66,B_67),B_67)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [A_70] : r1_tarski(A_70,A_70) ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( v4_relat_1(B_19,A_18)
      | ~ r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_123,plain,(
    ! [B_19] :
      ( v4_relat_1(B_19,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_118,c_20])).

tff(c_144,plain,(
    ! [B_78,A_79] :
      ( k7_relat_1(B_78,A_79) = B_78
      | ~ v4_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_148,plain,(
    ! [B_19] :
      ( k7_relat_1(B_19,k1_relat_1(B_19)) = B_19
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_123,c_144])).

tff(c_220,plain,(
    ! [B_95,A_96] :
      ( k2_relat_1(k7_relat_1(B_95,A_96)) = k9_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_241,plain,(
    ! [B_19] :
      ( k9_relat_1(B_19,k1_relat_1(B_19)) = k2_relat_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_220])).

tff(c_349,plain,(
    ! [B_111,A_112] :
      ( r1_xboole_0(k1_relat_1(B_111),A_112)
      | k9_relat_1(B_111,A_112) != k1_xboole_0
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_989,plain,(
    ! [C_163,A_164,B_165] :
      ( ~ r2_hidden(C_163,A_164)
      | ~ r2_hidden(C_163,k1_relat_1(B_165))
      | k9_relat_1(B_165,A_164) != k1_xboole_0
      | ~ v1_relat_1(B_165) ) ),
    inference(resolution,[status(thm)],[c_349,c_8])).

tff(c_1839,plain,(
    ! [A_251,B_252] :
      ( ~ r2_hidden('#skF_3'(A_251),k1_relat_1(B_252))
      | k9_relat_1(B_252,A_251) != k1_xboole_0
      | ~ v1_relat_1(B_252)
      | k1_xboole_0 = A_251 ) ),
    inference(resolution,[status(thm)],[c_14,c_989])).

tff(c_1850,plain,(
    ! [B_253] :
      ( k9_relat_1(B_253,k1_relat_1(B_253)) != k1_xboole_0
      | ~ v1_relat_1(B_253)
      | k1_relat_1(B_253) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_1839])).

tff(c_2348,plain,(
    ! [B_309] :
      ( k2_relat_1(B_309) != k1_xboole_0
      | ~ v1_relat_1(B_309)
      | k1_relat_1(B_309) = k1_xboole_0
      | ~ v1_relat_1(B_309)
      | ~ v1_relat_1(B_309) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_1850])).

tff(c_2358,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_110,c_2348])).

tff(c_2367,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_789,c_2358])).

tff(c_2369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_2367])).

tff(c_2370,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2977,plain,(
    ! [A_384,B_385,C_386] :
      ( k2_relset_1(A_384,B_385,C_386) = k2_relat_1(C_386)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3000,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_2977])).

tff(c_3007,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2370,c_3000])).

tff(c_2406,plain,(
    ! [B_313,A_314] :
      ( k7_relat_1(B_313,A_314) = B_313
      | ~ v4_relat_1(B_313,A_314)
      | ~ v1_relat_1(B_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2410,plain,(
    ! [B_19] :
      ( k7_relat_1(B_19,k1_relat_1(B_19)) = B_19
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_123,c_2406])).

tff(c_2453,plain,(
    ! [B_324,A_325] :
      ( k2_relat_1(k7_relat_1(B_324,A_325)) = k9_relat_1(B_324,A_325)
      | ~ v1_relat_1(B_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2462,plain,(
    ! [B_19] :
      ( k9_relat_1(B_19,k1_relat_1(B_19)) = k2_relat_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2410,c_2453])).

tff(c_2689,plain,(
    ! [B_356,A_357] :
      ( r1_xboole_0(k1_relat_1(B_356),A_357)
      | k9_relat_1(B_356,A_357) != k1_xboole_0
      | ~ v1_relat_1(B_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3256,plain,(
    ! [C_410,A_411,B_412] :
      ( ~ r2_hidden(C_410,A_411)
      | ~ r2_hidden(C_410,k1_relat_1(B_412))
      | k9_relat_1(B_412,A_411) != k1_xboole_0
      | ~ v1_relat_1(B_412) ) ),
    inference(resolution,[status(thm)],[c_2689,c_8])).

tff(c_4161,plain,(
    ! [A_523,B_524] :
      ( ~ r2_hidden('#skF_3'(A_523),k1_relat_1(B_524))
      | k9_relat_1(B_524,A_523) != k1_xboole_0
      | ~ v1_relat_1(B_524)
      | k1_xboole_0 = A_523 ) ),
    inference(resolution,[status(thm)],[c_14,c_3256])).

tff(c_4172,plain,(
    ! [B_525] :
      ( k9_relat_1(B_525,k1_relat_1(B_525)) != k1_xboole_0
      | ~ v1_relat_1(B_525)
      | k1_relat_1(B_525) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_4161])).

tff(c_4337,plain,(
    ! [B_539] :
      ( k2_relat_1(B_539) != k1_xboole_0
      | ~ v1_relat_1(B_539)
      | k1_relat_1(B_539) = k1_xboole_0
      | ~ v1_relat_1(B_539)
      | ~ v1_relat_1(B_539) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2462,c_4172])).

tff(c_4347,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_110,c_4337])).

tff(c_4356,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_3007,c_4347])).

tff(c_4358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2736,c_4356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.13/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/1.98  
% 5.13/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/1.98  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 5.13/1.98  
% 5.13/1.98  %Foreground sorts:
% 5.13/1.98  
% 5.13/1.98  
% 5.13/1.98  %Background operators:
% 5.13/1.98  
% 5.13/1.98  
% 5.13/1.98  %Foreground operators:
% 5.13/1.98  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.13/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.13/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.13/1.98  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.13/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.13/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.13/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.13/1.98  tff('#skF_5', type, '#skF_5': $i).
% 5.13/1.98  tff('#skF_6', type, '#skF_6': $i).
% 5.13/1.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.13/1.98  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.13/1.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.13/1.98  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.13/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.13/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.13/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.13/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.13/1.98  tff('#skF_4', type, '#skF_4': $i).
% 5.13/1.98  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.13/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.13/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.13/1.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.13/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.13/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.13/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.13/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.13/1.98  
% 5.44/2.00  tff(f_134, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 5.44/2.00  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.44/2.00  tff(f_83, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.44/2.00  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.44/2.00  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.44/2.00  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.44/2.00  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.44/2.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.44/2.00  tff(f_62, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.44/2.00  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.44/2.00  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.44/2.00  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.44/2.00  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.44/2.00  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 5.44/2.00  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.44/2.00  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.44/2.00  tff(c_2706, plain, (![A_359, B_360, C_361]: (k1_relset_1(A_359, B_360, C_361)=k1_relat_1(C_361) | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.44/2.00  tff(c_2735, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_2706])).
% 5.44/2.00  tff(c_48, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.44/2.00  tff(c_2736, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2735, c_48])).
% 5.44/2.00  tff(c_28, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.44/2.00  tff(c_99, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.44/2.00  tff(c_106, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_99])).
% 5.44/2.00  tff(c_110, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_106])).
% 5.44/2.00  tff(c_465, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.44/2.00  tff(c_499, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_465])).
% 5.44/2.00  tff(c_500, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_499, c_48])).
% 5.44/2.00  tff(c_263, plain, (![C_100, B_101, A_102]: (v5_relat_1(C_100, B_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.44/2.00  tff(c_287, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_263])).
% 5.44/2.00  tff(c_26, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.44/2.00  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.44/2.00  tff(c_250, plain, (![C_97, B_98, A_99]: (r2_hidden(C_97, B_98) | ~r2_hidden(C_97, A_99) | ~r1_tarski(A_99, B_98))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.44/2.00  tff(c_288, plain, (![A_103, B_104]: (r2_hidden('#skF_3'(A_103), B_104) | ~r1_tarski(A_103, B_104) | k1_xboole_0=A_103)), inference(resolution, [status(thm)], [c_14, c_250])).
% 5.44/2.00  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.44/2.00  tff(c_300, plain, (![A_103, B_104]: (m1_subset_1('#skF_3'(A_103), B_104) | ~r1_tarski(A_103, B_104) | k1_xboole_0=A_103)), inference(resolution, [status(thm)], [c_288, c_16])).
% 5.44/2.00  tff(c_600, plain, (![A_147, B_148, C_149]: (k2_relset_1(A_147, B_148, C_149)=k2_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.44/2.00  tff(c_644, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_600])).
% 5.44/2.00  tff(c_68, plain, (![D_59]: (~r2_hidden(D_59, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_59, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.44/2.00  tff(c_78, plain, (~m1_subset_1('#skF_3'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_68])).
% 5.44/2.00  tff(c_131, plain, (~m1_subset_1('#skF_3'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_78])).
% 5.44/2.00  tff(c_653, plain, (~m1_subset_1('#skF_3'(k2_relat_1('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_644, c_131])).
% 5.44/2.00  tff(c_709, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | k2_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_300, c_653])).
% 5.44/2.00  tff(c_781, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_709])).
% 5.44/2.00  tff(c_784, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_781])).
% 5.44/2.00  tff(c_788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_287, c_784])).
% 5.44/2.00  tff(c_789, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_709])).
% 5.44/2.00  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.44/2.00  tff(c_111, plain, (![A_66, B_67]: (~r2_hidden('#skF_1'(A_66, B_67), B_67) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.44/2.00  tff(c_118, plain, (![A_70]: (r1_tarski(A_70, A_70))), inference(resolution, [status(thm)], [c_6, c_111])).
% 5.44/2.00  tff(c_20, plain, (![B_19, A_18]: (v4_relat_1(B_19, A_18) | ~r1_tarski(k1_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.44/2.00  tff(c_123, plain, (![B_19]: (v4_relat_1(B_19, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_118, c_20])).
% 5.44/2.00  tff(c_144, plain, (![B_78, A_79]: (k7_relat_1(B_78, A_79)=B_78 | ~v4_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.44/2.00  tff(c_148, plain, (![B_19]: (k7_relat_1(B_19, k1_relat_1(B_19))=B_19 | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_123, c_144])).
% 5.44/2.00  tff(c_220, plain, (![B_95, A_96]: (k2_relat_1(k7_relat_1(B_95, A_96))=k9_relat_1(B_95, A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.44/2.00  tff(c_241, plain, (![B_19]: (k9_relat_1(B_19, k1_relat_1(B_19))=k2_relat_1(B_19) | ~v1_relat_1(B_19) | ~v1_relat_1(B_19))), inference(superposition, [status(thm), theory('equality')], [c_148, c_220])).
% 5.44/2.00  tff(c_349, plain, (![B_111, A_112]: (r1_xboole_0(k1_relat_1(B_111), A_112) | k9_relat_1(B_111, A_112)!=k1_xboole_0 | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.44/2.00  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.44/2.00  tff(c_989, plain, (![C_163, A_164, B_165]: (~r2_hidden(C_163, A_164) | ~r2_hidden(C_163, k1_relat_1(B_165)) | k9_relat_1(B_165, A_164)!=k1_xboole_0 | ~v1_relat_1(B_165))), inference(resolution, [status(thm)], [c_349, c_8])).
% 5.44/2.00  tff(c_1839, plain, (![A_251, B_252]: (~r2_hidden('#skF_3'(A_251), k1_relat_1(B_252)) | k9_relat_1(B_252, A_251)!=k1_xboole_0 | ~v1_relat_1(B_252) | k1_xboole_0=A_251)), inference(resolution, [status(thm)], [c_14, c_989])).
% 5.44/2.00  tff(c_1850, plain, (![B_253]: (k9_relat_1(B_253, k1_relat_1(B_253))!=k1_xboole_0 | ~v1_relat_1(B_253) | k1_relat_1(B_253)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_1839])).
% 5.44/2.00  tff(c_2348, plain, (![B_309]: (k2_relat_1(B_309)!=k1_xboole_0 | ~v1_relat_1(B_309) | k1_relat_1(B_309)=k1_xboole_0 | ~v1_relat_1(B_309) | ~v1_relat_1(B_309))), inference(superposition, [status(thm), theory('equality')], [c_241, c_1850])).
% 5.44/2.00  tff(c_2358, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_110, c_2348])).
% 5.44/2.00  tff(c_2367, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_110, c_789, c_2358])).
% 5.44/2.00  tff(c_2369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_500, c_2367])).
% 5.44/2.00  tff(c_2370, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 5.44/2.00  tff(c_2977, plain, (![A_384, B_385, C_386]: (k2_relset_1(A_384, B_385, C_386)=k2_relat_1(C_386) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.44/2.00  tff(c_3000, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_2977])).
% 5.44/2.00  tff(c_3007, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2370, c_3000])).
% 5.44/2.00  tff(c_2406, plain, (![B_313, A_314]: (k7_relat_1(B_313, A_314)=B_313 | ~v4_relat_1(B_313, A_314) | ~v1_relat_1(B_313))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.44/2.00  tff(c_2410, plain, (![B_19]: (k7_relat_1(B_19, k1_relat_1(B_19))=B_19 | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_123, c_2406])).
% 5.44/2.00  tff(c_2453, plain, (![B_324, A_325]: (k2_relat_1(k7_relat_1(B_324, A_325))=k9_relat_1(B_324, A_325) | ~v1_relat_1(B_324))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.44/2.00  tff(c_2462, plain, (![B_19]: (k9_relat_1(B_19, k1_relat_1(B_19))=k2_relat_1(B_19) | ~v1_relat_1(B_19) | ~v1_relat_1(B_19))), inference(superposition, [status(thm), theory('equality')], [c_2410, c_2453])).
% 5.44/2.00  tff(c_2689, plain, (![B_356, A_357]: (r1_xboole_0(k1_relat_1(B_356), A_357) | k9_relat_1(B_356, A_357)!=k1_xboole_0 | ~v1_relat_1(B_356))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.44/2.00  tff(c_3256, plain, (![C_410, A_411, B_412]: (~r2_hidden(C_410, A_411) | ~r2_hidden(C_410, k1_relat_1(B_412)) | k9_relat_1(B_412, A_411)!=k1_xboole_0 | ~v1_relat_1(B_412))), inference(resolution, [status(thm)], [c_2689, c_8])).
% 5.44/2.00  tff(c_4161, plain, (![A_523, B_524]: (~r2_hidden('#skF_3'(A_523), k1_relat_1(B_524)) | k9_relat_1(B_524, A_523)!=k1_xboole_0 | ~v1_relat_1(B_524) | k1_xboole_0=A_523)), inference(resolution, [status(thm)], [c_14, c_3256])).
% 5.44/2.00  tff(c_4172, plain, (![B_525]: (k9_relat_1(B_525, k1_relat_1(B_525))!=k1_xboole_0 | ~v1_relat_1(B_525) | k1_relat_1(B_525)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_4161])).
% 5.44/2.00  tff(c_4337, plain, (![B_539]: (k2_relat_1(B_539)!=k1_xboole_0 | ~v1_relat_1(B_539) | k1_relat_1(B_539)=k1_xboole_0 | ~v1_relat_1(B_539) | ~v1_relat_1(B_539))), inference(superposition, [status(thm), theory('equality')], [c_2462, c_4172])).
% 5.44/2.00  tff(c_4347, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_110, c_4337])).
% 5.44/2.00  tff(c_4356, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_110, c_3007, c_4347])).
% 5.44/2.00  tff(c_4358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2736, c_4356])).
% 5.44/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.00  
% 5.44/2.00  Inference rules
% 5.44/2.00  ----------------------
% 5.44/2.00  #Ref     : 0
% 5.44/2.00  #Sup     : 908
% 5.44/2.00  #Fact    : 0
% 5.44/2.00  #Define  : 0
% 5.44/2.00  #Split   : 9
% 5.44/2.00  #Chain   : 0
% 5.44/2.00  #Close   : 0
% 5.44/2.00  
% 5.44/2.00  Ordering : KBO
% 5.44/2.00  
% 5.44/2.00  Simplification rules
% 5.44/2.00  ----------------------
% 5.44/2.00  #Subsume      : 262
% 5.44/2.00  #Demod        : 285
% 5.44/2.00  #Tautology    : 194
% 5.44/2.00  #SimpNegUnit  : 5
% 5.44/2.00  #BackRed      : 28
% 5.44/2.00  
% 5.44/2.00  #Partial instantiations: 0
% 5.44/2.00  #Strategies tried      : 1
% 5.44/2.00  
% 5.44/2.00  Timing (in seconds)
% 5.44/2.00  ----------------------
% 5.44/2.00  Preprocessing        : 0.33
% 5.44/2.00  Parsing              : 0.18
% 5.44/2.00  CNF conversion       : 0.02
% 5.44/2.00  Main loop            : 0.90
% 5.44/2.00  Inferencing          : 0.33
% 5.44/2.00  Reduction            : 0.26
% 5.44/2.00  Demodulation         : 0.18
% 5.44/2.00  BG Simplification    : 0.03
% 5.44/2.00  Subsumption          : 0.19
% 5.44/2.00  Abstraction          : 0.04
% 5.44/2.00  MUC search           : 0.00
% 5.44/2.00  Cooper               : 0.00
% 5.44/2.00  Total                : 1.27
% 5.44/2.00  Index Insertion      : 0.00
% 5.44/2.00  Index Deletion       : 0.00
% 5.44/2.00  Index Matching       : 0.00
% 5.44/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
