%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:14 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 232 expanded)
%              Number of leaves         :   50 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  159 ( 453 expanded)
%              Number of equality atoms :   54 ( 142 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1('#skF_1'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_99,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_111,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_99])).

tff(c_30,plain,(
    ! [A_26] :
      ( k2_relat_1(A_26) != k1_xboole_0
      | k1_xboole_0 = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_120,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_111,c_30])).

tff(c_132,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_169,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_relat_1(C_78,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_181,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_169])).

tff(c_218,plain,(
    ! [B_94,A_95] :
      ( k7_relat_1(B_94,A_95) = B_94
      | ~ v4_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_224,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_181,c_218])).

tff(c_233,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_224])).

tff(c_248,plain,(
    ! [B_97,A_98] :
      ( k2_relat_1(k7_relat_1(B_97,A_98)) = k9_relat_1(B_97,A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_257,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_248])).

tff(c_264,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_257])).

tff(c_20,plain,(
    ! [A_17,B_19] :
      ( k9_relat_1(A_17,k1_tarski(B_19)) = k11_relat_1(A_17,B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_302,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_20])).

tff(c_309,plain,(
    k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_302])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,k1_relat_1(B_23))
      | k11_relat_1(B_23,A_22) = k1_xboole_0
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_153,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_165,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_153])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_525,plain,(
    ! [B_143,C_144,A_145] :
      ( r2_hidden(k1_funct_1(B_143,C_144),A_145)
      | ~ r2_hidden(C_144,k1_relat_1(B_143))
      | ~ v1_funct_1(B_143)
      | ~ v5_relat_1(B_143,A_145)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_62,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_546,plain,
    ( ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_525,c_62])).

tff(c_554,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_165,c_70,c_546])).

tff(c_557,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_554])).

tff(c_563,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_309,c_557])).

tff(c_565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_563])).

tff(c_566,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_574,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_64])).

tff(c_68,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_14,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_572,plain,(
    ! [A_11] : m1_subset_1('#skF_6',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_14])).

tff(c_60,plain,(
    ! [B_53,A_52,C_54] :
      ( k1_xboole_0 = B_53
      | k1_relset_1(A_52,B_53,C_54) = A_52
      | ~ v1_funct_2(C_54,A_52,B_53)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1119,plain,(
    ! [B_247,A_248,C_249] :
      ( B_247 = '#skF_6'
      | k1_relset_1(A_248,B_247,C_249) = A_248
      | ~ v1_funct_2(C_249,A_248,B_247)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_248,B_247))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_60])).

tff(c_1135,plain,(
    ! [B_250,A_251] :
      ( B_250 = '#skF_6'
      | k1_relset_1(A_251,B_250,'#skF_6') = A_251
      | ~ v1_funct_2('#skF_6',A_251,B_250) ) ),
    inference(resolution,[status(thm)],[c_572,c_1119])).

tff(c_1147,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1135])).

tff(c_1155,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_1147])).

tff(c_1007,plain,(
    ! [A_229,B_230,C_231] :
      ( r2_hidden('#skF_2'(A_229,B_230,C_231),B_230)
      | k1_relset_1(B_230,A_229,C_231) = B_230
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(B_230,A_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1018,plain,(
    ! [A_229,B_230] :
      ( r2_hidden('#skF_2'(A_229,B_230,'#skF_6'),B_230)
      | k1_relset_1(B_230,A_229,'#skF_6') = B_230 ) ),
    inference(resolution,[status(thm)],[c_572,c_1007])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_573,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_2])).

tff(c_1193,plain,(
    ! [D_264,A_265,B_266,C_267] :
      ( r2_hidden(k4_tarski(D_264,'#skF_3'(A_265,B_266,C_267,D_264)),C_267)
      | ~ r2_hidden(D_264,B_266)
      | k1_relset_1(B_266,A_265,C_267) != B_266
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(B_266,A_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36,plain,(
    ! [B_32,A_31] :
      ( ~ r1_tarski(B_32,A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1694,plain,(
    ! [C_329,D_330,A_331,B_332] :
      ( ~ r1_tarski(C_329,k4_tarski(D_330,'#skF_3'(A_331,B_332,C_329,D_330)))
      | ~ r2_hidden(D_330,B_332)
      | k1_relset_1(B_332,A_331,C_329) != B_332
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(B_332,A_331))) ) ),
    inference(resolution,[status(thm)],[c_1193,c_36])).

tff(c_1698,plain,(
    ! [D_330,B_332,A_331] :
      ( ~ r2_hidden(D_330,B_332)
      | k1_relset_1(B_332,A_331,'#skF_6') != B_332
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_332,A_331))) ) ),
    inference(resolution,[status(thm)],[c_573,c_1694])).

tff(c_1702,plain,(
    ! [D_333,B_334,A_335] :
      ( ~ r2_hidden(D_333,B_334)
      | k1_relset_1(B_334,A_335,'#skF_6') != B_334 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_1698])).

tff(c_1721,plain,(
    ! [B_336,A_337,A_338] :
      ( k1_relset_1(B_336,A_337,'#skF_6') != B_336
      | k1_relset_1(B_336,A_338,'#skF_6') = B_336 ) ),
    inference(resolution,[status(thm)],[c_1018,c_1702])).

tff(c_1733,plain,(
    ! [A_338] : k1_relset_1(k1_tarski('#skF_4'),A_338,'#skF_6') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1155,c_1721])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1748,plain,(
    ! [B_340,A_341,A_342] :
      ( k1_relset_1(B_340,A_341,'#skF_6') != B_340
      | v1_xboole_0(B_340)
      | ~ m1_subset_1(A_342,B_340) ) ),
    inference(resolution,[status(thm)],[c_16,c_1702])).

tff(c_1750,plain,(
    ! [A_342] :
      ( v1_xboole_0(k1_tarski('#skF_4'))
      | ~ m1_subset_1(A_342,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1733,c_1748])).

tff(c_1765,plain,(
    ! [A_343] : ~ m1_subset_1(A_343,k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_1750])).

tff(c_1785,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_1765])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:19:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.69  
% 4.12/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.70  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 4.12/1.70  
% 4.12/1.70  %Foreground sorts:
% 4.12/1.70  
% 4.12/1.70  
% 4.12/1.70  %Background operators:
% 4.12/1.70  
% 4.12/1.70  
% 4.12/1.70  %Foreground operators:
% 4.12/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.12/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.12/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.12/1.70  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.12/1.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.12/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.12/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.12/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.12/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.12/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.12/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.12/1.70  tff('#skF_5', type, '#skF_5': $i).
% 4.12/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.12/1.70  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.12/1.70  tff('#skF_6', type, '#skF_6': $i).
% 4.12/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.12/1.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.12/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.12/1.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.12/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.12/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.70  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.12/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.12/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.12/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.12/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.12/1.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.12/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.12/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.12/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.70  
% 4.12/1.71  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.12/1.71  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.12/1.71  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 4.12/1.71  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.12/1.71  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.12/1.71  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.12/1.71  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.12/1.71  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.12/1.71  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 4.12/1.71  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 4.12/1.71  tff(f_94, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 4.12/1.71  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.12/1.71  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.12/1.71  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 4.12/1.71  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.12/1.71  tff(f_99, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.12/1.71  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.12/1.71  tff(c_12, plain, (![A_9]: (m1_subset_1('#skF_1'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.12/1.71  tff(c_10, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.12/1.71  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.12/1.71  tff(c_99, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.12/1.71  tff(c_111, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_99])).
% 4.12/1.71  tff(c_30, plain, (![A_26]: (k2_relat_1(A_26)!=k1_xboole_0 | k1_xboole_0=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.12/1.71  tff(c_120, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_111, c_30])).
% 4.12/1.71  tff(c_132, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_120])).
% 4.12/1.71  tff(c_169, plain, (![C_78, A_79, B_80]: (v4_relat_1(C_78, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.12/1.71  tff(c_181, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_169])).
% 4.12/1.71  tff(c_218, plain, (![B_94, A_95]: (k7_relat_1(B_94, A_95)=B_94 | ~v4_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.12/1.71  tff(c_224, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_181, c_218])).
% 4.12/1.71  tff(c_233, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_224])).
% 4.12/1.71  tff(c_248, plain, (![B_97, A_98]: (k2_relat_1(k7_relat_1(B_97, A_98))=k9_relat_1(B_97, A_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.12/1.71  tff(c_257, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_233, c_248])).
% 4.12/1.71  tff(c_264, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_257])).
% 4.12/1.71  tff(c_20, plain, (![A_17, B_19]: (k9_relat_1(A_17, k1_tarski(B_19))=k11_relat_1(A_17, B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.12/1.71  tff(c_302, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_264, c_20])).
% 4.12/1.71  tff(c_309, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_302])).
% 4.12/1.71  tff(c_24, plain, (![A_22, B_23]: (r2_hidden(A_22, k1_relat_1(B_23)) | k11_relat_1(B_23, A_22)=k1_xboole_0 | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.12/1.71  tff(c_153, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.12/1.71  tff(c_165, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_153])).
% 4.12/1.71  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.12/1.71  tff(c_525, plain, (![B_143, C_144, A_145]: (r2_hidden(k1_funct_1(B_143, C_144), A_145) | ~r2_hidden(C_144, k1_relat_1(B_143)) | ~v1_funct_1(B_143) | ~v5_relat_1(B_143, A_145) | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.12/1.71  tff(c_62, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.12/1.71  tff(c_546, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_525, c_62])).
% 4.12/1.71  tff(c_554, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_165, c_70, c_546])).
% 4.12/1.71  tff(c_557, plain, (k11_relat_1('#skF_6', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_554])).
% 4.12/1.71  tff(c_563, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_111, c_309, c_557])).
% 4.12/1.71  tff(c_565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_563])).
% 4.12/1.71  tff(c_566, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_120])).
% 4.12/1.71  tff(c_64, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.12/1.71  tff(c_574, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_566, c_64])).
% 4.12/1.71  tff(c_68, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.12/1.71  tff(c_14, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.12/1.71  tff(c_572, plain, (![A_11]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_566, c_14])).
% 4.12/1.71  tff(c_60, plain, (![B_53, A_52, C_54]: (k1_xboole_0=B_53 | k1_relset_1(A_52, B_53, C_54)=A_52 | ~v1_funct_2(C_54, A_52, B_53) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.12/1.71  tff(c_1119, plain, (![B_247, A_248, C_249]: (B_247='#skF_6' | k1_relset_1(A_248, B_247, C_249)=A_248 | ~v1_funct_2(C_249, A_248, B_247) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_248, B_247))))), inference(demodulation, [status(thm), theory('equality')], [c_566, c_60])).
% 4.12/1.71  tff(c_1135, plain, (![B_250, A_251]: (B_250='#skF_6' | k1_relset_1(A_251, B_250, '#skF_6')=A_251 | ~v1_funct_2('#skF_6', A_251, B_250))), inference(resolution, [status(thm)], [c_572, c_1119])).
% 4.12/1.71  tff(c_1147, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1135])).
% 4.12/1.71  tff(c_1155, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_574, c_1147])).
% 4.12/1.71  tff(c_1007, plain, (![A_229, B_230, C_231]: (r2_hidden('#skF_2'(A_229, B_230, C_231), B_230) | k1_relset_1(B_230, A_229, C_231)=B_230 | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(B_230, A_229))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.12/1.71  tff(c_1018, plain, (![A_229, B_230]: (r2_hidden('#skF_2'(A_229, B_230, '#skF_6'), B_230) | k1_relset_1(B_230, A_229, '#skF_6')=B_230)), inference(resolution, [status(thm)], [c_572, c_1007])).
% 4.12/1.71  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.12/1.71  tff(c_573, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_566, c_2])).
% 4.12/1.71  tff(c_1193, plain, (![D_264, A_265, B_266, C_267]: (r2_hidden(k4_tarski(D_264, '#skF_3'(A_265, B_266, C_267, D_264)), C_267) | ~r2_hidden(D_264, B_266) | k1_relset_1(B_266, A_265, C_267)!=B_266 | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(B_266, A_265))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.12/1.71  tff(c_36, plain, (![B_32, A_31]: (~r1_tarski(B_32, A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.12/1.71  tff(c_1694, plain, (![C_329, D_330, A_331, B_332]: (~r1_tarski(C_329, k4_tarski(D_330, '#skF_3'(A_331, B_332, C_329, D_330))) | ~r2_hidden(D_330, B_332) | k1_relset_1(B_332, A_331, C_329)!=B_332 | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(B_332, A_331))))), inference(resolution, [status(thm)], [c_1193, c_36])).
% 4.12/1.71  tff(c_1698, plain, (![D_330, B_332, A_331]: (~r2_hidden(D_330, B_332) | k1_relset_1(B_332, A_331, '#skF_6')!=B_332 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_332, A_331))))), inference(resolution, [status(thm)], [c_573, c_1694])).
% 4.12/1.71  tff(c_1702, plain, (![D_333, B_334, A_335]: (~r2_hidden(D_333, B_334) | k1_relset_1(B_334, A_335, '#skF_6')!=B_334)), inference(demodulation, [status(thm), theory('equality')], [c_572, c_1698])).
% 4.12/1.71  tff(c_1721, plain, (![B_336, A_337, A_338]: (k1_relset_1(B_336, A_337, '#skF_6')!=B_336 | k1_relset_1(B_336, A_338, '#skF_6')=B_336)), inference(resolution, [status(thm)], [c_1018, c_1702])).
% 4.12/1.71  tff(c_1733, plain, (![A_338]: (k1_relset_1(k1_tarski('#skF_4'), A_338, '#skF_6')=k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1155, c_1721])).
% 4.12/1.71  tff(c_16, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.12/1.71  tff(c_1748, plain, (![B_340, A_341, A_342]: (k1_relset_1(B_340, A_341, '#skF_6')!=B_340 | v1_xboole_0(B_340) | ~m1_subset_1(A_342, B_340))), inference(resolution, [status(thm)], [c_16, c_1702])).
% 4.12/1.71  tff(c_1750, plain, (![A_342]: (v1_xboole_0(k1_tarski('#skF_4')) | ~m1_subset_1(A_342, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1733, c_1748])).
% 4.12/1.71  tff(c_1765, plain, (![A_343]: (~m1_subset_1(A_343, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_10, c_1750])).
% 4.12/1.71  tff(c_1785, plain, $false, inference(resolution, [status(thm)], [c_12, c_1765])).
% 4.12/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.71  
% 4.12/1.71  Inference rules
% 4.12/1.71  ----------------------
% 4.12/1.71  #Ref     : 0
% 4.12/1.71  #Sup     : 339
% 4.12/1.71  #Fact    : 0
% 4.12/1.71  #Define  : 0
% 4.12/1.71  #Split   : 7
% 4.12/1.71  #Chain   : 0
% 4.12/1.71  #Close   : 0
% 4.12/1.71  
% 4.12/1.71  Ordering : KBO
% 4.12/1.71  
% 4.12/1.71  Simplification rules
% 4.12/1.71  ----------------------
% 4.12/1.71  #Subsume      : 10
% 4.12/1.71  #Demod        : 114
% 4.12/1.71  #Tautology    : 114
% 4.12/1.71  #SimpNegUnit  : 3
% 4.12/1.71  #BackRed      : 9
% 4.12/1.71  
% 4.12/1.71  #Partial instantiations: 0
% 4.12/1.71  #Strategies tried      : 1
% 4.12/1.71  
% 4.12/1.71  Timing (in seconds)
% 4.12/1.71  ----------------------
% 4.12/1.72  Preprocessing        : 0.35
% 4.12/1.72  Parsing              : 0.18
% 4.12/1.72  CNF conversion       : 0.02
% 4.12/1.72  Main loop            : 0.58
% 4.12/1.72  Inferencing          : 0.21
% 4.12/1.72  Reduction            : 0.18
% 4.12/1.72  Demodulation         : 0.12
% 4.12/1.72  BG Simplification    : 0.03
% 4.12/1.72  Subsumption          : 0.10
% 4.12/1.72  Abstraction          : 0.03
% 4.12/1.72  MUC search           : 0.00
% 4.12/1.72  Cooper               : 0.00
% 4.12/1.72  Total                : 0.96
% 4.12/1.72  Index Insertion      : 0.00
% 4.12/1.72  Index Deletion       : 0.00
% 4.12/1.72  Index Matching       : 0.00
% 4.12/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
