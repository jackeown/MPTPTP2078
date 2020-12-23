%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:43 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :  108 (1021 expanded)
%              Number of leaves         :   45 ( 369 expanded)
%              Depth                    :   15
%              Number of atoms          :  155 (2447 expanded)
%              Number of equality atoms :   43 ( 617 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_176,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_193,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_176])).

tff(c_38,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,A_21),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_124,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_136,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_26,c_124])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_24,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_747,plain,(
    ! [B_150,A_151] :
      ( k1_tarski(k1_funct_1(B_150,A_151)) = k2_relat_1(B_150)
      | k1_tarski(A_151) != k1_relat_1(B_150)
      | ~ v1_funct_1(B_150)
      | ~ v1_relat_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_68,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_756,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k2_relat_1('#skF_5'))
    | k1_tarski('#skF_2') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_68])).

tff(c_762,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k2_relat_1('#skF_5'))
    | k1_tarski('#skF_2') != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_76,c_756])).

tff(c_787,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_762])).

tff(c_292,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_311,plain,(
    v4_relat_1('#skF_5',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_292])).

tff(c_266,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(k1_relat_1(B_81),A_82)
      | ~ v4_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k1_tarski(B_10) = A_9
      | k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_tarski(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2181,plain,(
    ! [B_296,B_297] :
      ( k1_tarski(B_296) = k1_relat_1(B_297)
      | k1_relat_1(B_297) = k1_xboole_0
      | ~ v4_relat_1(B_297,k1_tarski(B_296))
      | ~ v1_relat_1(B_297) ) ),
    inference(resolution,[status(thm)],[c_266,c_14])).

tff(c_2227,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_311,c_2181])).

tff(c_2254,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_2227])).

tff(c_2255,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_787,c_2254])).

tff(c_58,plain,(
    ! [C_45,B_44] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_45),B_44,C_45),k1_relat_1(C_45))
      | m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_45),B_44)))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2284,plain,(
    ! [B_44] :
      ( r2_hidden('#skF_1'(k1_relat_1('#skF_5'),B_44,'#skF_5'),k1_xboole_0)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_44)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2255,c_58])).

tff(c_2329,plain,(
    ! [B_44] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_44,'#skF_5'),k1_xboole_0)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_76,c_24,c_2255,c_2255,c_2284])).

tff(c_2408,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_2329])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2445,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2408,c_28])).

tff(c_150,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_136,c_150])).

tff(c_2513,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2445,c_158])).

tff(c_2571,plain,(
    ! [A_13] : r1_tarski('#skF_5',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2513,c_136])).

tff(c_603,plain,(
    ! [A_140,B_141,C_142] :
      ( k2_relset_1(A_140,B_141,C_142) = k2_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_623,plain,(
    ! [A_140,B_141] : k2_relset_1(A_140,B_141,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_603])).

tff(c_641,plain,(
    ! [A_146,B_147,C_148] :
      ( m1_subset_1(k2_relset_1(A_146,B_147,C_148),k1_zfmisc_1(B_147))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_678,plain,(
    ! [B_141,A_140] :
      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_141))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_641])).

tff(c_705,plain,(
    ! [B_149] : m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_149)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_678])).

tff(c_789,plain,(
    ! [B_154] : r1_tarski(k2_relat_1(k1_xboole_0),B_154) ),
    inference(resolution,[status(thm)],[c_705,c_28])).

tff(c_832,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_789,c_158])).

tff(c_2552,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2513,c_2513,c_832])).

tff(c_220,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(k9_relat_1(B_72,A_73),k2_relat_1(B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2697,plain,(
    ! [B_307,A_308] :
      ( k9_relat_1(B_307,A_308) = k2_relat_1(B_307)
      | ~ r1_tarski(k2_relat_1(B_307),k9_relat_1(B_307,A_308))
      | ~ v1_relat_1(B_307) ) ),
    inference(resolution,[status(thm)],[c_220,c_2])).

tff(c_2700,plain,(
    ! [A_308] :
      ( k9_relat_1('#skF_5',A_308) = k2_relat_1('#skF_5')
      | ~ r1_tarski('#skF_5',k9_relat_1('#skF_5',A_308))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2552,c_2697])).

tff(c_2702,plain,(
    ! [A_308] : k9_relat_1('#skF_5',A_308) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_2571,c_2552,c_2700])).

tff(c_855,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k7_relset_1(A_155,B_156,C_157,D_158) = k9_relat_1(C_157,D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_873,plain,(
    ! [D_158] : k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5',D_158) = k9_relat_1('#skF_5',D_158) ),
    inference(resolution,[status(thm)],[c_72,c_855])).

tff(c_878,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_4'),k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_68])).

tff(c_3064,plain,(
    ~ r1_tarski('#skF_5',k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2702,c_878])).

tff(c_3068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2571,c_3064])).

tff(c_3109,plain,(
    ! [B_317] : r2_hidden('#skF_1'(k1_xboole_0,B_317,'#skF_5'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2329])).

tff(c_42,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3116,plain,(
    ! [B_317] : ~ r1_tarski(k1_xboole_0,'#skF_1'(k1_xboole_0,B_317,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_3109,c_42])).

tff(c_3124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_3116])).

tff(c_3126,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_762])).

tff(c_3133,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3126,c_72])).

tff(c_54,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k7_relset_1(A_39,B_40,C_41,D_42) = k9_relat_1(C_41,D_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3248,plain,(
    ! [D_42] : k7_relset_1(k1_relat_1('#skF_5'),'#skF_3','#skF_5',D_42) = k9_relat_1('#skF_5',D_42) ),
    inference(resolution,[status(thm)],[c_3133,c_54])).

tff(c_3125,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_762])).

tff(c_3380,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_5'),'#skF_3','#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3126,c_3125])).

tff(c_3432,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3248,c_3380])).

tff(c_3445,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_3432])).

tff(c_3449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_3445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.91  
% 4.80/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.92  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.80/1.92  
% 4.80/1.92  %Foreground sorts:
% 4.80/1.92  
% 4.80/1.92  
% 4.80/1.92  %Background operators:
% 4.80/1.92  
% 4.80/1.92  
% 4.80/1.92  %Foreground operators:
% 4.80/1.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.80/1.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.80/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.80/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.80/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.80/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.80/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.80/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.80/1.92  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.80/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.80/1.92  tff('#skF_5', type, '#skF_5': $i).
% 4.80/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.80/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.80/1.92  tff('#skF_2', type, '#skF_2': $i).
% 4.80/1.92  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.80/1.92  tff('#skF_3', type, '#skF_3': $i).
% 4.80/1.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.80/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.80/1.92  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.80/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.80/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.80/1.92  tff('#skF_4', type, '#skF_4': $i).
% 4.80/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.80/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.80/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.80/1.92  
% 5.17/1.93  tff(f_135, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 5.17/1.93  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.17/1.93  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 5.17/1.93  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.17/1.93  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.17/1.93  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.17/1.93  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.17/1.93  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.17/1.93  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.17/1.93  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.17/1.93  tff(f_123, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 5.17/1.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.17/1.93  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.17/1.93  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.17/1.93  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.17/1.93  tff(f_84, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.17/1.93  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.17/1.93  tff(c_176, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.17/1.93  tff(c_193, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_176])).
% 5.17/1.93  tff(c_38, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, A_21), k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.17/1.93  tff(c_26, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.17/1.93  tff(c_124, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.17/1.93  tff(c_136, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_26, c_124])).
% 5.17/1.93  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.17/1.93  tff(c_24, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.17/1.93  tff(c_747, plain, (![B_150, A_151]: (k1_tarski(k1_funct_1(B_150, A_151))=k2_relat_1(B_150) | k1_tarski(A_151)!=k1_relat_1(B_150) | ~v1_funct_1(B_150) | ~v1_relat_1(B_150))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.17/1.93  tff(c_68, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.17/1.93  tff(c_756, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k2_relat_1('#skF_5')) | k1_tarski('#skF_2')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_747, c_68])).
% 5.17/1.93  tff(c_762, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k2_relat_1('#skF_5')) | k1_tarski('#skF_2')!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_76, c_756])).
% 5.17/1.93  tff(c_787, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_5')), inference(splitLeft, [status(thm)], [c_762])).
% 5.17/1.93  tff(c_292, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.17/1.93  tff(c_311, plain, (v4_relat_1('#skF_5', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_72, c_292])).
% 5.17/1.93  tff(c_266, plain, (![B_81, A_82]: (r1_tarski(k1_relat_1(B_81), A_82) | ~v4_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.17/1.93  tff(c_14, plain, (![B_10, A_9]: (k1_tarski(B_10)=A_9 | k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_tarski(B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.17/1.93  tff(c_2181, plain, (![B_296, B_297]: (k1_tarski(B_296)=k1_relat_1(B_297) | k1_relat_1(B_297)=k1_xboole_0 | ~v4_relat_1(B_297, k1_tarski(B_296)) | ~v1_relat_1(B_297))), inference(resolution, [status(thm)], [c_266, c_14])).
% 5.17/1.93  tff(c_2227, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_311, c_2181])).
% 5.17/1.93  tff(c_2254, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_193, c_2227])).
% 5.17/1.93  tff(c_2255, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_787, c_2254])).
% 5.17/1.93  tff(c_58, plain, (![C_45, B_44]: (r2_hidden('#skF_1'(k1_relat_1(C_45), B_44, C_45), k1_relat_1(C_45)) | m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_45), B_44))) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.17/1.93  tff(c_2284, plain, (![B_44]: (r2_hidden('#skF_1'(k1_relat_1('#skF_5'), B_44, '#skF_5'), k1_xboole_0) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_44))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2255, c_58])).
% 5.17/1.93  tff(c_2329, plain, (![B_44]: (r2_hidden('#skF_1'(k1_xboole_0, B_44, '#skF_5'), k1_xboole_0) | m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_76, c_24, c_2255, c_2255, c_2284])).
% 5.17/1.93  tff(c_2408, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_2329])).
% 5.17/1.93  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.17/1.93  tff(c_2445, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_2408, c_28])).
% 5.17/1.93  tff(c_150, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.17/1.93  tff(c_158, plain, (![A_13]: (k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_136, c_150])).
% 5.17/1.93  tff(c_2513, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2445, c_158])).
% 5.17/1.93  tff(c_2571, plain, (![A_13]: (r1_tarski('#skF_5', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_2513, c_136])).
% 5.17/1.93  tff(c_603, plain, (![A_140, B_141, C_142]: (k2_relset_1(A_140, B_141, C_142)=k2_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.17/1.93  tff(c_623, plain, (![A_140, B_141]: (k2_relset_1(A_140, B_141, k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_603])).
% 5.17/1.93  tff(c_641, plain, (![A_146, B_147, C_148]: (m1_subset_1(k2_relset_1(A_146, B_147, C_148), k1_zfmisc_1(B_147)) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.17/1.93  tff(c_678, plain, (![B_141, A_140]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_141)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(superposition, [status(thm), theory('equality')], [c_623, c_641])).
% 5.17/1.93  tff(c_705, plain, (![B_149]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_149)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_678])).
% 5.17/1.93  tff(c_789, plain, (![B_154]: (r1_tarski(k2_relat_1(k1_xboole_0), B_154))), inference(resolution, [status(thm)], [c_705, c_28])).
% 5.17/1.93  tff(c_832, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_789, c_158])).
% 5.17/1.93  tff(c_2552, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2513, c_2513, c_832])).
% 5.17/1.93  tff(c_220, plain, (![B_72, A_73]: (r1_tarski(k9_relat_1(B_72, A_73), k2_relat_1(B_72)) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.17/1.93  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.17/1.93  tff(c_2697, plain, (![B_307, A_308]: (k9_relat_1(B_307, A_308)=k2_relat_1(B_307) | ~r1_tarski(k2_relat_1(B_307), k9_relat_1(B_307, A_308)) | ~v1_relat_1(B_307))), inference(resolution, [status(thm)], [c_220, c_2])).
% 5.17/1.93  tff(c_2700, plain, (![A_308]: (k9_relat_1('#skF_5', A_308)=k2_relat_1('#skF_5') | ~r1_tarski('#skF_5', k9_relat_1('#skF_5', A_308)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2552, c_2697])).
% 5.17/1.93  tff(c_2702, plain, (![A_308]: (k9_relat_1('#skF_5', A_308)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_2571, c_2552, c_2700])).
% 5.17/1.93  tff(c_855, plain, (![A_155, B_156, C_157, D_158]: (k7_relset_1(A_155, B_156, C_157, D_158)=k9_relat_1(C_157, D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.17/1.93  tff(c_873, plain, (![D_158]: (k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', D_158)=k9_relat_1('#skF_5', D_158))), inference(resolution, [status(thm)], [c_72, c_855])).
% 5.17/1.93  tff(c_878, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_4'), k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_873, c_68])).
% 5.17/1.94  tff(c_3064, plain, (~r1_tarski('#skF_5', k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2702, c_878])).
% 5.17/1.94  tff(c_3068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2571, c_3064])).
% 5.17/1.94  tff(c_3109, plain, (![B_317]: (r2_hidden('#skF_1'(k1_xboole_0, B_317, '#skF_5'), k1_xboole_0))), inference(splitRight, [status(thm)], [c_2329])).
% 5.17/1.94  tff(c_42, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.17/1.94  tff(c_3116, plain, (![B_317]: (~r1_tarski(k1_xboole_0, '#skF_1'(k1_xboole_0, B_317, '#skF_5')))), inference(resolution, [status(thm)], [c_3109, c_42])).
% 5.17/1.94  tff(c_3124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_3116])).
% 5.17/1.94  tff(c_3126, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_5')), inference(splitRight, [status(thm)], [c_762])).
% 5.17/1.94  tff(c_3133, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3126, c_72])).
% 5.17/1.94  tff(c_54, plain, (![A_39, B_40, C_41, D_42]: (k7_relset_1(A_39, B_40, C_41, D_42)=k9_relat_1(C_41, D_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.17/1.94  tff(c_3248, plain, (![D_42]: (k7_relset_1(k1_relat_1('#skF_5'), '#skF_3', '#skF_5', D_42)=k9_relat_1('#skF_5', D_42))), inference(resolution, [status(thm)], [c_3133, c_54])).
% 5.17/1.94  tff(c_3125, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_762])).
% 5.17/1.94  tff(c_3380, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_5'), '#skF_3', '#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3126, c_3125])).
% 5.17/1.94  tff(c_3432, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3248, c_3380])).
% 5.17/1.94  tff(c_3445, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_3432])).
% 5.17/1.94  tff(c_3449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_3445])).
% 5.17/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/1.94  
% 5.17/1.94  Inference rules
% 5.17/1.94  ----------------------
% 5.17/1.94  #Ref     : 0
% 5.17/1.94  #Sup     : 712
% 5.17/1.94  #Fact    : 0
% 5.17/1.94  #Define  : 0
% 5.17/1.94  #Split   : 5
% 5.17/1.94  #Chain   : 0
% 5.17/1.94  #Close   : 0
% 5.17/1.94  
% 5.17/1.94  Ordering : KBO
% 5.17/1.94  
% 5.17/1.94  Simplification rules
% 5.17/1.94  ----------------------
% 5.17/1.94  #Subsume      : 43
% 5.17/1.94  #Demod        : 1080
% 5.17/1.94  #Tautology    : 395
% 5.17/1.94  #SimpNegUnit  : 1
% 5.17/1.94  #BackRed      : 94
% 5.17/1.94  
% 5.17/1.94  #Partial instantiations: 0
% 5.17/1.94  #Strategies tried      : 1
% 5.17/1.94  
% 5.17/1.94  Timing (in seconds)
% 5.17/1.94  ----------------------
% 5.17/1.94  Preprocessing        : 0.36
% 5.17/1.94  Parsing              : 0.19
% 5.17/1.94  CNF conversion       : 0.03
% 5.17/1.94  Main loop            : 0.79
% 5.17/1.94  Inferencing          : 0.26
% 5.17/1.94  Reduction            : 0.30
% 5.17/1.94  Demodulation         : 0.23
% 5.17/1.94  BG Simplification    : 0.03
% 5.17/1.94  Subsumption          : 0.13
% 5.17/1.94  Abstraction          : 0.03
% 5.17/1.94  MUC search           : 0.00
% 5.17/1.94  Cooper               : 0.00
% 5.17/1.94  Total                : 1.19
% 5.17/1.94  Index Insertion      : 0.00
% 5.17/1.94  Index Deletion       : 0.00
% 5.17/1.94  Index Matching       : 0.00
% 5.17/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
