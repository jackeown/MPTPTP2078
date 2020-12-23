%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:05 EST 2020

% Result     : Theorem 48.11s
% Output     : CNFRefutation 48.20s
% Verified   : 
% Statistics : Number of formulae       :  167 (2281 expanded)
%              Number of leaves         :   42 ( 767 expanded)
%              Depth                    :   38
%              Number of atoms          :  315 (5738 expanded)
%              Number of equality atoms :   75 ( 976 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
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

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    ! [A_84,B_85] :
      ( ~ r2_hidden('#skF_1'(A_84,B_85),B_85)
      | r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_208,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_203])).

tff(c_82,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_210,plain,(
    ! [C_87,B_88,A_89] :
      ( r2_hidden(C_87,B_88)
      | ~ r2_hidden(C_87,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_234,plain,(
    ! [B_88] :
      ( r2_hidden('#skF_8',B_88)
      | ~ r1_tarski('#skF_6',B_88) ) ),
    inference(resolution,[status(thm)],[c_82,c_210])).

tff(c_84,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_168,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_172,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_84,c_168])).

tff(c_88,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_86,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_789,plain,(
    ! [A_171,B_172,C_173] :
      ( k1_relset_1(A_171,B_172,C_173) = k1_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_793,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_84,c_789])).

tff(c_1442,plain,(
    ! [B_241,A_242,C_243] :
      ( k1_xboole_0 = B_241
      | k1_relset_1(A_242,B_241,C_243) = A_242
      | ~ v1_funct_2(C_243,A_242,B_241)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_242,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1445,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_84,c_1442])).

tff(c_1448,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_793,c_1445])).

tff(c_1449,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1448])).

tff(c_56,plain,(
    ! [B_28,A_27] :
      ( r2_hidden(k1_funct_1(B_28,A_27),k2_relat_1(B_28))
      | ~ r2_hidden(A_27,k1_relat_1(B_28))
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_189,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_1'(A_79,B_80),A_79)
      | r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_198,plain,(
    ! [A_14,B_80] :
      ( '#skF_1'(k1_tarski(A_14),B_80) = A_14
      | r1_tarski(k1_tarski(A_14),B_80) ) ),
    inference(resolution,[status(thm)],[c_189,c_34])).

tff(c_36,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_108,plain,(
    ! [B_54,A_55] :
      ( ~ r1_tarski(B_54,A_55)
      | ~ r2_hidden(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_123,plain,(
    ! [C_18] : ~ r1_tarski(k1_tarski(C_18),C_18) ),
    inference(resolution,[status(thm)],[c_36,c_108])).

tff(c_342,plain,(
    ! [A_119,B_120] :
      ( '#skF_1'(k1_tarski(A_119),B_120) = A_119
      | r1_tarski(k1_tarski(A_119),B_120) ) ),
    inference(resolution,[status(thm)],[c_189,c_34])).

tff(c_363,plain,(
    ! [B_120] : '#skF_1'(k1_tarski(B_120),B_120) = B_120 ),
    inference(resolution,[status(thm)],[c_342,c_123])).

tff(c_337,plain,(
    ! [C_116,B_117,A_118] :
      ( v5_relat_1(C_116,B_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_341,plain,(
    v5_relat_1('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_84,c_337])).

tff(c_54,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k2_relat_1(B_26),A_25)
      | ~ v5_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_455,plain,(
    ! [A_141,B_142,B_143] :
      ( r2_hidden('#skF_1'(A_141,B_142),B_143)
      | ~ r1_tarski(A_141,B_143)
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_6,c_210])).

tff(c_833,plain,(
    ! [A_180,A_181,B_182] :
      ( A_180 = '#skF_1'(A_181,B_182)
      | ~ r1_tarski(A_181,k1_tarski(A_180))
      | r1_tarski(A_181,B_182) ) ),
    inference(resolution,[status(thm)],[c_455,c_34])).

tff(c_14410,plain,(
    ! [A_17775,B_17776,B_17777] :
      ( A_17775 = '#skF_1'(k2_relat_1(B_17776),B_17777)
      | r1_tarski(k2_relat_1(B_17776),B_17777)
      | ~ v5_relat_1(B_17776,k1_tarski(A_17775))
      | ~ v1_relat_1(B_17776) ) ),
    inference(resolution,[status(thm)],[c_54,c_833])).

tff(c_14482,plain,(
    ! [B_17777] :
      ( '#skF_1'(k2_relat_1('#skF_9'),B_17777) = '#skF_7'
      | r1_tarski(k2_relat_1('#skF_9'),B_17777)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_341,c_14410])).

tff(c_14486,plain,(
    ! [B_17914] :
      ( '#skF_1'(k2_relat_1('#skF_9'),B_17914) = '#skF_7'
      | r1_tarski(k2_relat_1('#skF_9'),B_17914) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_14482])).

tff(c_483,plain,(
    ! [A_14,A_141,B_142] :
      ( A_14 = '#skF_1'(A_141,B_142)
      | ~ r1_tarski(A_141,k1_tarski(A_14))
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_455,c_34])).

tff(c_30586,plain,(
    ! [A_60325,B_60326] :
      ( A_60325 = '#skF_1'(k2_relat_1('#skF_9'),B_60326)
      | r1_tarski(k2_relat_1('#skF_9'),B_60326)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_60325)) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_14486,c_483])).

tff(c_52,plain,(
    ! [B_26,A_25] :
      ( v5_relat_1(B_26,A_25)
      | ~ r1_tarski(k2_relat_1(B_26),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_33702,plain,(
    ! [B_60326,A_60325] :
      ( v5_relat_1('#skF_9',B_60326)
      | ~ v1_relat_1('#skF_9')
      | A_60325 = '#skF_1'(k2_relat_1('#skF_9'),B_60326)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_60325)) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_30586,c_52])).

tff(c_34268,plain,(
    ! [B_60326,A_60325] :
      ( v5_relat_1('#skF_9',B_60326)
      | A_60325 = '#skF_1'(k2_relat_1('#skF_9'),B_60326)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_60325)) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_33702])).

tff(c_39777,plain,(
    ! [A_75701] :
      ( v5_relat_1('#skF_9',k1_tarski(A_75701))
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_75701)) = A_75701
      | A_75701 != '#skF_7' ) ),
    inference(factorization,[status(thm),theory(equality)],[c_34268])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39843,plain,(
    ! [A_75701] :
      ( ~ r2_hidden(A_75701,k1_tarski(A_75701))
      | r1_tarski(k2_relat_1('#skF_9'),k1_tarski(A_75701))
      | v5_relat_1('#skF_9',k1_tarski(A_75701))
      | A_75701 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39777,c_4])).

tff(c_40250,plain,(
    ! [A_76076] :
      ( r1_tarski(k2_relat_1('#skF_9'),k1_tarski(A_76076))
      | v5_relat_1('#skF_9',k1_tarski(A_76076))
      | A_76076 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_39843])).

tff(c_40270,plain,(
    ! [A_76076] :
      ( ~ v1_relat_1('#skF_9')
      | v5_relat_1('#skF_9',k1_tarski(A_76076))
      | A_76076 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_40250,c_52])).

tff(c_41884,plain,(
    ! [A_83696] :
      ( v5_relat_1('#skF_9',k1_tarski(A_83696))
      | A_83696 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_40270])).

tff(c_58,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_485,plain,(
    ! [B_144,A_145,B_146] :
      ( ~ r1_tarski(B_144,'#skF_1'(A_145,B_146))
      | ~ r1_tarski(A_145,B_144)
      | r1_tarski(A_145,B_146) ) ),
    inference(resolution,[status(thm)],[c_455,c_58])).

tff(c_514,plain,(
    ! [A_149,B_150] :
      ( ~ r1_tarski(A_149,k1_xboole_0)
      | r1_tarski(A_149,B_150) ) ),
    inference(resolution,[status(thm)],[c_8,c_485])).

tff(c_528,plain,(
    ! [B_26,B_150] :
      ( r1_tarski(k2_relat_1(B_26),B_150)
      | ~ v5_relat_1(B_26,k1_xboole_0)
      | ~ v1_relat_1(B_26) ) ),
    inference(resolution,[status(thm)],[c_54,c_514])).

tff(c_1001,plain,(
    ! [B_192,A_193] :
      ( r2_hidden(k1_funct_1(B_192,A_193),k2_relat_1(B_192))
      | ~ r2_hidden(A_193,k1_relat_1(B_192))
      | ~ v1_funct_1(B_192)
      | ~ v1_relat_1(B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1163,plain,(
    ! [B_213,A_214] :
      ( ~ r1_tarski(k2_relat_1(B_213),k1_funct_1(B_213,A_214))
      | ~ r2_hidden(A_214,k1_relat_1(B_213))
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213) ) ),
    inference(resolution,[status(thm)],[c_1001,c_58])).

tff(c_1174,plain,(
    ! [A_215,B_216] :
      ( ~ r2_hidden(A_215,k1_relat_1(B_216))
      | ~ v1_funct_1(B_216)
      | ~ v5_relat_1(B_216,k1_xboole_0)
      | ~ v1_relat_1(B_216) ) ),
    inference(resolution,[status(thm)],[c_528,c_1163])).

tff(c_1198,plain,(
    ! [B_216] :
      ( ~ v1_funct_1(B_216)
      | ~ v5_relat_1(B_216,k1_xboole_0)
      | ~ v1_relat_1(B_216)
      | ~ r1_tarski('#skF_6',k1_relat_1(B_216)) ) ),
    inference(resolution,[status(thm)],[c_234,c_1174])).

tff(c_1457,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v5_relat_1('#skF_9',k1_xboole_0)
    | ~ v1_relat_1('#skF_9')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1449,c_1198])).

tff(c_1466,plain,(
    ~ v5_relat_1('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_172,c_88,c_1457])).

tff(c_512,plain,(
    ! [A_145,B_146] :
      ( ~ r1_tarski(A_145,k1_xboole_0)
      | r1_tarski(A_145,B_146) ) ),
    inference(resolution,[status(thm)],[c_8,c_485])).

tff(c_14606,plain,(
    ! [B_146] :
      ( r1_tarski(k2_relat_1('#skF_9'),B_146)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_xboole_0) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_14486,c_512])).

tff(c_15611,plain,(
    '#skF_1'(k2_relat_1('#skF_9'),k1_xboole_0) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_14606])).

tff(c_15639,plain,
    ( r2_hidden('#skF_7',k2_relat_1('#skF_9'))
    | r1_tarski(k2_relat_1('#skF_9'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_15611,c_6])).

tff(c_16743,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_15639])).

tff(c_16752,plain,
    ( v5_relat_1('#skF_9',k1_xboole_0)
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_16743,c_52])).

tff(c_16762,plain,(
    v5_relat_1('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_16752])).

tff(c_16764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1466,c_16762])).

tff(c_16765,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_15639])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_17836,plain,(
    ! [B_24520] :
      ( r2_hidden('#skF_7',B_24520)
      | ~ r1_tarski(k2_relat_1('#skF_9'),B_24520) ) ),
    inference(resolution,[status(thm)],[c_16765,c_2])).

tff(c_17847,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_7',A_25)
      | ~ v5_relat_1('#skF_9',A_25)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_54,c_17836])).

tff(c_17858,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_7',A_25)
      | ~ v5_relat_1('#skF_9',A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_17847])).

tff(c_41982,plain,(
    ! [A_84105] :
      ( r2_hidden('#skF_7',k1_tarski(A_84105))
      | A_84105 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_41884,c_17858])).

tff(c_42514,plain,(
    ! [B_85332,A_85333] :
      ( r2_hidden('#skF_7',B_85332)
      | ~ r1_tarski(k1_tarski(A_85333),B_85332)
      | A_85333 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_41982,c_2])).

tff(c_46315,plain,(
    ! [B_103398,A_103399] :
      ( r2_hidden('#skF_7',B_103398)
      | A_103399 != '#skF_7'
      | '#skF_1'(k1_tarski(A_103399),B_103398) = A_103399 ) ),
    inference(resolution,[status(thm)],[c_198,c_42514])).

tff(c_49613,plain,(
    ! [A_115175,B_115176] :
      ( ~ r2_hidden(A_115175,B_115176)
      | r1_tarski(k1_tarski(A_115175),B_115176)
      | r2_hidden('#skF_7',B_115176)
      | A_115175 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46315,c_4])).

tff(c_42075,plain,(
    ! [B_2,A_84105] :
      ( r2_hidden('#skF_7',B_2)
      | ~ r1_tarski(k1_tarski(A_84105),B_2)
      | A_84105 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_41982,c_2])).

tff(c_49808,plain,(
    ! [A_115687,B_115688] :
      ( ~ r2_hidden(A_115687,B_115688)
      | r2_hidden('#skF_7',B_115688)
      | A_115687 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_49613,c_42075])).

tff(c_51753,plain,(
    ! [A_121835,B_121836] :
      ( r2_hidden('#skF_7',A_121835)
      | '#skF_1'(A_121835,B_121836) != '#skF_7'
      | r1_tarski(A_121835,B_121836) ) ),
    inference(resolution,[status(thm)],[c_6,c_49808])).

tff(c_235,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_8',B_90)
      | ~ r1_tarski('#skF_6',B_90) ) ),
    inference(resolution,[status(thm)],[c_82,c_210])).

tff(c_247,plain,(
    ! [A_14] :
      ( A_14 = '#skF_8'
      | ~ r1_tarski('#skF_6',k1_tarski(A_14)) ) ),
    inference(resolution,[status(thm)],[c_235,c_34])).

tff(c_52061,plain,(
    ! [A_14] :
      ( A_14 = '#skF_8'
      | r2_hidden('#skF_7','#skF_6')
      | '#skF_1'('#skF_6',k1_tarski(A_14)) != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_51753,c_247])).

tff(c_52081,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_52061])).

tff(c_35205,plain,(
    ! [B_68593,A_68594] :
      ( v5_relat_1('#skF_9',B_68593)
      | A_68594 = '#skF_1'(k2_relat_1('#skF_9'),B_68593)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_68594)) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_33702])).

tff(c_192398,plain,(
    ! [A_392406,B_392407] :
      ( ~ r2_hidden(A_392406,B_392407)
      | r1_tarski(k2_relat_1('#skF_9'),B_392407)
      | v5_relat_1('#skF_9',B_392407)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_392406)) = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35205,c_4])).

tff(c_192818,plain,
    ( r1_tarski(k2_relat_1('#skF_9'),'#skF_6')
    | v5_relat_1('#skF_9','#skF_6')
    | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_52081,c_192398])).

tff(c_192855,plain,(
    '#skF_1'(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_192818])).

tff(c_192966,plain,
    ( ~ r2_hidden('#skF_7',k1_tarski('#skF_7'))
    | r1_tarski(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_192855,c_4])).

tff(c_193404,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_192966])).

tff(c_480,plain,(
    ! [A_141,B_142,B_2,B_143] :
      ( r2_hidden('#skF_1'(A_141,B_142),B_2)
      | ~ r1_tarski(B_143,B_2)
      | ~ r1_tarski(A_141,B_143)
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_455,c_2])).

tff(c_193572,plain,(
    ! [A_394346,B_394347] :
      ( r2_hidden('#skF_1'(A_394346,B_394347),k1_tarski('#skF_7'))
      | ~ r1_tarski(A_394346,k2_relat_1('#skF_9'))
      | r1_tarski(A_394346,B_394347) ) ),
    inference(resolution,[status(thm)],[c_193404,c_480])).

tff(c_194739,plain,(
    ! [B_120] :
      ( r2_hidden(B_120,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(B_120),k2_relat_1('#skF_9'))
      | r1_tarski(k1_tarski(B_120),B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_193572])).

tff(c_195327,plain,(
    ! [B_396288] :
      ( r2_hidden(B_396288,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(B_396288),k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_194739])).

tff(c_195440,plain,(
    ! [A_396935] :
      ( r2_hidden(A_396935,k1_tarski('#skF_7'))
      | '#skF_1'(k1_tarski(A_396935),k2_relat_1('#skF_9')) = A_396935 ) ),
    inference(resolution,[status(thm)],[c_198,c_195327])).

tff(c_204124,plain,(
    ! [A_409238] :
      ( ~ r2_hidden(A_409238,k2_relat_1('#skF_9'))
      | r1_tarski(k1_tarski(A_409238),k2_relat_1('#skF_9'))
      | r2_hidden(A_409238,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195440,c_4])).

tff(c_194999,plain,(
    ! [B_120] :
      ( r2_hidden(B_120,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(B_120),k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_194739])).

tff(c_204369,plain,(
    ! [A_409885] :
      ( ~ r2_hidden(A_409885,k2_relat_1('#skF_9'))
      | r2_hidden(A_409885,k1_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_204124,c_194999])).

tff(c_204445,plain,(
    ! [A_27] :
      ( r2_hidden(k1_funct_1('#skF_9',A_27),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_27,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_56,c_204369])).

tff(c_204724,plain,(
    ! [A_411183] :
      ( r2_hidden(k1_funct_1('#skF_9',A_411183),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_411183,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_88,c_1449,c_204445])).

tff(c_204851,plain,(
    ! [A_411830] :
      ( k1_funct_1('#skF_9',A_411830) = '#skF_7'
      | ~ r2_hidden(A_411830,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_204724,c_34])).

tff(c_204944,plain,
    ( k1_funct_1('#skF_9','#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_234,c_204851])).

tff(c_204979,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_204944])).

tff(c_204981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_204979])).

tff(c_204983,plain,(
    '#skF_1'(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_192818])).

tff(c_14485,plain,(
    ! [B_17777] :
      ( '#skF_1'(k2_relat_1('#skF_9'),B_17777) = '#skF_7'
      | r1_tarski(k2_relat_1('#skF_9'),B_17777) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_14482])).

tff(c_14605,plain,(
    ! [A_14,B_142] :
      ( A_14 = '#skF_1'(k2_relat_1('#skF_9'),B_142)
      | r1_tarski(k2_relat_1('#skF_9'),B_142)
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_14)) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_14486,c_483])).

tff(c_205031,plain,(
    ! [A_14] :
      ( A_14 != '#skF_7'
      | r1_tarski(k2_relat_1('#skF_9'),k1_tarski('#skF_7'))
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_14)) = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14605,c_204983])).

tff(c_212119,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_205031])).

tff(c_213387,plain,(
    ! [A_428015,B_428016] :
      ( r2_hidden('#skF_1'(A_428015,B_428016),k1_tarski('#skF_7'))
      | ~ r1_tarski(A_428015,k2_relat_1('#skF_9'))
      | r1_tarski(A_428015,B_428016) ) ),
    inference(resolution,[status(thm)],[c_212119,c_480])).

tff(c_214559,plain,(
    ! [B_120] :
      ( r2_hidden(B_120,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(B_120),k2_relat_1('#skF_9'))
      | r1_tarski(k1_tarski(B_120),B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_213387])).

tff(c_214975,plain,(
    ! [B_429310] :
      ( r2_hidden(B_429310,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(B_429310),k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_214559])).

tff(c_215088,plain,(
    ! [A_429957] :
      ( r2_hidden(A_429957,k1_tarski('#skF_7'))
      | '#skF_1'(k1_tarski(A_429957),k2_relat_1('#skF_9')) = A_429957 ) ),
    inference(resolution,[status(thm)],[c_198,c_214975])).

tff(c_249263,plain,(
    ! [A_482405] :
      ( ~ r2_hidden(A_482405,k2_relat_1('#skF_9'))
      | r1_tarski(k1_tarski(A_482405),k2_relat_1('#skF_9'))
      | r2_hidden(A_482405,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215088,c_4])).

tff(c_214822,plain,(
    ! [B_120] :
      ( r2_hidden(B_120,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(B_120),k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_214559])).

tff(c_250053,plain,(
    ! [A_483702] :
      ( ~ r2_hidden(A_483702,k2_relat_1('#skF_9'))
      | r2_hidden(A_483702,k1_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_249263,c_214822])).

tff(c_250137,plain,(
    ! [A_27] :
      ( r2_hidden(k1_funct_1('#skF_9',A_27),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_27,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_56,c_250053])).

tff(c_250184,plain,(
    ! [A_484349] :
      ( r2_hidden(k1_funct_1('#skF_9',A_484349),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_484349,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_88,c_1449,c_250137])).

tff(c_250344,plain,(
    ! [A_484996] :
      ( k1_funct_1('#skF_9',A_484996) = '#skF_7'
      | ~ r2_hidden(A_484996,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_250184,c_34])).

tff(c_250460,plain,
    ( k1_funct_1('#skF_9','#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_234,c_250344])).

tff(c_250504,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_250460])).

tff(c_250506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_250504])).

tff(c_250508,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_205031])).

tff(c_251672,plain,(
    '#skF_1'(k2_relat_1('#skF_9'),k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_14485,c_250508])).

tff(c_251700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204983,c_251672])).

tff(c_251701,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1448])).

tff(c_251759,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_251701,c_123])).

tff(c_251783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_251759])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 48.11/36.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.20/36.43  
% 48.20/36.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.20/36.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 48.20/36.43  
% 48.20/36.43  %Foreground sorts:
% 48.20/36.43  
% 48.20/36.43  
% 48.20/36.43  %Background operators:
% 48.20/36.43  
% 48.20/36.43  
% 48.20/36.43  %Foreground operators:
% 48.20/36.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 48.20/36.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 48.20/36.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 48.20/36.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 48.20/36.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 48.20/36.43  tff('#skF_7', type, '#skF_7': $i).
% 48.20/36.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 48.20/36.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 48.20/36.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 48.20/36.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 48.20/36.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 48.20/36.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 48.20/36.43  tff('#skF_6', type, '#skF_6': $i).
% 48.20/36.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 48.20/36.43  tff('#skF_9', type, '#skF_9': $i).
% 48.20/36.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 48.20/36.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 48.20/36.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 48.20/36.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 48.20/36.43  tff('#skF_8', type, '#skF_8': $i).
% 48.20/36.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 48.20/36.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 48.20/36.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 48.20/36.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 48.20/36.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 48.20/36.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 48.20/36.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 48.20/36.43  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 48.20/36.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 48.20/36.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 48.20/36.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 48.20/36.43  
% 48.20/36.46  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 48.20/36.46  tff(f_124, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 48.20/36.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 48.20/36.46  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 48.20/36.46  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 48.20/36.46  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 48.20/36.46  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 48.20/36.46  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 48.20/36.46  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 48.20/36.46  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 48.20/36.46  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 48.20/36.46  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 48.20/36.46  tff(c_80, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_124])).
% 48.20/36.46  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.20/36.46  tff(c_203, plain, (![A_84, B_85]: (~r2_hidden('#skF_1'(A_84, B_85), B_85) | r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.20/36.46  tff(c_208, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_203])).
% 48.20/36.46  tff(c_82, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 48.20/36.46  tff(c_210, plain, (![C_87, B_88, A_89]: (r2_hidden(C_87, B_88) | ~r2_hidden(C_87, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.20/36.46  tff(c_234, plain, (![B_88]: (r2_hidden('#skF_8', B_88) | ~r1_tarski('#skF_6', B_88))), inference(resolution, [status(thm)], [c_82, c_210])).
% 48.20/36.46  tff(c_84, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 48.20/36.46  tff(c_168, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 48.20/36.46  tff(c_172, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_84, c_168])).
% 48.20/36.46  tff(c_88, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_124])).
% 48.20/36.46  tff(c_86, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 48.20/36.46  tff(c_789, plain, (![A_171, B_172, C_173]: (k1_relset_1(A_171, B_172, C_173)=k1_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 48.20/36.46  tff(c_793, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_84, c_789])).
% 48.20/36.46  tff(c_1442, plain, (![B_241, A_242, C_243]: (k1_xboole_0=B_241 | k1_relset_1(A_242, B_241, C_243)=A_242 | ~v1_funct_2(C_243, A_242, B_241) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_242, B_241))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 48.20/36.46  tff(c_1445, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_84, c_1442])).
% 48.20/36.46  tff(c_1448, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_793, c_1445])).
% 48.20/36.46  tff(c_1449, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_1448])).
% 48.20/36.46  tff(c_56, plain, (![B_28, A_27]: (r2_hidden(k1_funct_1(B_28, A_27), k2_relat_1(B_28)) | ~r2_hidden(A_27, k1_relat_1(B_28)) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 48.20/36.46  tff(c_189, plain, (![A_79, B_80]: (r2_hidden('#skF_1'(A_79, B_80), A_79) | r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.20/36.46  tff(c_34, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 48.20/36.46  tff(c_198, plain, (![A_14, B_80]: ('#skF_1'(k1_tarski(A_14), B_80)=A_14 | r1_tarski(k1_tarski(A_14), B_80))), inference(resolution, [status(thm)], [c_189, c_34])).
% 48.20/36.46  tff(c_36, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 48.20/36.46  tff(c_108, plain, (![B_54, A_55]: (~r1_tarski(B_54, A_55) | ~r2_hidden(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_81])).
% 48.20/36.46  tff(c_123, plain, (![C_18]: (~r1_tarski(k1_tarski(C_18), C_18))), inference(resolution, [status(thm)], [c_36, c_108])).
% 48.20/36.46  tff(c_342, plain, (![A_119, B_120]: ('#skF_1'(k1_tarski(A_119), B_120)=A_119 | r1_tarski(k1_tarski(A_119), B_120))), inference(resolution, [status(thm)], [c_189, c_34])).
% 48.20/36.46  tff(c_363, plain, (![B_120]: ('#skF_1'(k1_tarski(B_120), B_120)=B_120)), inference(resolution, [status(thm)], [c_342, c_123])).
% 48.20/36.46  tff(c_337, plain, (![C_116, B_117, A_118]: (v5_relat_1(C_116, B_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 48.20/36.46  tff(c_341, plain, (v5_relat_1('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_84, c_337])).
% 48.20/36.46  tff(c_54, plain, (![B_26, A_25]: (r1_tarski(k2_relat_1(B_26), A_25) | ~v5_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 48.20/36.46  tff(c_455, plain, (![A_141, B_142, B_143]: (r2_hidden('#skF_1'(A_141, B_142), B_143) | ~r1_tarski(A_141, B_143) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_6, c_210])).
% 48.20/36.46  tff(c_833, plain, (![A_180, A_181, B_182]: (A_180='#skF_1'(A_181, B_182) | ~r1_tarski(A_181, k1_tarski(A_180)) | r1_tarski(A_181, B_182))), inference(resolution, [status(thm)], [c_455, c_34])).
% 48.20/36.46  tff(c_14410, plain, (![A_17775, B_17776, B_17777]: (A_17775='#skF_1'(k2_relat_1(B_17776), B_17777) | r1_tarski(k2_relat_1(B_17776), B_17777) | ~v5_relat_1(B_17776, k1_tarski(A_17775)) | ~v1_relat_1(B_17776))), inference(resolution, [status(thm)], [c_54, c_833])).
% 48.20/36.46  tff(c_14482, plain, (![B_17777]: ('#skF_1'(k2_relat_1('#skF_9'), B_17777)='#skF_7' | r1_tarski(k2_relat_1('#skF_9'), B_17777) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_341, c_14410])).
% 48.20/36.46  tff(c_14486, plain, (![B_17914]: ('#skF_1'(k2_relat_1('#skF_9'), B_17914)='#skF_7' | r1_tarski(k2_relat_1('#skF_9'), B_17914))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_14482])).
% 48.20/36.46  tff(c_483, plain, (![A_14, A_141, B_142]: (A_14='#skF_1'(A_141, B_142) | ~r1_tarski(A_141, k1_tarski(A_14)) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_455, c_34])).
% 48.20/36.46  tff(c_30586, plain, (![A_60325, B_60326]: (A_60325='#skF_1'(k2_relat_1('#skF_9'), B_60326) | r1_tarski(k2_relat_1('#skF_9'), B_60326) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_60325))='#skF_7')), inference(resolution, [status(thm)], [c_14486, c_483])).
% 48.20/36.46  tff(c_52, plain, (![B_26, A_25]: (v5_relat_1(B_26, A_25) | ~r1_tarski(k2_relat_1(B_26), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 48.20/36.46  tff(c_33702, plain, (![B_60326, A_60325]: (v5_relat_1('#skF_9', B_60326) | ~v1_relat_1('#skF_9') | A_60325='#skF_1'(k2_relat_1('#skF_9'), B_60326) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_60325))='#skF_7')), inference(resolution, [status(thm)], [c_30586, c_52])).
% 48.20/36.46  tff(c_34268, plain, (![B_60326, A_60325]: (v5_relat_1('#skF_9', B_60326) | A_60325='#skF_1'(k2_relat_1('#skF_9'), B_60326) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_60325))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_33702])).
% 48.20/36.46  tff(c_39777, plain, (![A_75701]: (v5_relat_1('#skF_9', k1_tarski(A_75701)) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_75701))=A_75701 | A_75701!='#skF_7')), inference(factorization, [status(thm), theory('equality')], [c_34268])).
% 48.20/36.46  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.20/36.46  tff(c_39843, plain, (![A_75701]: (~r2_hidden(A_75701, k1_tarski(A_75701)) | r1_tarski(k2_relat_1('#skF_9'), k1_tarski(A_75701)) | v5_relat_1('#skF_9', k1_tarski(A_75701)) | A_75701!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_39777, c_4])).
% 48.20/36.46  tff(c_40250, plain, (![A_76076]: (r1_tarski(k2_relat_1('#skF_9'), k1_tarski(A_76076)) | v5_relat_1('#skF_9', k1_tarski(A_76076)) | A_76076!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_39843])).
% 48.20/36.46  tff(c_40270, plain, (![A_76076]: (~v1_relat_1('#skF_9') | v5_relat_1('#skF_9', k1_tarski(A_76076)) | A_76076!='#skF_7')), inference(resolution, [status(thm)], [c_40250, c_52])).
% 48.20/36.46  tff(c_41884, plain, (![A_83696]: (v5_relat_1('#skF_9', k1_tarski(A_83696)) | A_83696!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_40270])).
% 48.20/36.46  tff(c_58, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_81])).
% 48.20/36.46  tff(c_485, plain, (![B_144, A_145, B_146]: (~r1_tarski(B_144, '#skF_1'(A_145, B_146)) | ~r1_tarski(A_145, B_144) | r1_tarski(A_145, B_146))), inference(resolution, [status(thm)], [c_455, c_58])).
% 48.20/36.46  tff(c_514, plain, (![A_149, B_150]: (~r1_tarski(A_149, k1_xboole_0) | r1_tarski(A_149, B_150))), inference(resolution, [status(thm)], [c_8, c_485])).
% 48.20/36.46  tff(c_528, plain, (![B_26, B_150]: (r1_tarski(k2_relat_1(B_26), B_150) | ~v5_relat_1(B_26, k1_xboole_0) | ~v1_relat_1(B_26))), inference(resolution, [status(thm)], [c_54, c_514])).
% 48.20/36.46  tff(c_1001, plain, (![B_192, A_193]: (r2_hidden(k1_funct_1(B_192, A_193), k2_relat_1(B_192)) | ~r2_hidden(A_193, k1_relat_1(B_192)) | ~v1_funct_1(B_192) | ~v1_relat_1(B_192))), inference(cnfTransformation, [status(thm)], [f_76])).
% 48.20/36.46  tff(c_1163, plain, (![B_213, A_214]: (~r1_tarski(k2_relat_1(B_213), k1_funct_1(B_213, A_214)) | ~r2_hidden(A_214, k1_relat_1(B_213)) | ~v1_funct_1(B_213) | ~v1_relat_1(B_213))), inference(resolution, [status(thm)], [c_1001, c_58])).
% 48.20/36.46  tff(c_1174, plain, (![A_215, B_216]: (~r2_hidden(A_215, k1_relat_1(B_216)) | ~v1_funct_1(B_216) | ~v5_relat_1(B_216, k1_xboole_0) | ~v1_relat_1(B_216))), inference(resolution, [status(thm)], [c_528, c_1163])).
% 48.20/36.46  tff(c_1198, plain, (![B_216]: (~v1_funct_1(B_216) | ~v5_relat_1(B_216, k1_xboole_0) | ~v1_relat_1(B_216) | ~r1_tarski('#skF_6', k1_relat_1(B_216)))), inference(resolution, [status(thm)], [c_234, c_1174])).
% 48.20/36.46  tff(c_1457, plain, (~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', k1_xboole_0) | ~v1_relat_1('#skF_9') | ~r1_tarski('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1449, c_1198])).
% 48.20/36.46  tff(c_1466, plain, (~v5_relat_1('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_208, c_172, c_88, c_1457])).
% 48.20/36.46  tff(c_512, plain, (![A_145, B_146]: (~r1_tarski(A_145, k1_xboole_0) | r1_tarski(A_145, B_146))), inference(resolution, [status(thm)], [c_8, c_485])).
% 48.20/36.46  tff(c_14606, plain, (![B_146]: (r1_tarski(k2_relat_1('#skF_9'), B_146) | '#skF_1'(k2_relat_1('#skF_9'), k1_xboole_0)='#skF_7')), inference(resolution, [status(thm)], [c_14486, c_512])).
% 48.20/36.46  tff(c_15611, plain, ('#skF_1'(k2_relat_1('#skF_9'), k1_xboole_0)='#skF_7'), inference(splitLeft, [status(thm)], [c_14606])).
% 48.20/36.46  tff(c_15639, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_9')) | r1_tarski(k2_relat_1('#skF_9'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15611, c_6])).
% 48.20/36.46  tff(c_16743, plain, (r1_tarski(k2_relat_1('#skF_9'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_15639])).
% 48.20/36.46  tff(c_16752, plain, (v5_relat_1('#skF_9', k1_xboole_0) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_16743, c_52])).
% 48.20/36.46  tff(c_16762, plain, (v5_relat_1('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_172, c_16752])).
% 48.20/36.46  tff(c_16764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1466, c_16762])).
% 48.20/36.46  tff(c_16765, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_15639])).
% 48.20/36.46  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.20/36.46  tff(c_17836, plain, (![B_24520]: (r2_hidden('#skF_7', B_24520) | ~r1_tarski(k2_relat_1('#skF_9'), B_24520))), inference(resolution, [status(thm)], [c_16765, c_2])).
% 48.20/36.46  tff(c_17847, plain, (![A_25]: (r2_hidden('#skF_7', A_25) | ~v5_relat_1('#skF_9', A_25) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_54, c_17836])).
% 48.20/36.46  tff(c_17858, plain, (![A_25]: (r2_hidden('#skF_7', A_25) | ~v5_relat_1('#skF_9', A_25))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_17847])).
% 48.20/36.46  tff(c_41982, plain, (![A_84105]: (r2_hidden('#skF_7', k1_tarski(A_84105)) | A_84105!='#skF_7')), inference(resolution, [status(thm)], [c_41884, c_17858])).
% 48.20/36.46  tff(c_42514, plain, (![B_85332, A_85333]: (r2_hidden('#skF_7', B_85332) | ~r1_tarski(k1_tarski(A_85333), B_85332) | A_85333!='#skF_7')), inference(resolution, [status(thm)], [c_41982, c_2])).
% 48.20/36.46  tff(c_46315, plain, (![B_103398, A_103399]: (r2_hidden('#skF_7', B_103398) | A_103399!='#skF_7' | '#skF_1'(k1_tarski(A_103399), B_103398)=A_103399)), inference(resolution, [status(thm)], [c_198, c_42514])).
% 48.20/36.46  tff(c_49613, plain, (![A_115175, B_115176]: (~r2_hidden(A_115175, B_115176) | r1_tarski(k1_tarski(A_115175), B_115176) | r2_hidden('#skF_7', B_115176) | A_115175!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_46315, c_4])).
% 48.20/36.46  tff(c_42075, plain, (![B_2, A_84105]: (r2_hidden('#skF_7', B_2) | ~r1_tarski(k1_tarski(A_84105), B_2) | A_84105!='#skF_7')), inference(resolution, [status(thm)], [c_41982, c_2])).
% 48.20/36.46  tff(c_49808, plain, (![A_115687, B_115688]: (~r2_hidden(A_115687, B_115688) | r2_hidden('#skF_7', B_115688) | A_115687!='#skF_7')), inference(resolution, [status(thm)], [c_49613, c_42075])).
% 48.20/36.46  tff(c_51753, plain, (![A_121835, B_121836]: (r2_hidden('#skF_7', A_121835) | '#skF_1'(A_121835, B_121836)!='#skF_7' | r1_tarski(A_121835, B_121836))), inference(resolution, [status(thm)], [c_6, c_49808])).
% 48.20/36.46  tff(c_235, plain, (![B_90]: (r2_hidden('#skF_8', B_90) | ~r1_tarski('#skF_6', B_90))), inference(resolution, [status(thm)], [c_82, c_210])).
% 48.20/36.46  tff(c_247, plain, (![A_14]: (A_14='#skF_8' | ~r1_tarski('#skF_6', k1_tarski(A_14)))), inference(resolution, [status(thm)], [c_235, c_34])).
% 48.20/36.46  tff(c_52061, plain, (![A_14]: (A_14='#skF_8' | r2_hidden('#skF_7', '#skF_6') | '#skF_1'('#skF_6', k1_tarski(A_14))!='#skF_7')), inference(resolution, [status(thm)], [c_51753, c_247])).
% 48.20/36.46  tff(c_52081, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_52061])).
% 48.20/36.46  tff(c_35205, plain, (![B_68593, A_68594]: (v5_relat_1('#skF_9', B_68593) | A_68594='#skF_1'(k2_relat_1('#skF_9'), B_68593) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_68594))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_33702])).
% 48.20/36.46  tff(c_192398, plain, (![A_392406, B_392407]: (~r2_hidden(A_392406, B_392407) | r1_tarski(k2_relat_1('#skF_9'), B_392407) | v5_relat_1('#skF_9', B_392407) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_392406))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_35205, c_4])).
% 48.20/36.46  tff(c_192818, plain, (r1_tarski(k2_relat_1('#skF_9'), '#skF_6') | v5_relat_1('#skF_9', '#skF_6') | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_52081, c_192398])).
% 48.20/36.46  tff(c_192855, plain, ('#skF_1'(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))='#skF_7'), inference(splitLeft, [status(thm)], [c_192818])).
% 48.20/36.46  tff(c_192966, plain, (~r2_hidden('#skF_7', k1_tarski('#skF_7')) | r1_tarski(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_192855, c_4])).
% 48.20/36.46  tff(c_193404, plain, (r1_tarski(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_192966])).
% 48.20/36.46  tff(c_480, plain, (![A_141, B_142, B_2, B_143]: (r2_hidden('#skF_1'(A_141, B_142), B_2) | ~r1_tarski(B_143, B_2) | ~r1_tarski(A_141, B_143) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_455, c_2])).
% 48.20/36.46  tff(c_193572, plain, (![A_394346, B_394347]: (r2_hidden('#skF_1'(A_394346, B_394347), k1_tarski('#skF_7')) | ~r1_tarski(A_394346, k2_relat_1('#skF_9')) | r1_tarski(A_394346, B_394347))), inference(resolution, [status(thm)], [c_193404, c_480])).
% 48.20/36.46  tff(c_194739, plain, (![B_120]: (r2_hidden(B_120, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(B_120), k2_relat_1('#skF_9')) | r1_tarski(k1_tarski(B_120), B_120))), inference(superposition, [status(thm), theory('equality')], [c_363, c_193572])).
% 48.20/36.46  tff(c_195327, plain, (![B_396288]: (r2_hidden(B_396288, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(B_396288), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_123, c_194739])).
% 48.20/36.46  tff(c_195440, plain, (![A_396935]: (r2_hidden(A_396935, k1_tarski('#skF_7')) | '#skF_1'(k1_tarski(A_396935), k2_relat_1('#skF_9'))=A_396935)), inference(resolution, [status(thm)], [c_198, c_195327])).
% 48.20/36.46  tff(c_204124, plain, (![A_409238]: (~r2_hidden(A_409238, k2_relat_1('#skF_9')) | r1_tarski(k1_tarski(A_409238), k2_relat_1('#skF_9')) | r2_hidden(A_409238, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_195440, c_4])).
% 48.20/36.46  tff(c_194999, plain, (![B_120]: (r2_hidden(B_120, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(B_120), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_123, c_194739])).
% 48.20/36.46  tff(c_204369, plain, (![A_409885]: (~r2_hidden(A_409885, k2_relat_1('#skF_9')) | r2_hidden(A_409885, k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_204124, c_194999])).
% 48.20/36.46  tff(c_204445, plain, (![A_27]: (r2_hidden(k1_funct_1('#skF_9', A_27), k1_tarski('#skF_7')) | ~r2_hidden(A_27, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_56, c_204369])).
% 48.20/36.46  tff(c_204724, plain, (![A_411183]: (r2_hidden(k1_funct_1('#skF_9', A_411183), k1_tarski('#skF_7')) | ~r2_hidden(A_411183, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_88, c_1449, c_204445])).
% 48.20/36.46  tff(c_204851, plain, (![A_411830]: (k1_funct_1('#skF_9', A_411830)='#skF_7' | ~r2_hidden(A_411830, '#skF_6'))), inference(resolution, [status(thm)], [c_204724, c_34])).
% 48.20/36.46  tff(c_204944, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7' | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_234, c_204851])).
% 48.20/36.46  tff(c_204979, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_208, c_204944])).
% 48.20/36.46  tff(c_204981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_204979])).
% 48.20/36.46  tff(c_204983, plain, ('#skF_1'(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))!='#skF_7'), inference(splitRight, [status(thm)], [c_192818])).
% 48.20/36.46  tff(c_14485, plain, (![B_17777]: ('#skF_1'(k2_relat_1('#skF_9'), B_17777)='#skF_7' | r1_tarski(k2_relat_1('#skF_9'), B_17777))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_14482])).
% 48.20/36.46  tff(c_14605, plain, (![A_14, B_142]: (A_14='#skF_1'(k2_relat_1('#skF_9'), B_142) | r1_tarski(k2_relat_1('#skF_9'), B_142) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_14))='#skF_7')), inference(resolution, [status(thm)], [c_14486, c_483])).
% 48.20/36.46  tff(c_205031, plain, (![A_14]: (A_14!='#skF_7' | r1_tarski(k2_relat_1('#skF_9'), k1_tarski('#skF_7')) | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_14))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14605, c_204983])).
% 48.20/36.46  tff(c_212119, plain, (r1_tarski(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_205031])).
% 48.20/36.46  tff(c_213387, plain, (![A_428015, B_428016]: (r2_hidden('#skF_1'(A_428015, B_428016), k1_tarski('#skF_7')) | ~r1_tarski(A_428015, k2_relat_1('#skF_9')) | r1_tarski(A_428015, B_428016))), inference(resolution, [status(thm)], [c_212119, c_480])).
% 48.20/36.46  tff(c_214559, plain, (![B_120]: (r2_hidden(B_120, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(B_120), k2_relat_1('#skF_9')) | r1_tarski(k1_tarski(B_120), B_120))), inference(superposition, [status(thm), theory('equality')], [c_363, c_213387])).
% 48.20/36.46  tff(c_214975, plain, (![B_429310]: (r2_hidden(B_429310, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(B_429310), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_123, c_214559])).
% 48.20/36.46  tff(c_215088, plain, (![A_429957]: (r2_hidden(A_429957, k1_tarski('#skF_7')) | '#skF_1'(k1_tarski(A_429957), k2_relat_1('#skF_9'))=A_429957)), inference(resolution, [status(thm)], [c_198, c_214975])).
% 48.20/36.46  tff(c_249263, plain, (![A_482405]: (~r2_hidden(A_482405, k2_relat_1('#skF_9')) | r1_tarski(k1_tarski(A_482405), k2_relat_1('#skF_9')) | r2_hidden(A_482405, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_215088, c_4])).
% 48.20/36.46  tff(c_214822, plain, (![B_120]: (r2_hidden(B_120, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(B_120), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_123, c_214559])).
% 48.20/36.46  tff(c_250053, plain, (![A_483702]: (~r2_hidden(A_483702, k2_relat_1('#skF_9')) | r2_hidden(A_483702, k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_249263, c_214822])).
% 48.20/36.46  tff(c_250137, plain, (![A_27]: (r2_hidden(k1_funct_1('#skF_9', A_27), k1_tarski('#skF_7')) | ~r2_hidden(A_27, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_56, c_250053])).
% 48.20/36.46  tff(c_250184, plain, (![A_484349]: (r2_hidden(k1_funct_1('#skF_9', A_484349), k1_tarski('#skF_7')) | ~r2_hidden(A_484349, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_88, c_1449, c_250137])).
% 48.20/36.46  tff(c_250344, plain, (![A_484996]: (k1_funct_1('#skF_9', A_484996)='#skF_7' | ~r2_hidden(A_484996, '#skF_6'))), inference(resolution, [status(thm)], [c_250184, c_34])).
% 48.20/36.46  tff(c_250460, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7' | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_234, c_250344])).
% 48.20/36.46  tff(c_250504, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_208, c_250460])).
% 48.20/36.46  tff(c_250506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_250504])).
% 48.20/36.46  tff(c_250508, plain, (~r1_tarski(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_205031])).
% 48.20/36.46  tff(c_251672, plain, ('#skF_1'(k2_relat_1('#skF_9'), k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_14485, c_250508])).
% 48.20/36.46  tff(c_251700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204983, c_251672])).
% 48.20/36.46  tff(c_251701, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1448])).
% 48.20/36.46  tff(c_251759, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_251701, c_123])).
% 48.20/36.46  tff(c_251783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_251759])).
% 48.20/36.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.20/36.46  
% 48.20/36.46  Inference rules
% 48.20/36.46  ----------------------
% 48.20/36.46  #Ref     : 1
% 48.20/36.46  #Sup     : 40944
% 48.20/36.46  #Fact    : 324
% 48.20/36.46  #Define  : 0
% 48.20/36.46  #Split   : 82
% 48.20/36.46  #Chain   : 0
% 48.20/36.46  #Close   : 0
% 48.20/36.46  
% 48.20/36.46  Ordering : KBO
% 48.20/36.46  
% 48.20/36.46  Simplification rules
% 48.20/36.46  ----------------------
% 48.20/36.46  #Subsume      : 15382
% 48.20/36.46  #Demod        : 5132
% 48.20/36.46  #Tautology    : 6432
% 48.20/36.46  #SimpNegUnit  : 1128
% 48.20/36.46  #BackRed      : 144
% 48.20/36.46  
% 48.20/36.46  #Partial instantiations: 285660
% 48.20/36.46  #Strategies tried      : 1
% 48.20/36.46  
% 48.20/36.46  Timing (in seconds)
% 48.20/36.46  ----------------------
% 48.20/36.46  Preprocessing        : 0.43
% 48.20/36.46  Parsing              : 0.23
% 48.20/36.46  CNF conversion       : 0.03
% 48.20/36.46  Main loop            : 35.11
% 48.20/36.46  Inferencing          : 7.84
% 48.20/36.46  Reduction            : 8.63
% 48.20/36.46  Demodulation         : 5.53
% 48.20/36.46  BG Simplification    : 0.63
% 48.20/36.46  Subsumption          : 16.01
% 48.20/36.46  Abstraction          : 0.97
% 48.20/36.46  MUC search           : 0.00
% 48.20/36.46  Cooper               : 0.00
% 48.20/36.46  Total                : 35.59
% 48.20/36.46  Index Insertion      : 0.00
% 48.20/36.46  Index Deletion       : 0.00
% 48.20/36.46  Index Matching       : 0.00
% 48.20/36.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
