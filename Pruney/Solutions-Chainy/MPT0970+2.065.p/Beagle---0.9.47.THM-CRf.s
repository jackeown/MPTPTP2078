%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:28 EST 2020

% Result     : Theorem 7.10s
% Output     : CNFRefutation 7.10s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 229 expanded)
%              Number of leaves         :   46 ( 100 expanded)
%              Depth                    :   14
%              Number of atoms          :  174 ( 544 expanded)
%              Number of equality atoms :   42 ( 135 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_15 > #skF_14 > #skF_13 > #skF_5 > #skF_11 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_78,plain,(
    m1_subset_1('#skF_14',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_13'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_239,plain,(
    ! [A_145,B_146,C_147] :
      ( k2_relset_1(A_145,B_146,C_147) = k2_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_248,plain,(
    k2_relset_1('#skF_12','#skF_13','#skF_14') = k2_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_78,c_239])).

tff(c_76,plain,(
    k2_relset_1('#skF_12','#skF_13','#skF_14') != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_249,plain,(
    k2_relat_1('#skF_14') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_76])).

tff(c_154,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_1'(A_122,B_123),A_122)
      | r1_tarski(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_162,plain,(
    ! [A_122] : r1_tarski(A_122,A_122) ),
    inference(resolution,[status(thm)],[c_154,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    v1_funct_2('#skF_14','#skF_12','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_305,plain,(
    ! [A_160,B_161,C_162] :
      ( k1_relset_1(A_160,B_161,C_162) = k1_relat_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_314,plain,(
    k1_relset_1('#skF_12','#skF_13','#skF_14') = k1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_78,c_305])).

tff(c_741,plain,(
    ! [B_230,A_231,C_232] :
      ( k1_xboole_0 = B_230
      | k1_relset_1(A_231,B_230,C_232) = A_231
      | ~ v1_funct_2(C_232,A_231,B_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_231,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_748,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_relset_1('#skF_12','#skF_13','#skF_14') = '#skF_12'
    | ~ v1_funct_2('#skF_14','#skF_12','#skF_13') ),
    inference(resolution,[status(thm)],[c_78,c_741])).

tff(c_752,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_relat_1('#skF_14') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_314,c_748])).

tff(c_753,plain,(
    k1_relat_1('#skF_14') = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_752])).

tff(c_86,plain,(
    ! [D_100] :
      ( r2_hidden('#skF_15'(D_100),'#skF_12')
      | ~ r2_hidden(D_100,'#skF_13') ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_177,plain,(
    ! [C_130,B_131,A_132] :
      ( r2_hidden(C_130,B_131)
      | ~ r2_hidden(C_130,A_132)
      | ~ r1_tarski(A_132,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_183,plain,(
    ! [D_100,B_131] :
      ( r2_hidden('#skF_15'(D_100),B_131)
      | ~ r1_tarski('#skF_12',B_131)
      | ~ r2_hidden(D_100,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_86,c_177])).

tff(c_28,plain,(
    ! [A_31,B_32] : v1_relat_1(k2_zfmisc_1(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_114,plain,(
    ! [B_113,A_114] :
      ( v1_relat_1(B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_114))
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_120,plain,
    ( v1_relat_1('#skF_14')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_78,c_114])).

tff(c_124,plain,(
    v1_relat_1('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_120])).

tff(c_82,plain,(
    v1_funct_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_84,plain,(
    ! [D_100] :
      ( k1_funct_1('#skF_14','#skF_15'(D_100)) = D_100
      | ~ r2_hidden(D_100,'#skF_13') ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_441,plain,(
    ! [A_182,D_183] :
      ( r2_hidden(k1_funct_1(A_182,D_183),k2_relat_1(A_182))
      | ~ r2_hidden(D_183,k1_relat_1(A_182))
      | ~ v1_funct_1(A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_449,plain,(
    ! [D_100] :
      ( r2_hidden(D_100,k2_relat_1('#skF_14'))
      | ~ r2_hidden('#skF_15'(D_100),k1_relat_1('#skF_14'))
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14')
      | ~ r2_hidden(D_100,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_441])).

tff(c_460,plain,(
    ! [D_184] :
      ( r2_hidden(D_184,k2_relat_1('#skF_14'))
      | ~ r2_hidden('#skF_15'(D_184),k1_relat_1('#skF_14'))
      | ~ r2_hidden(D_184,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_82,c_449])).

tff(c_465,plain,(
    ! [D_100] :
      ( r2_hidden(D_100,k2_relat_1('#skF_14'))
      | ~ r1_tarski('#skF_12',k1_relat_1('#skF_14'))
      | ~ r2_hidden(D_100,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_183,c_460])).

tff(c_466,plain,(
    ~ r1_tarski('#skF_12',k1_relat_1('#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_465])).

tff(c_755,plain,(
    ~ r1_tarski('#skF_12','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_466])).

tff(c_760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_755])).

tff(c_761,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_672,plain,(
    ! [A_220,B_221,C_222] :
      ( r2_hidden('#skF_10'(A_220,B_221,C_222),B_221)
      | k2_relset_1(A_220,B_221,C_222) = B_221
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_677,plain,
    ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),'#skF_13')
    | k2_relset_1('#skF_12','#skF_13','#skF_14') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_78,c_672])).

tff(c_680,plain,
    ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),'#skF_13')
    | k2_relat_1('#skF_14') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_677])).

tff(c_681,plain,(
    r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_680])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_689,plain,(
    ! [B_223] :
      ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),B_223)
      | ~ r1_tarski('#skF_13',B_223) ) ),
    inference(resolution,[status(thm)],[c_681,c_2])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_354,plain,(
    ! [A_172,C_173] :
      ( r2_hidden(k4_tarski('#skF_5'(A_172,k2_relat_1(A_172),C_173),C_173),A_172)
      | ~ r2_hidden(C_173,k2_relat_1(A_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_365,plain,(
    ! [C_173] :
      ( r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0,C_173),C_173),k1_xboole_0)
      | ~ r2_hidden(C_173,k2_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_354])).

tff(c_370,plain,(
    ! [C_174] :
      ( r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0,C_174),C_174),k1_xboole_0)
      | ~ r2_hidden(C_174,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_365])).

tff(c_52,plain,(
    ! [B_74,A_73] :
      ( ~ r1_tarski(B_74,A_73)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_378,plain,(
    ! [C_174] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0,C_174),C_174))
      | ~ r2_hidden(C_174,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_370,c_52])).

tff(c_386,plain,(
    ! [C_174] : ~ r2_hidden(C_174,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_378])).

tff(c_699,plain,(
    ~ r1_tarski('#skF_13',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_689,c_386])).

tff(c_765,plain,(
    ~ r1_tarski('#skF_13','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_699])).

tff(c_788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_765])).

tff(c_801,plain,(
    ! [D_233] :
      ( r2_hidden(D_233,k2_relat_1('#skF_14'))
      | ~ r2_hidden(D_233,'#skF_13') ) ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_850,plain,(
    ! [A_241] :
      ( r1_tarski(A_241,k2_relat_1('#skF_14'))
      | ~ r2_hidden('#skF_1'(A_241,k2_relat_1('#skF_14')),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_801,c_4])).

tff(c_860,plain,(
    r1_tarski('#skF_13',k2_relat_1('#skF_14')) ),
    inference(resolution,[status(thm)],[c_6,c_850])).

tff(c_1155,plain,(
    ! [A_275,B_276,C_277] :
      ( r2_hidden('#skF_10'(A_275,B_276,C_277),B_276)
      | k2_relset_1(A_275,B_276,C_277) = B_276
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1160,plain,
    ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),'#skF_13')
    | k2_relset_1('#skF_12','#skF_13','#skF_14') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_78,c_1155])).

tff(c_1163,plain,
    ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),'#skF_13')
    | k2_relat_1('#skF_14') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_1160])).

tff(c_1164,plain,(
    r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_1163])).

tff(c_1172,plain,(
    ! [B_278] :
      ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),B_278)
      | ~ r1_tarski('#skF_13',B_278) ) ),
    inference(resolution,[status(thm)],[c_1164,c_2])).

tff(c_1208,plain,(
    ! [B_281,B_282] :
      ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),B_281)
      | ~ r1_tarski(B_282,B_281)
      | ~ r1_tarski('#skF_13',B_282) ) ),
    inference(resolution,[status(thm)],[c_1172,c_2])).

tff(c_1216,plain,
    ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),k2_relat_1('#skF_14'))
    | ~ r1_tarski('#skF_13','#skF_13') ),
    inference(resolution,[status(thm)],[c_860,c_1208])).

tff(c_1230,plain,(
    r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),k2_relat_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_1216])).

tff(c_1240,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_14'),B_2) ) ),
    inference(resolution,[status(thm)],[c_1230,c_2])).

tff(c_16,plain,(
    ! [A_12,C_27] :
      ( r2_hidden(k4_tarski('#skF_5'(A_12,k2_relat_1(A_12),C_27),C_27),A_12)
      | ~ r2_hidden(C_27,k2_relat_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1779,plain,(
    ! [E_339,A_340,B_341,C_342] :
      ( ~ r2_hidden(k4_tarski(E_339,'#skF_10'(A_340,B_341,C_342)),C_342)
      | k2_relset_1(A_340,B_341,C_342) = B_341
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k2_zfmisc_1(A_340,B_341))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6881,plain,(
    ! [A_490,B_491,A_492] :
      ( k2_relset_1(A_490,B_491,A_492) = B_491
      | ~ m1_subset_1(A_492,k1_zfmisc_1(k2_zfmisc_1(A_490,B_491)))
      | ~ r2_hidden('#skF_10'(A_490,B_491,A_492),k2_relat_1(A_492)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1779])).

tff(c_6904,plain,
    ( k2_relset_1('#skF_12','#skF_13','#skF_14') = '#skF_13'
    | ~ m1_subset_1('#skF_14',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_13')))
    | ~ r1_tarski(k2_relat_1('#skF_14'),k2_relat_1('#skF_14')) ),
    inference(resolution,[status(thm)],[c_1240,c_6881])).

tff(c_6927,plain,(
    k2_relat_1('#skF_14') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_78,c_248,c_6904])).

tff(c_6929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_6927])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.10/2.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.50  
% 7.10/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.50  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_15 > #skF_14 > #skF_13 > #skF_5 > #skF_11 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4 > #skF_10
% 7.10/2.50  
% 7.10/2.50  %Foreground sorts:
% 7.10/2.50  
% 7.10/2.50  
% 7.10/2.50  %Background operators:
% 7.10/2.50  
% 7.10/2.50  
% 7.10/2.50  %Foreground operators:
% 7.10/2.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.10/2.50  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.10/2.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.10/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.10/2.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.10/2.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.10/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.10/2.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.10/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.10/2.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.10/2.50  tff('#skF_15', type, '#skF_15': $i > $i).
% 7.10/2.50  tff('#skF_14', type, '#skF_14': $i).
% 7.10/2.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.10/2.50  tff('#skF_13', type, '#skF_13': $i).
% 7.10/2.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.10/2.50  tff('#skF_11', type, '#skF_11': ($i * $i * $i * $i) > $i).
% 7.10/2.50  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 7.10/2.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.10/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.10/2.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.10/2.50  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 7.10/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.10/2.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.10/2.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.10/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.10/2.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.10/2.50  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.10/2.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.10/2.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.10/2.50  tff('#skF_12', type, '#skF_12': $i).
% 7.10/2.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.10/2.50  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 7.10/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.10/2.50  
% 7.10/2.52  tff(f_135, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 7.10/2.52  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.10/2.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.10/2.52  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.10/2.52  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.10/2.52  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.10/2.52  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.10/2.52  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 7.10/2.52  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 7.10/2.52  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.10/2.52  tff(f_58, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 7.10/2.52  tff(f_53, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 7.10/2.52  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.10/2.52  tff(c_78, plain, (m1_subset_1('#skF_14', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_13')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.10/2.52  tff(c_239, plain, (![A_145, B_146, C_147]: (k2_relset_1(A_145, B_146, C_147)=k2_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.10/2.52  tff(c_248, plain, (k2_relset_1('#skF_12', '#skF_13', '#skF_14')=k2_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_78, c_239])).
% 7.10/2.52  tff(c_76, plain, (k2_relset_1('#skF_12', '#skF_13', '#skF_14')!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.10/2.52  tff(c_249, plain, (k2_relat_1('#skF_14')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_248, c_76])).
% 7.10/2.52  tff(c_154, plain, (![A_122, B_123]: (r2_hidden('#skF_1'(A_122, B_123), A_122) | r1_tarski(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.52  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.52  tff(c_162, plain, (![A_122]: (r1_tarski(A_122, A_122))), inference(resolution, [status(thm)], [c_154, c_4])).
% 7.10/2.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.52  tff(c_80, plain, (v1_funct_2('#skF_14', '#skF_12', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.10/2.52  tff(c_305, plain, (![A_160, B_161, C_162]: (k1_relset_1(A_160, B_161, C_162)=k1_relat_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.10/2.52  tff(c_314, plain, (k1_relset_1('#skF_12', '#skF_13', '#skF_14')=k1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_78, c_305])).
% 7.10/2.52  tff(c_741, plain, (![B_230, A_231, C_232]: (k1_xboole_0=B_230 | k1_relset_1(A_231, B_230, C_232)=A_231 | ~v1_funct_2(C_232, A_231, B_230) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_231, B_230))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.10/2.52  tff(c_748, plain, (k1_xboole_0='#skF_13' | k1_relset_1('#skF_12', '#skF_13', '#skF_14')='#skF_12' | ~v1_funct_2('#skF_14', '#skF_12', '#skF_13')), inference(resolution, [status(thm)], [c_78, c_741])).
% 7.10/2.52  tff(c_752, plain, (k1_xboole_0='#skF_13' | k1_relat_1('#skF_14')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_314, c_748])).
% 7.10/2.52  tff(c_753, plain, (k1_relat_1('#skF_14')='#skF_12'), inference(splitLeft, [status(thm)], [c_752])).
% 7.10/2.52  tff(c_86, plain, (![D_100]: (r2_hidden('#skF_15'(D_100), '#skF_12') | ~r2_hidden(D_100, '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.10/2.52  tff(c_177, plain, (![C_130, B_131, A_132]: (r2_hidden(C_130, B_131) | ~r2_hidden(C_130, A_132) | ~r1_tarski(A_132, B_131))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.52  tff(c_183, plain, (![D_100, B_131]: (r2_hidden('#skF_15'(D_100), B_131) | ~r1_tarski('#skF_12', B_131) | ~r2_hidden(D_100, '#skF_13'))), inference(resolution, [status(thm)], [c_86, c_177])).
% 7.10/2.52  tff(c_28, plain, (![A_31, B_32]: (v1_relat_1(k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.10/2.52  tff(c_114, plain, (![B_113, A_114]: (v1_relat_1(B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(A_114)) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.10/2.52  tff(c_120, plain, (v1_relat_1('#skF_14') | ~v1_relat_1(k2_zfmisc_1('#skF_12', '#skF_13'))), inference(resolution, [status(thm)], [c_78, c_114])).
% 7.10/2.52  tff(c_124, plain, (v1_relat_1('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_120])).
% 7.10/2.52  tff(c_82, plain, (v1_funct_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.10/2.52  tff(c_84, plain, (![D_100]: (k1_funct_1('#skF_14', '#skF_15'(D_100))=D_100 | ~r2_hidden(D_100, '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.10/2.52  tff(c_441, plain, (![A_182, D_183]: (r2_hidden(k1_funct_1(A_182, D_183), k2_relat_1(A_182)) | ~r2_hidden(D_183, k1_relat_1(A_182)) | ~v1_funct_1(A_182) | ~v1_relat_1(A_182))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.10/2.52  tff(c_449, plain, (![D_100]: (r2_hidden(D_100, k2_relat_1('#skF_14')) | ~r2_hidden('#skF_15'(D_100), k1_relat_1('#skF_14')) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14') | ~r2_hidden(D_100, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_441])).
% 7.10/2.52  tff(c_460, plain, (![D_184]: (r2_hidden(D_184, k2_relat_1('#skF_14')) | ~r2_hidden('#skF_15'(D_184), k1_relat_1('#skF_14')) | ~r2_hidden(D_184, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_82, c_449])).
% 7.10/2.52  tff(c_465, plain, (![D_100]: (r2_hidden(D_100, k2_relat_1('#skF_14')) | ~r1_tarski('#skF_12', k1_relat_1('#skF_14')) | ~r2_hidden(D_100, '#skF_13'))), inference(resolution, [status(thm)], [c_183, c_460])).
% 7.10/2.52  tff(c_466, plain, (~r1_tarski('#skF_12', k1_relat_1('#skF_14'))), inference(splitLeft, [status(thm)], [c_465])).
% 7.10/2.52  tff(c_755, plain, (~r1_tarski('#skF_12', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_753, c_466])).
% 7.10/2.52  tff(c_760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_755])).
% 7.10/2.52  tff(c_761, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_752])).
% 7.10/2.52  tff(c_672, plain, (![A_220, B_221, C_222]: (r2_hidden('#skF_10'(A_220, B_221, C_222), B_221) | k2_relset_1(A_220, B_221, C_222)=B_221 | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.10/2.52  tff(c_677, plain, (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), '#skF_13') | k2_relset_1('#skF_12', '#skF_13', '#skF_14')='#skF_13'), inference(resolution, [status(thm)], [c_78, c_672])).
% 7.10/2.52  tff(c_680, plain, (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), '#skF_13') | k2_relat_1('#skF_14')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_248, c_677])).
% 7.10/2.52  tff(c_681, plain, (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_249, c_680])).
% 7.10/2.52  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.52  tff(c_689, plain, (![B_223]: (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), B_223) | ~r1_tarski('#skF_13', B_223))), inference(resolution, [status(thm)], [c_681, c_2])).
% 7.10/2.52  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.10/2.52  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.10/2.52  tff(c_354, plain, (![A_172, C_173]: (r2_hidden(k4_tarski('#skF_5'(A_172, k2_relat_1(A_172), C_173), C_173), A_172) | ~r2_hidden(C_173, k2_relat_1(A_172)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.10/2.52  tff(c_365, plain, (![C_173]: (r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0, C_173), C_173), k1_xboole_0) | ~r2_hidden(C_173, k2_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_354])).
% 7.10/2.52  tff(c_370, plain, (![C_174]: (r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0, C_174), C_174), k1_xboole_0) | ~r2_hidden(C_174, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_365])).
% 7.10/2.52  tff(c_52, plain, (![B_74, A_73]: (~r1_tarski(B_74, A_73) | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.10/2.52  tff(c_378, plain, (![C_174]: (~r1_tarski(k1_xboole_0, k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0, C_174), C_174)) | ~r2_hidden(C_174, k1_xboole_0))), inference(resolution, [status(thm)], [c_370, c_52])).
% 7.10/2.52  tff(c_386, plain, (![C_174]: (~r2_hidden(C_174, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_378])).
% 7.10/2.52  tff(c_699, plain, (~r1_tarski('#skF_13', k1_xboole_0)), inference(resolution, [status(thm)], [c_689, c_386])).
% 7.10/2.52  tff(c_765, plain, (~r1_tarski('#skF_13', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_761, c_699])).
% 7.10/2.52  tff(c_788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_765])).
% 7.10/2.52  tff(c_801, plain, (![D_233]: (r2_hidden(D_233, k2_relat_1('#skF_14')) | ~r2_hidden(D_233, '#skF_13'))), inference(splitRight, [status(thm)], [c_465])).
% 7.10/2.52  tff(c_850, plain, (![A_241]: (r1_tarski(A_241, k2_relat_1('#skF_14')) | ~r2_hidden('#skF_1'(A_241, k2_relat_1('#skF_14')), '#skF_13'))), inference(resolution, [status(thm)], [c_801, c_4])).
% 7.10/2.52  tff(c_860, plain, (r1_tarski('#skF_13', k2_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_6, c_850])).
% 7.10/2.52  tff(c_1155, plain, (![A_275, B_276, C_277]: (r2_hidden('#skF_10'(A_275, B_276, C_277), B_276) | k2_relset_1(A_275, B_276, C_277)=B_276 | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.10/2.52  tff(c_1160, plain, (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), '#skF_13') | k2_relset_1('#skF_12', '#skF_13', '#skF_14')='#skF_13'), inference(resolution, [status(thm)], [c_78, c_1155])).
% 7.10/2.52  tff(c_1163, plain, (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), '#skF_13') | k2_relat_1('#skF_14')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_248, c_1160])).
% 7.10/2.52  tff(c_1164, plain, (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_249, c_1163])).
% 7.10/2.52  tff(c_1172, plain, (![B_278]: (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), B_278) | ~r1_tarski('#skF_13', B_278))), inference(resolution, [status(thm)], [c_1164, c_2])).
% 7.10/2.52  tff(c_1208, plain, (![B_281, B_282]: (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), B_281) | ~r1_tarski(B_282, B_281) | ~r1_tarski('#skF_13', B_282))), inference(resolution, [status(thm)], [c_1172, c_2])).
% 7.10/2.52  tff(c_1216, plain, (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), k2_relat_1('#skF_14')) | ~r1_tarski('#skF_13', '#skF_13')), inference(resolution, [status(thm)], [c_860, c_1208])).
% 7.10/2.52  tff(c_1230, plain, (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), k2_relat_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_1216])).
% 7.10/2.52  tff(c_1240, plain, (![B_2]: (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), B_2) | ~r1_tarski(k2_relat_1('#skF_14'), B_2))), inference(resolution, [status(thm)], [c_1230, c_2])).
% 7.10/2.52  tff(c_16, plain, (![A_12, C_27]: (r2_hidden(k4_tarski('#skF_5'(A_12, k2_relat_1(A_12), C_27), C_27), A_12) | ~r2_hidden(C_27, k2_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.10/2.52  tff(c_1779, plain, (![E_339, A_340, B_341, C_342]: (~r2_hidden(k4_tarski(E_339, '#skF_10'(A_340, B_341, C_342)), C_342) | k2_relset_1(A_340, B_341, C_342)=B_341 | ~m1_subset_1(C_342, k1_zfmisc_1(k2_zfmisc_1(A_340, B_341))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.10/2.52  tff(c_6881, plain, (![A_490, B_491, A_492]: (k2_relset_1(A_490, B_491, A_492)=B_491 | ~m1_subset_1(A_492, k1_zfmisc_1(k2_zfmisc_1(A_490, B_491))) | ~r2_hidden('#skF_10'(A_490, B_491, A_492), k2_relat_1(A_492)))), inference(resolution, [status(thm)], [c_16, c_1779])).
% 7.10/2.52  tff(c_6904, plain, (k2_relset_1('#skF_12', '#skF_13', '#skF_14')='#skF_13' | ~m1_subset_1('#skF_14', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_13'))) | ~r1_tarski(k2_relat_1('#skF_14'), k2_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_1240, c_6881])).
% 7.10/2.52  tff(c_6927, plain, (k2_relat_1('#skF_14')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_78, c_248, c_6904])).
% 7.10/2.52  tff(c_6929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_6927])).
% 7.10/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.52  
% 7.10/2.52  Inference rules
% 7.10/2.52  ----------------------
% 7.10/2.52  #Ref     : 2
% 7.10/2.52  #Sup     : 1548
% 7.10/2.52  #Fact    : 0
% 7.10/2.52  #Define  : 0
% 7.10/2.52  #Split   : 38
% 7.10/2.52  #Chain   : 0
% 7.10/2.52  #Close   : 0
% 7.10/2.52  
% 7.10/2.52  Ordering : KBO
% 7.10/2.52  
% 7.10/2.52  Simplification rules
% 7.10/2.52  ----------------------
% 7.10/2.52  #Subsume      : 748
% 7.10/2.52  #Demod        : 535
% 7.10/2.52  #Tautology    : 227
% 7.10/2.52  #SimpNegUnit  : 69
% 7.10/2.52  #BackRed      : 86
% 7.10/2.52  
% 7.10/2.52  #Partial instantiations: 0
% 7.10/2.52  #Strategies tried      : 1
% 7.10/2.52  
% 7.10/2.52  Timing (in seconds)
% 7.10/2.52  ----------------------
% 7.10/2.52  Preprocessing        : 0.38
% 7.10/2.52  Parsing              : 0.19
% 7.10/2.52  CNF conversion       : 0.04
% 7.10/2.52  Main loop            : 1.31
% 7.10/2.52  Inferencing          : 0.39
% 7.10/2.52  Reduction            : 0.41
% 7.10/2.52  Demodulation         : 0.26
% 7.10/2.53  BG Simplification    : 0.05
% 7.10/2.53  Subsumption          : 0.36
% 7.10/2.53  Abstraction          : 0.06
% 7.10/2.53  MUC search           : 0.00
% 7.10/2.53  Cooper               : 0.00
% 7.10/2.53  Total                : 1.72
% 7.10/2.53  Index Insertion      : 0.00
% 7.10/2.53  Index Deletion       : 0.00
% 7.10/2.53  Index Matching       : 0.00
% 7.10/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
