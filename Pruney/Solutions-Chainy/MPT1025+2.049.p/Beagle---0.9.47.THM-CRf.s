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
% DateTime   : Thu Dec  3 10:16:37 EST 2020

% Result     : Theorem 10.17s
% Output     : CNFRefutation 10.17s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 395 expanded)
%              Number of leaves         :   45 ( 151 expanded)
%              Depth                    :   14
%              Number of atoms          :  232 ( 927 expanded)
%              Number of equality atoms :   35 (  99 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_36,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_72,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_177,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_187,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_72,c_177])).

tff(c_194,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_187])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( v1_xboole_0(k2_zfmisc_1(A_15,B_16))
      | ~ v1_xboole_0(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_135,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,B_73)
      | v1_xboole_0(B_73)
      | ~ m1_subset_1(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_147,plain,(
    ! [A_72,A_10] :
      ( r1_tarski(A_72,A_10)
      | v1_xboole_0(k1_zfmisc_1(A_10))
      | ~ m1_subset_1(A_72,k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_135,c_14])).

tff(c_161,plain,(
    ! [A_74,A_75] :
      ( r1_tarski(A_74,A_75)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(A_75)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_147])).

tff(c_176,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_72,c_161])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_260,plain,(
    ! [C_87,B_88,A_89] :
      ( r2_hidden(C_87,B_88)
      | ~ r2_hidden(C_87,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_287,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92),B_93)
      | ~ r1_tarski(A_92,B_93)
      | v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_4,c_260])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_321,plain,(
    ! [B_95,A_96] :
      ( ~ v1_xboole_0(B_95)
      | ~ r1_tarski(A_96,B_95)
      | v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_287,c_2])).

tff(c_336,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_176,c_321])).

tff(c_338,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_342,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_338])).

tff(c_3197,plain,(
    ! [A_412,B_413,C_414,D_415] :
      ( k7_relset_1(A_412,B_413,C_414,D_415) = k9_relat_1(C_414,D_415)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_412,B_413))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3234,plain,(
    ! [D_415] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_415) = k9_relat_1('#skF_9',D_415) ),
    inference(resolution,[status(thm)],[c_72,c_3197])).

tff(c_70,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_99,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_3237,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3234,c_99])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_98,plain,(
    m1_subset_1('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_70,c_30])).

tff(c_3236,plain,(
    m1_subset_1('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3234,c_98])).

tff(c_3238,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3234,c_70])).

tff(c_74,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_348,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_369,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_348])).

tff(c_5170,plain,(
    ! [B_522,A_523,C_524] :
      ( k1_xboole_0 = B_522
      | k1_relset_1(A_523,B_522,C_524) = A_523
      | ~ v1_funct_2(C_524,A_523,B_522)
      | ~ m1_subset_1(C_524,k1_zfmisc_1(k2_zfmisc_1(A_523,B_522))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5205,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_5170])).

tff(c_5218,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_369,c_5205])).

tff(c_5219,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_5218])).

tff(c_44,plain,(
    ! [A_27,B_28,C_29] :
      ( r2_hidden('#skF_5'(A_27,B_28,C_29),k1_relat_1(C_29))
      | ~ r2_hidden(A_27,k9_relat_1(C_29,B_28))
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_5248,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_5'(A_27,B_28,'#skF_9'),'#skF_6')
      | ~ r2_hidden(A_27,k9_relat_1('#skF_9',B_28))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5219,c_44])).

tff(c_5620,plain,(
    ! [A_535,B_536] :
      ( r2_hidden('#skF_5'(A_535,B_536,'#skF_9'),'#skF_6')
      | ~ r2_hidden(A_535,k9_relat_1('#skF_9',B_536)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_5248])).

tff(c_5635,plain,(
    ! [A_537,B_538] :
      ( m1_subset_1('#skF_5'(A_537,B_538,'#skF_9'),'#skF_6')
      | ~ r2_hidden(A_537,k9_relat_1('#skF_9',B_538)) ) ),
    inference(resolution,[status(thm)],[c_5620,c_30])).

tff(c_5688,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_8','#skF_9'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3238,c_5635])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2177,plain,(
    ! [A_297,B_298,C_299] :
      ( r2_hidden('#skF_5'(A_297,B_298,C_299),B_298)
      | ~ r2_hidden(A_297,k9_relat_1(C_299,B_298))
      | ~ v1_relat_1(C_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    ! [F_50] :
      ( k1_funct_1('#skF_9',F_50) != '#skF_10'
      | ~ r2_hidden(F_50,'#skF_8')
      | ~ m1_subset_1(F_50,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2439,plain,(
    ! [A_330,C_331] :
      ( k1_funct_1('#skF_9','#skF_5'(A_330,'#skF_8',C_331)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'(A_330,'#skF_8',C_331),'#skF_6')
      | ~ r2_hidden(A_330,k9_relat_1(C_331,'#skF_8'))
      | ~ v1_relat_1(C_331) ) ),
    inference(resolution,[status(thm)],[c_2177,c_68])).

tff(c_2473,plain,(
    ! [A_20,C_331] :
      ( k1_funct_1('#skF_9','#skF_5'(A_20,'#skF_8',C_331)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'(A_20,'#skF_8',C_331),'#skF_6')
      | ~ v1_relat_1(C_331)
      | v1_xboole_0(k9_relat_1(C_331,'#skF_8'))
      | ~ m1_subset_1(A_20,k9_relat_1(C_331,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_32,c_2439])).

tff(c_5699,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) != '#skF_10'
    | ~ v1_relat_1('#skF_9')
    | v1_xboole_0(k9_relat_1('#skF_9','#skF_8'))
    | ~ m1_subset_1('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_5688,c_2473])).

tff(c_5705,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) != '#skF_10'
    | v1_xboole_0(k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3236,c_194,c_5699])).

tff(c_5706,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_3237,c_5705])).

tff(c_76,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4344,plain,(
    ! [A_479,B_480,C_481] :
      ( r2_hidden(k4_tarski('#skF_5'(A_479,B_480,C_481),A_479),C_481)
      | ~ r2_hidden(A_479,k9_relat_1(C_481,B_480))
      | ~ v1_relat_1(C_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    ! [C_35,A_33,B_34] :
      ( k1_funct_1(C_35,A_33) = B_34
      | ~ r2_hidden(k4_tarski(A_33,B_34),C_35)
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_11043,plain,(
    ! [C_770,A_771,B_772] :
      ( k1_funct_1(C_770,'#skF_5'(A_771,B_772,C_770)) = A_771
      | ~ v1_funct_1(C_770)
      | ~ r2_hidden(A_771,k9_relat_1(C_770,B_772))
      | ~ v1_relat_1(C_770) ) ),
    inference(resolution,[status(thm)],[c_4344,c_48])).

tff(c_11068,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) = '#skF_10'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3238,c_11043])).

tff(c_11103,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_76,c_11068])).

tff(c_11105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5706,c_11103])).

tff(c_11106,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_5218])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11120,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11106,c_12])).

tff(c_11122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_11120])).

tff(c_11123,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_11124,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11304,plain,(
    ! [A_800,B_801,B_802] :
      ( r2_hidden('#skF_2'(A_800,B_801),B_802)
      | ~ r1_tarski(A_800,B_802)
      | r1_tarski(A_800,B_801) ) ),
    inference(resolution,[status(thm)],[c_10,c_260])).

tff(c_11342,plain,(
    ! [B_806,A_807,B_808] :
      ( ~ v1_xboole_0(B_806)
      | ~ r1_tarski(A_807,B_806)
      | r1_tarski(A_807,B_808) ) ),
    inference(resolution,[status(thm)],[c_11304,c_2])).

tff(c_11352,plain,(
    ! [B_808] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | r1_tarski('#skF_9',B_808) ) ),
    inference(resolution,[status(thm)],[c_176,c_11342])).

tff(c_11361,plain,(
    ! [B_808] : r1_tarski('#skF_9',B_808) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11124,c_11352])).

tff(c_195,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_2'(A_78,B_79),A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11201,plain,(
    ! [A_785,B_786] :
      ( r1_tarski('#skF_2'(k1_zfmisc_1(A_785),B_786),A_785)
      | r1_tarski(k1_zfmisc_1(A_785),B_786) ) ),
    inference(resolution,[status(thm)],[c_195,c_14])).

tff(c_308,plain,(
    ! [B_93,A_92] :
      ( ~ v1_xboole_0(B_93)
      | ~ r1_tarski(A_92,B_93)
      | v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_287,c_2])).

tff(c_11571,plain,(
    ! [A_838,B_839] :
      ( ~ v1_xboole_0(A_838)
      | v1_xboole_0('#skF_2'(k1_zfmisc_1(A_838),B_839))
      | r1_tarski(k1_zfmisc_1(A_838),B_839) ) ),
    inference(resolution,[status(thm)],[c_11201,c_308])).

tff(c_218,plain,(
    ! [A_78,B_79] :
      ( ~ v1_xboole_0(A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_195,c_2])).

tff(c_16,plain,(
    ! [C_14,A_10] :
      ( r2_hidden(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_123,plain,(
    ! [A_69,B_70] :
      ( ~ r2_hidden('#skF_2'(A_69,B_70),B_70)
      | r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11193,plain,(
    ! [A_780,A_781] :
      ( r1_tarski(A_780,k1_zfmisc_1(A_781))
      | ~ r1_tarski('#skF_2'(A_780,k1_zfmisc_1(A_781)),A_781) ) ),
    inference(resolution,[status(thm)],[c_16,c_123])).

tff(c_11198,plain,(
    ! [A_780,B_79] :
      ( r1_tarski(A_780,k1_zfmisc_1(B_79))
      | ~ v1_xboole_0('#skF_2'(A_780,k1_zfmisc_1(B_79))) ) ),
    inference(resolution,[status(thm)],[c_218,c_11193])).

tff(c_11593,plain,(
    ! [A_842,B_843] :
      ( ~ v1_xboole_0(A_842)
      | r1_tarski(k1_zfmisc_1(A_842),k1_zfmisc_1(B_843)) ) ),
    inference(resolution,[status(thm)],[c_11571,c_11198])).

tff(c_273,plain,(
    ! [C_14,B_88,A_10] :
      ( r2_hidden(C_14,B_88)
      | ~ r1_tarski(k1_zfmisc_1(A_10),B_88)
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_260])).

tff(c_11617,plain,(
    ! [C_847,B_848,A_849] :
      ( r2_hidden(C_847,k1_zfmisc_1(B_848))
      | ~ r1_tarski(C_847,A_849)
      | ~ v1_xboole_0(A_849) ) ),
    inference(resolution,[status(thm)],[c_11593,c_273])).

tff(c_11639,plain,(
    ! [B_848,B_808] :
      ( r2_hidden('#skF_9',k1_zfmisc_1(B_848))
      | ~ v1_xboole_0(B_808) ) ),
    inference(resolution,[status(thm)],[c_11361,c_11617])).

tff(c_11645,plain,(
    ! [B_808] : ~ v1_xboole_0(B_808) ),
    inference(splitLeft,[status(thm)],[c_11639])).

tff(c_11663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11645,c_11124])).

tff(c_11665,plain,(
    ! [B_850] : r2_hidden('#skF_9',k1_zfmisc_1(B_850)) ),
    inference(splitRight,[status(thm)],[c_11639])).

tff(c_11680,plain,(
    ! [B_850] : m1_subset_1('#skF_9',k1_zfmisc_1(B_850)) ),
    inference(resolution,[status(thm)],[c_11665,c_30])).

tff(c_12519,plain,(
    ! [A_929,B_930,C_931,D_932] :
      ( k7_relset_1(A_929,B_930,C_931,D_932) = k9_relat_1(C_931,D_932)
      | ~ m1_subset_1(C_931,k1_zfmisc_1(k2_zfmisc_1(A_929,B_930))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_12546,plain,(
    ! [A_929,B_930,D_932] : k7_relset_1(A_929,B_930,'#skF_9',D_932) = k9_relat_1('#skF_9',D_932) ),
    inference(resolution,[status(thm)],[c_11680,c_12519])).

tff(c_12629,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12546,c_70])).

tff(c_13103,plain,(
    ! [A_954,B_955,C_956] :
      ( r2_hidden(k4_tarski('#skF_5'(A_954,B_955,C_956),A_954),C_956)
      | ~ r2_hidden(A_954,k9_relat_1(C_956,B_955))
      | ~ v1_relat_1(C_956) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_13462,plain,(
    ! [C_970,A_971,B_972] :
      ( ~ v1_xboole_0(C_970)
      | ~ r2_hidden(A_971,k9_relat_1(C_970,B_972))
      | ~ v1_relat_1(C_970) ) ),
    inference(resolution,[status(thm)],[c_13103,c_2])).

tff(c_13469,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_12629,c_13462])).

tff(c_13502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_11123,c_13469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.17/3.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.17/3.62  
% 10.17/3.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.17/3.63  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 10.17/3.63  
% 10.17/3.63  %Foreground sorts:
% 10.17/3.63  
% 10.17/3.63  
% 10.17/3.63  %Background operators:
% 10.17/3.63  
% 10.17/3.63  
% 10.17/3.63  %Foreground operators:
% 10.17/3.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.17/3.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.17/3.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.17/3.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.17/3.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.17/3.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.17/3.63  tff('#skF_7', type, '#skF_7': $i).
% 10.17/3.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.17/3.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.17/3.63  tff('#skF_10', type, '#skF_10': $i).
% 10.17/3.63  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 10.17/3.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.17/3.63  tff('#skF_6', type, '#skF_6': $i).
% 10.17/3.63  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.17/3.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.17/3.63  tff('#skF_9', type, '#skF_9': $i).
% 10.17/3.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.17/3.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.17/3.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.17/3.63  tff('#skF_8', type, '#skF_8': $i).
% 10.17/3.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.17/3.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.17/3.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.17/3.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.17/3.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.17/3.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.17/3.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.17/3.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.17/3.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.17/3.63  
% 10.17/3.65  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.17/3.65  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 10.17/3.65  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.17/3.65  tff(f_50, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 10.17/3.65  tff(f_53, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 10.17/3.65  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 10.17/3.65  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 10.17/3.65  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.17/3.65  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.17/3.65  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 10.17/3.65  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 10.17/3.65  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.17/3.65  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.17/3.65  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 10.17/3.65  tff(f_93, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 10.17/3.65  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.17/3.65  tff(c_36, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.17/3.65  tff(c_72, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.17/3.65  tff(c_177, plain, (![B_76, A_77]: (v1_relat_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.17/3.65  tff(c_187, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_177])).
% 10.17/3.65  tff(c_194, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_187])).
% 10.17/3.65  tff(c_26, plain, (![A_15, B_16]: (v1_xboole_0(k2_zfmisc_1(A_15, B_16)) | ~v1_xboole_0(B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.17/3.65  tff(c_28, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.17/3.65  tff(c_135, plain, (![A_72, B_73]: (r2_hidden(A_72, B_73) | v1_xboole_0(B_73) | ~m1_subset_1(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.17/3.65  tff(c_14, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.17/3.65  tff(c_147, plain, (![A_72, A_10]: (r1_tarski(A_72, A_10) | v1_xboole_0(k1_zfmisc_1(A_10)) | ~m1_subset_1(A_72, k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_135, c_14])).
% 10.17/3.65  tff(c_161, plain, (![A_74, A_75]: (r1_tarski(A_74, A_75) | ~m1_subset_1(A_74, k1_zfmisc_1(A_75)))), inference(negUnitSimplification, [status(thm)], [c_28, c_147])).
% 10.17/3.65  tff(c_176, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_161])).
% 10.17/3.65  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.17/3.65  tff(c_260, plain, (![C_87, B_88, A_89]: (r2_hidden(C_87, B_88) | ~r2_hidden(C_87, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.17/3.65  tff(c_287, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92), B_93) | ~r1_tarski(A_92, B_93) | v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_4, c_260])).
% 10.17/3.65  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.17/3.65  tff(c_321, plain, (![B_95, A_96]: (~v1_xboole_0(B_95) | ~r1_tarski(A_96, B_95) | v1_xboole_0(A_96))), inference(resolution, [status(thm)], [c_287, c_2])).
% 10.17/3.65  tff(c_336, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7')) | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_176, c_321])).
% 10.17/3.65  tff(c_338, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_336])).
% 10.17/3.65  tff(c_342, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_26, c_338])).
% 10.17/3.65  tff(c_3197, plain, (![A_412, B_413, C_414, D_415]: (k7_relset_1(A_412, B_413, C_414, D_415)=k9_relat_1(C_414, D_415) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_412, B_413))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.17/3.65  tff(c_3234, plain, (![D_415]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_415)=k9_relat_1('#skF_9', D_415))), inference(resolution, [status(thm)], [c_72, c_3197])).
% 10.17/3.65  tff(c_70, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.17/3.65  tff(c_99, plain, (~v1_xboole_0(k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_70, c_2])).
% 10.17/3.65  tff(c_3237, plain, (~v1_xboole_0(k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3234, c_99])).
% 10.17/3.65  tff(c_30, plain, (![A_18, B_19]: (m1_subset_1(A_18, B_19) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.17/3.65  tff(c_98, plain, (m1_subset_1('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_70, c_30])).
% 10.17/3.65  tff(c_3236, plain, (m1_subset_1('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3234, c_98])).
% 10.17/3.65  tff(c_3238, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3234, c_70])).
% 10.17/3.65  tff(c_74, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.17/3.65  tff(c_348, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.17/3.65  tff(c_369, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_72, c_348])).
% 10.17/3.65  tff(c_5170, plain, (![B_522, A_523, C_524]: (k1_xboole_0=B_522 | k1_relset_1(A_523, B_522, C_524)=A_523 | ~v1_funct_2(C_524, A_523, B_522) | ~m1_subset_1(C_524, k1_zfmisc_1(k2_zfmisc_1(A_523, B_522))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.17/3.65  tff(c_5205, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_72, c_5170])).
% 10.17/3.65  tff(c_5218, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_369, c_5205])).
% 10.17/3.65  tff(c_5219, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_5218])).
% 10.17/3.65  tff(c_44, plain, (![A_27, B_28, C_29]: (r2_hidden('#skF_5'(A_27, B_28, C_29), k1_relat_1(C_29)) | ~r2_hidden(A_27, k9_relat_1(C_29, B_28)) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.17/3.65  tff(c_5248, plain, (![A_27, B_28]: (r2_hidden('#skF_5'(A_27, B_28, '#skF_9'), '#skF_6') | ~r2_hidden(A_27, k9_relat_1('#skF_9', B_28)) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5219, c_44])).
% 10.17/3.65  tff(c_5620, plain, (![A_535, B_536]: (r2_hidden('#skF_5'(A_535, B_536, '#skF_9'), '#skF_6') | ~r2_hidden(A_535, k9_relat_1('#skF_9', B_536)))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_5248])).
% 10.17/3.65  tff(c_5635, plain, (![A_537, B_538]: (m1_subset_1('#skF_5'(A_537, B_538, '#skF_9'), '#skF_6') | ~r2_hidden(A_537, k9_relat_1('#skF_9', B_538)))), inference(resolution, [status(thm)], [c_5620, c_30])).
% 10.17/3.65  tff(c_5688, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_8', '#skF_9'), '#skF_6')), inference(resolution, [status(thm)], [c_3238, c_5635])).
% 10.17/3.65  tff(c_32, plain, (![A_20, B_21]: (r2_hidden(A_20, B_21) | v1_xboole_0(B_21) | ~m1_subset_1(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.17/3.65  tff(c_2177, plain, (![A_297, B_298, C_299]: (r2_hidden('#skF_5'(A_297, B_298, C_299), B_298) | ~r2_hidden(A_297, k9_relat_1(C_299, B_298)) | ~v1_relat_1(C_299))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.17/3.65  tff(c_68, plain, (![F_50]: (k1_funct_1('#skF_9', F_50)!='#skF_10' | ~r2_hidden(F_50, '#skF_8') | ~m1_subset_1(F_50, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.17/3.65  tff(c_2439, plain, (![A_330, C_331]: (k1_funct_1('#skF_9', '#skF_5'(A_330, '#skF_8', C_331))!='#skF_10' | ~m1_subset_1('#skF_5'(A_330, '#skF_8', C_331), '#skF_6') | ~r2_hidden(A_330, k9_relat_1(C_331, '#skF_8')) | ~v1_relat_1(C_331))), inference(resolution, [status(thm)], [c_2177, c_68])).
% 10.17/3.65  tff(c_2473, plain, (![A_20, C_331]: (k1_funct_1('#skF_9', '#skF_5'(A_20, '#skF_8', C_331))!='#skF_10' | ~m1_subset_1('#skF_5'(A_20, '#skF_8', C_331), '#skF_6') | ~v1_relat_1(C_331) | v1_xboole_0(k9_relat_1(C_331, '#skF_8')) | ~m1_subset_1(A_20, k9_relat_1(C_331, '#skF_8')))), inference(resolution, [status(thm)], [c_32, c_2439])).
% 10.17/3.65  tff(c_5699, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10' | ~v1_relat_1('#skF_9') | v1_xboole_0(k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_5688, c_2473])).
% 10.17/3.65  tff(c_5705, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10' | v1_xboole_0(k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3236, c_194, c_5699])).
% 10.17/3.65  tff(c_5706, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_3237, c_5705])).
% 10.17/3.65  tff(c_76, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.17/3.65  tff(c_4344, plain, (![A_479, B_480, C_481]: (r2_hidden(k4_tarski('#skF_5'(A_479, B_480, C_481), A_479), C_481) | ~r2_hidden(A_479, k9_relat_1(C_481, B_480)) | ~v1_relat_1(C_481))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.17/3.65  tff(c_48, plain, (![C_35, A_33, B_34]: (k1_funct_1(C_35, A_33)=B_34 | ~r2_hidden(k4_tarski(A_33, B_34), C_35) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.17/3.65  tff(c_11043, plain, (![C_770, A_771, B_772]: (k1_funct_1(C_770, '#skF_5'(A_771, B_772, C_770))=A_771 | ~v1_funct_1(C_770) | ~r2_hidden(A_771, k9_relat_1(C_770, B_772)) | ~v1_relat_1(C_770))), inference(resolution, [status(thm)], [c_4344, c_48])).
% 10.17/3.65  tff(c_11068, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))='#skF_10' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_3238, c_11043])).
% 10.17/3.65  tff(c_11103, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_76, c_11068])).
% 10.17/3.65  tff(c_11105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5706, c_11103])).
% 10.17/3.65  tff(c_11106, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_5218])).
% 10.17/3.65  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.17/3.65  tff(c_11120, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11106, c_12])).
% 10.17/3.65  tff(c_11122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_11120])).
% 10.17/3.65  tff(c_11123, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_336])).
% 10.17/3.65  tff(c_11124, plain, (v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_336])).
% 10.17/3.65  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.17/3.65  tff(c_11304, plain, (![A_800, B_801, B_802]: (r2_hidden('#skF_2'(A_800, B_801), B_802) | ~r1_tarski(A_800, B_802) | r1_tarski(A_800, B_801))), inference(resolution, [status(thm)], [c_10, c_260])).
% 10.17/3.65  tff(c_11342, plain, (![B_806, A_807, B_808]: (~v1_xboole_0(B_806) | ~r1_tarski(A_807, B_806) | r1_tarski(A_807, B_808))), inference(resolution, [status(thm)], [c_11304, c_2])).
% 10.17/3.65  tff(c_11352, plain, (![B_808]: (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7')) | r1_tarski('#skF_9', B_808))), inference(resolution, [status(thm)], [c_176, c_11342])).
% 10.17/3.65  tff(c_11361, plain, (![B_808]: (r1_tarski('#skF_9', B_808))), inference(demodulation, [status(thm), theory('equality')], [c_11124, c_11352])).
% 10.17/3.65  tff(c_195, plain, (![A_78, B_79]: (r2_hidden('#skF_2'(A_78, B_79), A_78) | r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.17/3.65  tff(c_11201, plain, (![A_785, B_786]: (r1_tarski('#skF_2'(k1_zfmisc_1(A_785), B_786), A_785) | r1_tarski(k1_zfmisc_1(A_785), B_786))), inference(resolution, [status(thm)], [c_195, c_14])).
% 10.17/3.65  tff(c_308, plain, (![B_93, A_92]: (~v1_xboole_0(B_93) | ~r1_tarski(A_92, B_93) | v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_287, c_2])).
% 10.17/3.65  tff(c_11571, plain, (![A_838, B_839]: (~v1_xboole_0(A_838) | v1_xboole_0('#skF_2'(k1_zfmisc_1(A_838), B_839)) | r1_tarski(k1_zfmisc_1(A_838), B_839))), inference(resolution, [status(thm)], [c_11201, c_308])).
% 10.17/3.65  tff(c_218, plain, (![A_78, B_79]: (~v1_xboole_0(A_78) | r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_195, c_2])).
% 10.17/3.65  tff(c_16, plain, (![C_14, A_10]: (r2_hidden(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.17/3.65  tff(c_123, plain, (![A_69, B_70]: (~r2_hidden('#skF_2'(A_69, B_70), B_70) | r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.17/3.65  tff(c_11193, plain, (![A_780, A_781]: (r1_tarski(A_780, k1_zfmisc_1(A_781)) | ~r1_tarski('#skF_2'(A_780, k1_zfmisc_1(A_781)), A_781))), inference(resolution, [status(thm)], [c_16, c_123])).
% 10.17/3.65  tff(c_11198, plain, (![A_780, B_79]: (r1_tarski(A_780, k1_zfmisc_1(B_79)) | ~v1_xboole_0('#skF_2'(A_780, k1_zfmisc_1(B_79))))), inference(resolution, [status(thm)], [c_218, c_11193])).
% 10.17/3.65  tff(c_11593, plain, (![A_842, B_843]: (~v1_xboole_0(A_842) | r1_tarski(k1_zfmisc_1(A_842), k1_zfmisc_1(B_843)))), inference(resolution, [status(thm)], [c_11571, c_11198])).
% 10.17/3.65  tff(c_273, plain, (![C_14, B_88, A_10]: (r2_hidden(C_14, B_88) | ~r1_tarski(k1_zfmisc_1(A_10), B_88) | ~r1_tarski(C_14, A_10))), inference(resolution, [status(thm)], [c_16, c_260])).
% 10.17/3.65  tff(c_11617, plain, (![C_847, B_848, A_849]: (r2_hidden(C_847, k1_zfmisc_1(B_848)) | ~r1_tarski(C_847, A_849) | ~v1_xboole_0(A_849))), inference(resolution, [status(thm)], [c_11593, c_273])).
% 10.17/3.65  tff(c_11639, plain, (![B_848, B_808]: (r2_hidden('#skF_9', k1_zfmisc_1(B_848)) | ~v1_xboole_0(B_808))), inference(resolution, [status(thm)], [c_11361, c_11617])).
% 10.17/3.65  tff(c_11645, plain, (![B_808]: (~v1_xboole_0(B_808))), inference(splitLeft, [status(thm)], [c_11639])).
% 10.17/3.65  tff(c_11663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11645, c_11124])).
% 10.17/3.65  tff(c_11665, plain, (![B_850]: (r2_hidden('#skF_9', k1_zfmisc_1(B_850)))), inference(splitRight, [status(thm)], [c_11639])).
% 10.17/3.65  tff(c_11680, plain, (![B_850]: (m1_subset_1('#skF_9', k1_zfmisc_1(B_850)))), inference(resolution, [status(thm)], [c_11665, c_30])).
% 10.17/3.65  tff(c_12519, plain, (![A_929, B_930, C_931, D_932]: (k7_relset_1(A_929, B_930, C_931, D_932)=k9_relat_1(C_931, D_932) | ~m1_subset_1(C_931, k1_zfmisc_1(k2_zfmisc_1(A_929, B_930))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.17/3.65  tff(c_12546, plain, (![A_929, B_930, D_932]: (k7_relset_1(A_929, B_930, '#skF_9', D_932)=k9_relat_1('#skF_9', D_932))), inference(resolution, [status(thm)], [c_11680, c_12519])).
% 10.17/3.65  tff(c_12629, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_12546, c_70])).
% 10.17/3.65  tff(c_13103, plain, (![A_954, B_955, C_956]: (r2_hidden(k4_tarski('#skF_5'(A_954, B_955, C_956), A_954), C_956) | ~r2_hidden(A_954, k9_relat_1(C_956, B_955)) | ~v1_relat_1(C_956))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.17/3.65  tff(c_13462, plain, (![C_970, A_971, B_972]: (~v1_xboole_0(C_970) | ~r2_hidden(A_971, k9_relat_1(C_970, B_972)) | ~v1_relat_1(C_970))), inference(resolution, [status(thm)], [c_13103, c_2])).
% 10.17/3.65  tff(c_13469, plain, (~v1_xboole_0('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_12629, c_13462])).
% 10.17/3.65  tff(c_13502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_11123, c_13469])).
% 10.17/3.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.17/3.65  
% 10.17/3.65  Inference rules
% 10.17/3.65  ----------------------
% 10.17/3.65  #Ref     : 0
% 10.17/3.65  #Sup     : 2916
% 10.17/3.65  #Fact    : 0
% 10.17/3.65  #Define  : 0
% 10.17/3.65  #Split   : 43
% 10.17/3.65  #Chain   : 0
% 10.17/3.65  #Close   : 0
% 10.17/3.65  
% 10.17/3.65  Ordering : KBO
% 10.17/3.65  
% 10.17/3.65  Simplification rules
% 10.17/3.65  ----------------------
% 10.17/3.65  #Subsume      : 1463
% 10.17/3.65  #Demod        : 247
% 10.17/3.65  #Tautology    : 190
% 10.17/3.65  #SimpNegUnit  : 440
% 10.17/3.65  #BackRed      : 217
% 10.17/3.65  
% 10.17/3.65  #Partial instantiations: 0
% 10.17/3.65  #Strategies tried      : 1
% 10.17/3.65  
% 10.17/3.65  Timing (in seconds)
% 10.17/3.65  ----------------------
% 10.17/3.65  Preprocessing        : 0.36
% 10.17/3.65  Parsing              : 0.18
% 10.17/3.65  CNF conversion       : 0.03
% 10.17/3.65  Main loop            : 2.50
% 10.17/3.65  Inferencing          : 0.75
% 10.17/3.65  Reduction            : 0.67
% 10.17/3.65  Demodulation         : 0.40
% 10.17/3.65  BG Simplification    : 0.08
% 10.17/3.65  Subsumption          : 0.80
% 10.17/3.65  Abstraction          : 0.11
% 10.17/3.65  MUC search           : 0.00
% 10.17/3.65  Cooper               : 0.00
% 10.17/3.65  Total                : 2.91
% 10.17/3.65  Index Insertion      : 0.00
% 10.17/3.65  Index Deletion       : 0.00
% 10.17/3.65  Index Matching       : 0.00
% 10.17/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
