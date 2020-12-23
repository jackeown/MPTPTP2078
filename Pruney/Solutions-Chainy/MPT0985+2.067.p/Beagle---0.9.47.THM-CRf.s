%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:36 EST 2020

% Result     : Theorem 17.61s
% Output     : CNFRefutation 17.74s
% Verified   : 
% Statistics : Number of formulae       :  265 (3142 expanded)
%              Number of leaves         :   50 ( 997 expanded)
%              Depth                    :   15
%              Number of atoms          :  411 (8171 expanded)
%              Number of equality atoms :  147 (2750 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v8_relat_2 > v5_ordinal1 > v4_relat_2 > v3_relat_2 > v2_funct_1 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(v3_relat_2,type,(
    v3_relat_2: $i > $o )).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_205,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_176,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_147,axiom,(
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

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_188,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( v1_xboole_0(k2_zfmisc_1(A_9,B_10))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_108,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_116,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_229,plain,(
    ! [A_68] :
      ( v1_funct_1(k2_funct_1(A_68))
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_106,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_206,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_232,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_229,c_206])).

tff(c_235,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_232])).

tff(c_112,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_360,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_370,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_360])).

tff(c_381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_370])).

tff(c_382,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_393,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_475,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_493,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_475])).

tff(c_110,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_1400,plain,(
    ! [A_153,B_154,C_155] :
      ( k2_relset_1(A_153,B_154,C_155) = k2_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1413,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_1400])).

tff(c_1423,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1413])).

tff(c_48,plain,(
    ! [A_25] :
      ( k1_relat_1(k2_funct_1(A_25)) = k2_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    ! [A_24] :
      ( v1_relat_1(k2_funct_1(A_24))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_383,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_1302,plain,(
    ! [A_140] :
      ( k1_relat_1(k2_funct_1(A_140)) = k2_relat_1(A_140)
      | ~ v2_funct_1(A_140)
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_96,plain,(
    ! [A_41] :
      ( v1_funct_2(A_41,k1_relat_1(A_41),k2_relat_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_44852,plain,(
    ! [A_622] :
      ( v1_funct_2(k2_funct_1(A_622),k2_relat_1(A_622),k2_relat_1(k2_funct_1(A_622)))
      | ~ v1_funct_1(k2_funct_1(A_622))
      | ~ v1_relat_1(k2_funct_1(A_622))
      | ~ v2_funct_1(A_622)
      | ~ v1_funct_1(A_622)
      | ~ v1_relat_1(A_622) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1302,c_96])).

tff(c_44894,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1423,c_44852])).

tff(c_44931,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_116,c_110,c_383,c_44894])).

tff(c_46585,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_44931])).

tff(c_46588,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_46585])).

tff(c_46592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_116,c_46588])).

tff(c_46594,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_44931])).

tff(c_38,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_501,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_493,c_38])).

tff(c_503,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_1424,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1423,c_503])).

tff(c_114,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_1704,plain,(
    ! [A_166,B_167,C_168] :
      ( k1_relset_1(A_166,B_167,C_168) = k1_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1737,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_1704])).

tff(c_3310,plain,(
    ! [B_228,A_229,C_230] :
      ( k1_xboole_0 = B_228
      | k1_relset_1(A_229,B_228,C_230) = A_229
      | ~ v1_funct_2(C_230,A_229,B_228)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_229,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_3341,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_3310])).

tff(c_3359,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_1737,c_3341])).

tff(c_3360,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1424,c_3359])).

tff(c_46,plain,(
    ! [A_25] :
      ( k2_relat_1(k2_funct_1(A_25)) = k1_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1602,plain,(
    ! [A_164] :
      ( m1_subset_1(A_164,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_164),k2_relat_1(A_164))))
      | ~ v1_funct_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_55586,plain,(
    ! [A_680] :
      ( m1_subset_1(k2_funct_1(A_680),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_680)),k1_relat_1(A_680))))
      | ~ v1_funct_1(k2_funct_1(A_680))
      | ~ v1_relat_1(k2_funct_1(A_680))
      | ~ v2_funct_1(A_680)
      | ~ v1_funct_1(A_680)
      | ~ v1_relat_1(A_680) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1602])).

tff(c_55624,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3360,c_55586])).

tff(c_55651,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_116,c_110,c_46594,c_383,c_55624])).

tff(c_55679,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_55651])).

tff(c_55695,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_116,c_110,c_1423,c_55679])).

tff(c_55697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_393,c_55695])).

tff(c_55698,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_55713,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55698,c_55698,c_36])).

tff(c_40,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_500,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_493,c_40])).

tff(c_502,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_55700,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55698,c_502])).

tff(c_55757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55713,c_55700])).

tff(c_55758,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_55771,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55758,c_55758,c_34])).

tff(c_56090,plain,(
    ! [A_710,B_711,C_712] :
      ( k2_relset_1(A_710,B_711,C_712) = k2_relat_1(C_712)
      | ~ m1_subset_1(C_712,k1_zfmisc_1(k2_zfmisc_1(A_710,B_711))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_56106,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_56090])).

tff(c_56110,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55771,c_108,c_56106])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55776,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55758,c_6])).

tff(c_56133,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56110,c_55776])).

tff(c_18,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_55770,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55758,c_55758,c_18])).

tff(c_56125,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56110,c_56110,c_55770])).

tff(c_55847,plain,(
    ! [C_691,B_692,A_693] :
      ( ~ v1_xboole_0(C_691)
      | ~ m1_subset_1(B_692,k1_zfmisc_1(C_691))
      | ~ r2_hidden(A_693,B_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_55856,plain,(
    ! [A_693] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_693,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_112,c_55847])).

tff(c_55955,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_55856])).

tff(c_56364,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56125,c_55955])).

tff(c_56367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56133,c_56364])).

tff(c_56369,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_55856])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55769,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55758,c_8])).

tff(c_56392,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56369,c_55769])).

tff(c_56396,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56392,c_112])).

tff(c_57311,plain,(
    ! [A_781,B_782,C_783] :
      ( k2_relset_1(A_781,B_782,C_783) = k2_relat_1(C_783)
      | ~ m1_subset_1(C_783,k1_zfmisc_1(k2_zfmisc_1(A_781,B_782))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_57376,plain,(
    ! [C_788] :
      ( k2_relset_1('#skF_3','#skF_4',C_788) = k2_relat_1(C_788)
      | ~ m1_subset_1(C_788,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56392,c_57311])).

tff(c_57379,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56396,c_57376])).

tff(c_57385,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_55771,c_57379])).

tff(c_57433,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57385,c_493])).

tff(c_57440,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57385,c_116])).

tff(c_20,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_55768,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_5',B_12) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55758,c_55758,c_20])).

tff(c_57425,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_4',B_12) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57385,c_57385,c_55768])).

tff(c_57435,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57385,c_393])).

tff(c_57678,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57425,c_57435])).

tff(c_57439,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57385,c_110])).

tff(c_57436,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57385,c_383])).

tff(c_57423,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57385,c_57385,c_55770])).

tff(c_55772,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55758,c_55758,c_36])).

tff(c_57429,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57385,c_57385,c_55772])).

tff(c_56725,plain,(
    ! [A_750] :
      ( m1_subset_1(A_750,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_750),k2_relat_1(A_750))))
      | ~ v1_funct_1(A_750)
      | ~ v1_relat_1(A_750) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_71572,plain,(
    ! [A_1061] :
      ( m1_subset_1(k2_funct_1(A_1061),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1061)),k1_relat_1(A_1061))))
      | ~ v1_funct_1(k2_funct_1(A_1061))
      | ~ v1_relat_1(k2_funct_1(A_1061))
      | ~ v2_funct_1(A_1061)
      | ~ v1_funct_1(A_1061)
      | ~ v1_relat_1(A_1061) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_56725])).

tff(c_71616,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_57429,c_71572])).

tff(c_71644,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57433,c_57440,c_57439,c_57436,c_57423,c_71616])).

tff(c_71645,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_57678,c_71644])).

tff(c_71648,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_71645])).

tff(c_71652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57433,c_57440,c_71648])).

tff(c_71654,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_74208,plain,(
    ! [B_1202,A_1203] :
      ( v1_xboole_0(B_1202)
      | ~ m1_subset_1(B_1202,k1_zfmisc_1(A_1203))
      | ~ v1_xboole_0(A_1203) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_74222,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_71654,c_74208])).

tff(c_74233,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_74222])).

tff(c_74240,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_74233])).

tff(c_71753,plain,(
    ! [B_1073,A_1074] :
      ( v1_xboole_0(B_1073)
      | ~ m1_subset_1(B_1073,k1_zfmisc_1(A_1074))
      | ~ v1_xboole_0(A_1074) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_71775,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_112,c_71753])).

tff(c_71820,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_71775])).

tff(c_71835,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_71820])).

tff(c_71712,plain,(
    ! [C_1070,A_1071,B_1072] :
      ( v1_relat_1(C_1070)
      | ~ m1_subset_1(C_1070,k1_zfmisc_1(k2_zfmisc_1(A_1071,B_1072))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_71734,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_71712])).

tff(c_72936,plain,(
    ! [A_1143,B_1144,C_1145] :
      ( k2_relset_1(A_1143,B_1144,C_1145) = k2_relat_1(C_1145)
      | ~ m1_subset_1(C_1145,k1_zfmisc_1(k2_zfmisc_1(A_1143,B_1144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_72958,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_72936])).

tff(c_72970,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_72958])).

tff(c_71653,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_72667,plain,(
    ! [A_1130,B_1131,C_1132] :
      ( k1_relset_1(A_1130,B_1131,C_1132) = k1_relat_1(C_1132)
      | ~ m1_subset_1(C_1132,k1_zfmisc_1(k2_zfmisc_1(A_1130,B_1131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_72691,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_71654,c_72667])).

tff(c_73845,plain,(
    ! [B_1183,C_1184,A_1185] :
      ( k1_xboole_0 = B_1183
      | v1_funct_2(C_1184,A_1185,B_1183)
      | k1_relset_1(A_1185,B_1183,C_1184) != A_1185
      | ~ m1_subset_1(C_1184,k1_zfmisc_1(k2_zfmisc_1(A_1185,B_1183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_73870,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_71654,c_73845])).

tff(c_73891,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72691,c_73870])).

tff(c_73892,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_71653,c_73891])).

tff(c_73899,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_73892])).

tff(c_73902,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_73899])).

tff(c_73905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71734,c_116,c_110,c_72970,c_73902])).

tff(c_73906,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_73892])).

tff(c_73968,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73906,c_6])).

tff(c_73972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71835,c_73968])).

tff(c_73973,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_71775])).

tff(c_73984,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_73973,c_8])).

tff(c_73994,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73984,c_73984,c_34])).

tff(c_71741,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_71734,c_38])).

tff(c_71752,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_71741])).

tff(c_73986,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73984,c_71752])).

tff(c_74052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73994,c_73986])).

tff(c_74053,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_71741])).

tff(c_74065,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74053,c_74053,c_36])).

tff(c_71742,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_71734,c_40])).

tff(c_71751,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_71742])).

tff(c_74055,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74053,c_71751])).

tff(c_74113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74065,c_74055])).

tff(c_74114,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_71742])).

tff(c_74125,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74114,c_74114,c_34])).

tff(c_74116,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_71741])).

tff(c_74174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74125,c_74114,c_74116])).

tff(c_74176,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_71741])).

tff(c_74203,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74114,c_74176])).

tff(c_75122,plain,(
    ! [A_1270,B_1271,C_1272] :
      ( k2_relset_1(A_1270,B_1271,C_1272) = k2_relat_1(C_1272)
      | ~ m1_subset_1(C_1272,k1_zfmisc_1(k2_zfmisc_1(A_1270,B_1271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_75144,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_75122])).

tff(c_75150,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_74203,c_75144])).

tff(c_74190,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74114,c_6])).

tff(c_75188,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75150,c_74190])).

tff(c_75197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74240,c_75188])).

tff(c_75199,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_74222])).

tff(c_75233,plain,(
    ! [A_1277] :
      ( A_1277 = '#skF_5'
      | ~ v1_xboole_0(A_1277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74114,c_8])).

tff(c_75246,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_75199,c_75233])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k1_xboole_0 = B_12
      | k1_xboole_0 = A_11
      | k2_zfmisc_1(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_75209,plain,(
    ! [B_12,A_11] :
      ( B_12 = '#skF_5'
      | A_11 = '#skF_5'
      | k2_zfmisc_1(A_11,B_12) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74114,c_74114,c_74114,c_16])).

tff(c_75542,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_75246,c_75209])).

tff(c_75578,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_75542])).

tff(c_75597,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75578,c_71734])).

tff(c_75601,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75578,c_116])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74187,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74114,c_10])).

tff(c_75590,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75578,c_74187])).

tff(c_75593,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75578,c_75578,c_74203])).

tff(c_74115,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_71742])).

tff(c_74226,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74114,c_74115])).

tff(c_75592,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75578,c_75578,c_74226])).

tff(c_76829,plain,(
    ! [B_1365,A_1366] :
      ( v1_funct_2(B_1365,k1_relat_1(B_1365),A_1366)
      | ~ r1_tarski(k2_relat_1(B_1365),A_1366)
      | ~ v1_funct_1(B_1365)
      | ~ v1_relat_1(B_1365) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_76838,plain,(
    ! [A_1366] :
      ( v1_funct_2('#skF_4','#skF_4',A_1366)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_1366)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75592,c_76829])).

tff(c_76841,plain,(
    ! [A_1366] : v1_funct_2('#skF_4','#skF_4',A_1366) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75597,c_75601,c_75590,c_75593,c_76838])).

tff(c_75198,plain,(
    v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_74222])).

tff(c_75247,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_75198,c_75233])).

tff(c_71731,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_71654,c_71712])).

tff(c_71749,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0
    | k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71731,c_38])).

tff(c_75251,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74114,c_74114,c_71749])).

tff(c_75252,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_75251])).

tff(c_75309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74203,c_75247,c_75252])).

tff(c_75310,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_75251])).

tff(c_75316,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75310,c_71653])).

tff(c_75583,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75578,c_75316])).

tff(c_76845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76841,c_75583])).

tff(c_76846,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_75542])).

tff(c_76847,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_75542])).

tff(c_76875,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76846,c_76847])).

tff(c_75337,plain,(
    ! [C_1279,B_1280,A_1281] :
      ( ~ v1_xboole_0(C_1279)
      | ~ m1_subset_1(B_1280,k1_zfmisc_1(C_1279))
      | ~ r2_hidden(A_1281,B_1280) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_75346,plain,(
    ! [A_1281] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_1281,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_112,c_75337])).

tff(c_75379,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_75346])).

tff(c_75383,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_75379])).

tff(c_75397,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_75246,c_75209])).

tff(c_75400,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_75397])).

tff(c_75420,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75400,c_74190])).

tff(c_74184,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74114,c_74114,c_18])).

tff(c_75413,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75400,c_75400,c_74184])).

tff(c_75478,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75413,c_75379])).

tff(c_75481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75420,c_75478])).

tff(c_75482,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_75397])).

tff(c_75497,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75482,c_74190])).

tff(c_75506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75383,c_75497])).

tff(c_75508,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_75346])).

tff(c_74183,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74114,c_8])).

tff(c_75527,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_75508,c_74183])).

tff(c_75546,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75527,c_112])).

tff(c_76848,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76846,c_76846,c_75546])).

tff(c_76865,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76846,c_74114])).

tff(c_64,plain,(
    ! [A_36] :
      ( v1_funct_2(k1_xboole_0,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_36,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_119,plain,(
    ! [A_36] :
      ( v1_funct_2(k1_xboole_0,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_64])).

tff(c_76964,plain,(
    ! [A_36] :
      ( v1_funct_2('#skF_3',A_36,'#skF_3')
      | A_36 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76848,c_76865,c_76865,c_76865,c_76865,c_76865,c_119])).

tff(c_76852,plain,(
    ~ v1_funct_2('#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76846,c_75316])).

tff(c_76988,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_76964,c_76852])).

tff(c_76992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76875,c_76988])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:28:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.61/9.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.74/9.26  
% 17.74/9.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.74/9.26  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v8_relat_2 > v5_ordinal1 > v4_relat_2 > v3_relat_2 > v2_funct_1 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 17.74/9.26  
% 17.74/9.26  %Foreground sorts:
% 17.74/9.26  
% 17.74/9.26  
% 17.74/9.26  %Background operators:
% 17.74/9.26  
% 17.74/9.26  
% 17.74/9.26  %Foreground operators:
% 17.74/9.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 17.74/9.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 17.74/9.26  tff('#skF_2', type, '#skF_2': $i > $i).
% 17.74/9.26  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 17.74/9.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 17.74/9.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.74/9.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.74/9.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 17.74/9.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.74/9.26  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 17.74/9.26  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 17.74/9.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.74/9.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.74/9.26  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 17.74/9.26  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 17.74/9.26  tff('#skF_5', type, '#skF_5': $i).
% 17.74/9.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 17.74/9.26  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 17.74/9.26  tff('#skF_3', type, '#skF_3': $i).
% 17.74/9.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 17.74/9.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 17.74/9.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.74/9.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.74/9.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.74/9.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.74/9.26  tff('#skF_4', type, '#skF_4': $i).
% 17.74/9.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.74/9.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 17.74/9.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.74/9.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.74/9.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.74/9.26  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 17.74/9.26  
% 17.74/9.29  tff(f_50, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 17.74/9.29  tff(f_205, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 17.74/9.29  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 17.74/9.29  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 17.74/9.29  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 17.74/9.29  tff(f_109, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 17.74/9.29  tff(f_176, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 17.74/9.29  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 17.74/9.29  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 17.74/9.29  tff(f_147, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 17.74/9.29  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 17.74/9.29  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 17.74/9.29  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 17.74/9.29  tff(f_74, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 17.74/9.29  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 17.74/9.29  tff(f_63, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 17.74/9.29  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 17.74/9.29  tff(f_188, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 17.74/9.29  tff(c_14, plain, (![A_9, B_10]: (v1_xboole_0(k2_zfmisc_1(A_9, B_10)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.74/9.29  tff(c_108, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_205])).
% 17.74/9.29  tff(c_116, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_205])).
% 17.74/9.29  tff(c_229, plain, (![A_68]: (v1_funct_1(k2_funct_1(A_68)) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_99])).
% 17.74/9.29  tff(c_106, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 17.74/9.29  tff(c_206, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_106])).
% 17.74/9.29  tff(c_232, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_229, c_206])).
% 17.74/9.29  tff(c_235, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_232])).
% 17.74/9.29  tff(c_112, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 17.74/9.29  tff(c_360, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.74/9.29  tff(c_370, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_360])).
% 17.74/9.29  tff(c_381, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_370])).
% 17.74/9.29  tff(c_382, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_106])).
% 17.74/9.29  tff(c_393, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_382])).
% 17.74/9.29  tff(c_475, plain, (![C_96, A_97, B_98]: (v1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.74/9.29  tff(c_493, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_475])).
% 17.74/9.29  tff(c_110, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_205])).
% 17.74/9.29  tff(c_1400, plain, (![A_153, B_154, C_155]: (k2_relset_1(A_153, B_154, C_155)=k2_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 17.74/9.29  tff(c_1413, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_1400])).
% 17.74/9.29  tff(c_1423, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_1413])).
% 17.74/9.29  tff(c_48, plain, (![A_25]: (k1_relat_1(k2_funct_1(A_25))=k2_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_109])).
% 17.74/9.29  tff(c_44, plain, (![A_24]: (v1_relat_1(k2_funct_1(A_24)) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 17.74/9.29  tff(c_383, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_106])).
% 17.74/9.29  tff(c_1302, plain, (![A_140]: (k1_relat_1(k2_funct_1(A_140))=k2_relat_1(A_140) | ~v2_funct_1(A_140) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_109])).
% 17.74/9.29  tff(c_96, plain, (![A_41]: (v1_funct_2(A_41, k1_relat_1(A_41), k2_relat_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_176])).
% 17.74/9.29  tff(c_44852, plain, (![A_622]: (v1_funct_2(k2_funct_1(A_622), k2_relat_1(A_622), k2_relat_1(k2_funct_1(A_622))) | ~v1_funct_1(k2_funct_1(A_622)) | ~v1_relat_1(k2_funct_1(A_622)) | ~v2_funct_1(A_622) | ~v1_funct_1(A_622) | ~v1_relat_1(A_622))), inference(superposition, [status(thm), theory('equality')], [c_1302, c_96])).
% 17.74/9.29  tff(c_44894, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1423, c_44852])).
% 17.74/9.29  tff(c_44931, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_116, c_110, c_383, c_44894])).
% 17.74/9.29  tff(c_46585, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_44931])).
% 17.74/9.29  tff(c_46588, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_46585])).
% 17.74/9.29  tff(c_46592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_493, c_116, c_46588])).
% 17.74/9.29  tff(c_46594, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_44931])).
% 17.74/9.29  tff(c_38, plain, (![A_23]: (k2_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 17.74/9.29  tff(c_501, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_493, c_38])).
% 17.74/9.29  tff(c_503, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_501])).
% 17.74/9.29  tff(c_1424, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1423, c_503])).
% 17.74/9.29  tff(c_114, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 17.74/9.29  tff(c_1704, plain, (![A_166, B_167, C_168]: (k1_relset_1(A_166, B_167, C_168)=k1_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 17.74/9.29  tff(c_1737, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_1704])).
% 17.74/9.29  tff(c_3310, plain, (![B_228, A_229, C_230]: (k1_xboole_0=B_228 | k1_relset_1(A_229, B_228, C_230)=A_229 | ~v1_funct_2(C_230, A_229, B_228) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_229, B_228))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.74/9.29  tff(c_3341, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_112, c_3310])).
% 17.74/9.29  tff(c_3359, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_1737, c_3341])).
% 17.74/9.29  tff(c_3360, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1424, c_3359])).
% 17.74/9.29  tff(c_46, plain, (![A_25]: (k2_relat_1(k2_funct_1(A_25))=k1_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_109])).
% 17.74/9.29  tff(c_1602, plain, (![A_164]: (m1_subset_1(A_164, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_164), k2_relat_1(A_164)))) | ~v1_funct_1(A_164) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_176])).
% 17.74/9.29  tff(c_55586, plain, (![A_680]: (m1_subset_1(k2_funct_1(A_680), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_680)), k1_relat_1(A_680)))) | ~v1_funct_1(k2_funct_1(A_680)) | ~v1_relat_1(k2_funct_1(A_680)) | ~v2_funct_1(A_680) | ~v1_funct_1(A_680) | ~v1_relat_1(A_680))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1602])).
% 17.74/9.29  tff(c_55624, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3360, c_55586])).
% 17.74/9.29  tff(c_55651, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_116, c_110, c_46594, c_383, c_55624])).
% 17.74/9.29  tff(c_55679, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48, c_55651])).
% 17.74/9.29  tff(c_55695, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_116, c_110, c_1423, c_55679])).
% 17.74/9.29  tff(c_55697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_393, c_55695])).
% 17.74/9.29  tff(c_55698, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_501])).
% 17.74/9.29  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.74/9.29  tff(c_55713, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_55698, c_55698, c_36])).
% 17.74/9.29  tff(c_40, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 17.74/9.29  tff(c_500, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_493, c_40])).
% 17.74/9.29  tff(c_502, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_500])).
% 17.74/9.29  tff(c_55700, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_55698, c_502])).
% 17.74/9.29  tff(c_55757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55713, c_55700])).
% 17.74/9.29  tff(c_55758, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_500])).
% 17.74/9.29  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.74/9.29  tff(c_55771, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_55758, c_55758, c_34])).
% 17.74/9.29  tff(c_56090, plain, (![A_710, B_711, C_712]: (k2_relset_1(A_710, B_711, C_712)=k2_relat_1(C_712) | ~m1_subset_1(C_712, k1_zfmisc_1(k2_zfmisc_1(A_710, B_711))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 17.74/9.29  tff(c_56106, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_56090])).
% 17.74/9.29  tff(c_56110, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_55771, c_108, c_56106])).
% 17.74/9.29  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.74/9.29  tff(c_55776, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_55758, c_6])).
% 17.74/9.29  tff(c_56133, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56110, c_55776])).
% 17.74/9.29  tff(c_18, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 17.74/9.29  tff(c_55770, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_55758, c_55758, c_18])).
% 17.74/9.29  tff(c_56125, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56110, c_56110, c_55770])).
% 17.74/9.29  tff(c_55847, plain, (![C_691, B_692, A_693]: (~v1_xboole_0(C_691) | ~m1_subset_1(B_692, k1_zfmisc_1(C_691)) | ~r2_hidden(A_693, B_692))), inference(cnfTransformation, [status(thm)], [f_74])).
% 17.74/9.29  tff(c_55856, plain, (![A_693]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_693, '#skF_5'))), inference(resolution, [status(thm)], [c_112, c_55847])).
% 17.74/9.29  tff(c_55955, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_55856])).
% 17.74/9.29  tff(c_56364, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56125, c_55955])).
% 17.74/9.29  tff(c_56367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56133, c_56364])).
% 17.74/9.29  tff(c_56369, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_55856])).
% 17.74/9.29  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 17.74/9.29  tff(c_55769, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_55758, c_8])).
% 17.74/9.29  tff(c_56392, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_56369, c_55769])).
% 17.74/9.29  tff(c_56396, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56392, c_112])).
% 17.74/9.29  tff(c_57311, plain, (![A_781, B_782, C_783]: (k2_relset_1(A_781, B_782, C_783)=k2_relat_1(C_783) | ~m1_subset_1(C_783, k1_zfmisc_1(k2_zfmisc_1(A_781, B_782))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 17.74/9.29  tff(c_57376, plain, (![C_788]: (k2_relset_1('#skF_3', '#skF_4', C_788)=k2_relat_1(C_788) | ~m1_subset_1(C_788, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_56392, c_57311])).
% 17.74/9.29  tff(c_57379, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56396, c_57376])).
% 17.74/9.29  tff(c_57385, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_55771, c_57379])).
% 17.74/9.29  tff(c_57433, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57385, c_493])).
% 17.74/9.29  tff(c_57440, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57385, c_116])).
% 17.74/9.29  tff(c_20, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 17.74/9.29  tff(c_55768, plain, (![B_12]: (k2_zfmisc_1('#skF_5', B_12)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_55758, c_55758, c_20])).
% 17.74/9.29  tff(c_57425, plain, (![B_12]: (k2_zfmisc_1('#skF_4', B_12)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57385, c_57385, c_55768])).
% 17.74/9.29  tff(c_57435, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_57385, c_393])).
% 17.74/9.29  tff(c_57678, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_57425, c_57435])).
% 17.74/9.29  tff(c_57439, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57385, c_110])).
% 17.74/9.29  tff(c_57436, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_57385, c_383])).
% 17.74/9.29  tff(c_57423, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57385, c_57385, c_55770])).
% 17.74/9.29  tff(c_55772, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_55758, c_55758, c_36])).
% 17.74/9.29  tff(c_57429, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57385, c_57385, c_55772])).
% 17.74/9.29  tff(c_56725, plain, (![A_750]: (m1_subset_1(A_750, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_750), k2_relat_1(A_750)))) | ~v1_funct_1(A_750) | ~v1_relat_1(A_750))), inference(cnfTransformation, [status(thm)], [f_176])).
% 17.74/9.29  tff(c_71572, plain, (![A_1061]: (m1_subset_1(k2_funct_1(A_1061), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1061)), k1_relat_1(A_1061)))) | ~v1_funct_1(k2_funct_1(A_1061)) | ~v1_relat_1(k2_funct_1(A_1061)) | ~v2_funct_1(A_1061) | ~v1_funct_1(A_1061) | ~v1_relat_1(A_1061))), inference(superposition, [status(thm), theory('equality')], [c_46, c_56725])).
% 17.74/9.29  tff(c_71616, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_57429, c_71572])).
% 17.74/9.29  tff(c_71644, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_57433, c_57440, c_57439, c_57436, c_57423, c_71616])).
% 17.74/9.29  tff(c_71645, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_57678, c_71644])).
% 17.74/9.29  tff(c_71648, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_71645])).
% 17.74/9.29  tff(c_71652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57433, c_57440, c_71648])).
% 17.74/9.29  tff(c_71654, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_382])).
% 17.74/9.29  tff(c_74208, plain, (![B_1202, A_1203]: (v1_xboole_0(B_1202) | ~m1_subset_1(B_1202, k1_zfmisc_1(A_1203)) | ~v1_xboole_0(A_1203))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.74/9.29  tff(c_74222, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_71654, c_74208])).
% 17.74/9.29  tff(c_74233, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_74222])).
% 17.74/9.29  tff(c_74240, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_14, c_74233])).
% 17.74/9.29  tff(c_71753, plain, (![B_1073, A_1074]: (v1_xboole_0(B_1073) | ~m1_subset_1(B_1073, k1_zfmisc_1(A_1074)) | ~v1_xboole_0(A_1074))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.74/9.29  tff(c_71775, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_112, c_71753])).
% 17.74/9.29  tff(c_71820, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_71775])).
% 17.74/9.29  tff(c_71835, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_14, c_71820])).
% 17.74/9.29  tff(c_71712, plain, (![C_1070, A_1071, B_1072]: (v1_relat_1(C_1070) | ~m1_subset_1(C_1070, k1_zfmisc_1(k2_zfmisc_1(A_1071, B_1072))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.74/9.29  tff(c_71734, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_71712])).
% 17.74/9.29  tff(c_72936, plain, (![A_1143, B_1144, C_1145]: (k2_relset_1(A_1143, B_1144, C_1145)=k2_relat_1(C_1145) | ~m1_subset_1(C_1145, k1_zfmisc_1(k2_zfmisc_1(A_1143, B_1144))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 17.74/9.29  tff(c_72958, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_72936])).
% 17.74/9.29  tff(c_72970, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_72958])).
% 17.74/9.29  tff(c_71653, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_382])).
% 17.74/9.29  tff(c_72667, plain, (![A_1130, B_1131, C_1132]: (k1_relset_1(A_1130, B_1131, C_1132)=k1_relat_1(C_1132) | ~m1_subset_1(C_1132, k1_zfmisc_1(k2_zfmisc_1(A_1130, B_1131))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 17.74/9.29  tff(c_72691, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_71654, c_72667])).
% 17.74/9.29  tff(c_73845, plain, (![B_1183, C_1184, A_1185]: (k1_xboole_0=B_1183 | v1_funct_2(C_1184, A_1185, B_1183) | k1_relset_1(A_1185, B_1183, C_1184)!=A_1185 | ~m1_subset_1(C_1184, k1_zfmisc_1(k2_zfmisc_1(A_1185, B_1183))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.74/9.29  tff(c_73870, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_71654, c_73845])).
% 17.74/9.29  tff(c_73891, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72691, c_73870])).
% 17.74/9.29  tff(c_73892, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_71653, c_73891])).
% 17.74/9.29  tff(c_73899, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_73892])).
% 17.74/9.29  tff(c_73902, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48, c_73899])).
% 17.74/9.29  tff(c_73905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71734, c_116, c_110, c_72970, c_73902])).
% 17.74/9.29  tff(c_73906, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_73892])).
% 17.74/9.29  tff(c_73968, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73906, c_6])).
% 17.74/9.29  tff(c_73972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71835, c_73968])).
% 17.74/9.29  tff(c_73973, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_71775])).
% 17.74/9.29  tff(c_73984, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_73973, c_8])).
% 17.74/9.29  tff(c_73994, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_73984, c_73984, c_34])).
% 17.74/9.29  tff(c_71741, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_71734, c_38])).
% 17.74/9.29  tff(c_71752, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_71741])).
% 17.74/9.29  tff(c_73986, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_73984, c_71752])).
% 17.74/9.29  tff(c_74052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73994, c_73986])).
% 17.74/9.29  tff(c_74053, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_71741])).
% 17.74/9.29  tff(c_74065, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74053, c_74053, c_36])).
% 17.74/9.29  tff(c_71742, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_71734, c_40])).
% 17.74/9.29  tff(c_71751, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_71742])).
% 17.74/9.29  tff(c_74055, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74053, c_71751])).
% 17.74/9.29  tff(c_74113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74065, c_74055])).
% 17.74/9.29  tff(c_74114, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_71742])).
% 17.74/9.29  tff(c_74125, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74114, c_74114, c_34])).
% 17.74/9.29  tff(c_74116, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_71741])).
% 17.74/9.29  tff(c_74174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74125, c_74114, c_74116])).
% 17.74/9.29  tff(c_74176, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_71741])).
% 17.74/9.29  tff(c_74203, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74114, c_74176])).
% 17.74/9.29  tff(c_75122, plain, (![A_1270, B_1271, C_1272]: (k2_relset_1(A_1270, B_1271, C_1272)=k2_relat_1(C_1272) | ~m1_subset_1(C_1272, k1_zfmisc_1(k2_zfmisc_1(A_1270, B_1271))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 17.74/9.29  tff(c_75144, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_75122])).
% 17.74/9.29  tff(c_75150, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_74203, c_75144])).
% 17.74/9.29  tff(c_74190, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74114, c_6])).
% 17.74/9.29  tff(c_75188, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75150, c_74190])).
% 17.74/9.29  tff(c_75197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74240, c_75188])).
% 17.74/9.29  tff(c_75199, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_74222])).
% 17.74/9.29  tff(c_75233, plain, (![A_1277]: (A_1277='#skF_5' | ~v1_xboole_0(A_1277))), inference(demodulation, [status(thm), theory('equality')], [c_74114, c_8])).
% 17.74/9.29  tff(c_75246, plain, (k2_zfmisc_1('#skF_4', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_75199, c_75233])).
% 17.74/9.29  tff(c_16, plain, (![B_12, A_11]: (k1_xboole_0=B_12 | k1_xboole_0=A_11 | k2_zfmisc_1(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 17.74/9.29  tff(c_75209, plain, (![B_12, A_11]: (B_12='#skF_5' | A_11='#skF_5' | k2_zfmisc_1(A_11, B_12)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74114, c_74114, c_74114, c_16])).
% 17.74/9.29  tff(c_75542, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_75246, c_75209])).
% 17.74/9.29  tff(c_75578, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_75542])).
% 17.74/9.29  tff(c_75597, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75578, c_71734])).
% 17.74/9.29  tff(c_75601, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75578, c_116])).
% 17.74/9.29  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.74/9.29  tff(c_74187, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_74114, c_10])).
% 17.74/9.29  tff(c_75590, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_75578, c_74187])).
% 17.74/9.29  tff(c_75593, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_75578, c_75578, c_74203])).
% 17.74/9.29  tff(c_74115, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_71742])).
% 17.74/9.29  tff(c_74226, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74114, c_74115])).
% 17.74/9.29  tff(c_75592, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_75578, c_75578, c_74226])).
% 17.74/9.29  tff(c_76829, plain, (![B_1365, A_1366]: (v1_funct_2(B_1365, k1_relat_1(B_1365), A_1366) | ~r1_tarski(k2_relat_1(B_1365), A_1366) | ~v1_funct_1(B_1365) | ~v1_relat_1(B_1365))), inference(cnfTransformation, [status(thm)], [f_188])).
% 17.74/9.29  tff(c_76838, plain, (![A_1366]: (v1_funct_2('#skF_4', '#skF_4', A_1366) | ~r1_tarski(k2_relat_1('#skF_4'), A_1366) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75592, c_76829])).
% 17.74/9.29  tff(c_76841, plain, (![A_1366]: (v1_funct_2('#skF_4', '#skF_4', A_1366))), inference(demodulation, [status(thm), theory('equality')], [c_75597, c_75601, c_75590, c_75593, c_76838])).
% 17.74/9.29  tff(c_75198, plain, (v1_xboole_0(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_74222])).
% 17.74/9.29  tff(c_75247, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_75198, c_75233])).
% 17.74/9.29  tff(c_71731, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_71654, c_71712])).
% 17.74/9.29  tff(c_71749, plain, (k2_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0 | k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_71731, c_38])).
% 17.74/9.29  tff(c_75251, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74114, c_74114, c_71749])).
% 17.74/9.29  tff(c_75252, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_75251])).
% 17.74/9.29  tff(c_75309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74203, c_75247, c_75252])).
% 17.74/9.29  tff(c_75310, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_75251])).
% 17.74/9.29  tff(c_75316, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75310, c_71653])).
% 17.74/9.29  tff(c_75583, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75578, c_75316])).
% 17.74/9.29  tff(c_76845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76841, c_75583])).
% 17.74/9.29  tff(c_76846, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_75542])).
% 17.74/9.29  tff(c_76847, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_75542])).
% 17.74/9.29  tff(c_76875, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76846, c_76847])).
% 17.74/9.29  tff(c_75337, plain, (![C_1279, B_1280, A_1281]: (~v1_xboole_0(C_1279) | ~m1_subset_1(B_1280, k1_zfmisc_1(C_1279)) | ~r2_hidden(A_1281, B_1280))), inference(cnfTransformation, [status(thm)], [f_74])).
% 17.74/9.29  tff(c_75346, plain, (![A_1281]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_1281, '#skF_5'))), inference(resolution, [status(thm)], [c_112, c_75337])).
% 17.74/9.29  tff(c_75379, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_75346])).
% 17.74/9.29  tff(c_75383, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_14, c_75379])).
% 17.74/9.29  tff(c_75397, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_75246, c_75209])).
% 17.74/9.29  tff(c_75400, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_75397])).
% 17.74/9.29  tff(c_75420, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75400, c_74190])).
% 17.74/9.29  tff(c_74184, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74114, c_74114, c_18])).
% 17.74/9.29  tff(c_75413, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75400, c_75400, c_74184])).
% 17.74/9.29  tff(c_75478, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75413, c_75379])).
% 17.74/9.29  tff(c_75481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75420, c_75478])).
% 17.74/9.29  tff(c_75482, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_75397])).
% 17.74/9.29  tff(c_75497, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75482, c_74190])).
% 17.74/9.29  tff(c_75506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75383, c_75497])).
% 17.74/9.29  tff(c_75508, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_75346])).
% 17.74/9.29  tff(c_74183, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_74114, c_8])).
% 17.74/9.29  tff(c_75527, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_75508, c_74183])).
% 17.74/9.29  tff(c_75546, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_75527, c_112])).
% 17.74/9.29  tff(c_76848, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76846, c_76846, c_75546])).
% 17.74/9.29  tff(c_76865, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76846, c_74114])).
% 17.74/9.29  tff(c_64, plain, (![A_36]: (v1_funct_2(k1_xboole_0, A_36, k1_xboole_0) | k1_xboole_0=A_36 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_36, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.74/9.29  tff(c_119, plain, (![A_36]: (v1_funct_2(k1_xboole_0, A_36, k1_xboole_0) | k1_xboole_0=A_36 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_64])).
% 17.74/9.29  tff(c_76964, plain, (![A_36]: (v1_funct_2('#skF_3', A_36, '#skF_3') | A_36='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76848, c_76865, c_76865, c_76865, c_76865, c_76865, c_119])).
% 17.74/9.29  tff(c_76852, plain, (~v1_funct_2('#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76846, c_75316])).
% 17.74/9.29  tff(c_76988, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_76964, c_76852])).
% 17.74/9.29  tff(c_76992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76875, c_76988])).
% 17.74/9.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.74/9.29  
% 17.74/9.29  Inference rules
% 17.74/9.29  ----------------------
% 17.74/9.29  #Ref     : 0
% 17.74/9.29  #Sup     : 20284
% 17.74/9.29  #Fact    : 0
% 17.74/9.29  #Define  : 0
% 17.74/9.29  #Split   : 49
% 17.74/9.29  #Chain   : 0
% 17.74/9.29  #Close   : 0
% 17.74/9.29  
% 17.74/9.29  Ordering : KBO
% 17.74/9.29  
% 17.74/9.29  Simplification rules
% 17.74/9.29  ----------------------
% 17.74/9.29  #Subsume      : 7356
% 17.74/9.29  #Demod        : 26796
% 17.74/9.29  #Tautology    : 9649
% 17.74/9.29  #SimpNegUnit  : 320
% 17.74/9.29  #BackRed      : 490
% 17.74/9.29  
% 17.74/9.29  #Partial instantiations: 0
% 17.74/9.29  #Strategies tried      : 1
% 17.74/9.29  
% 17.74/9.29  Timing (in seconds)
% 17.74/9.29  ----------------------
% 17.74/9.29  Preprocessing        : 0.38
% 17.74/9.29  Parsing              : 0.20
% 17.74/9.29  CNF conversion       : 0.03
% 17.74/9.29  Main loop            : 8.09
% 17.74/9.29  Inferencing          : 1.52
% 17.74/9.29  Reduction            : 2.75
% 17.74/9.29  Demodulation         : 2.12
% 17.74/9.29  BG Simplification    : 0.17
% 17.74/9.29  Subsumption          : 3.25
% 17.74/9.29  Abstraction          : 0.26
% 17.74/9.29  MUC search           : 0.00
% 17.74/9.29  Cooper               : 0.00
% 17.74/9.29  Total                : 8.55
% 17.74/9.29  Index Insertion      : 0.00
% 17.74/9.29  Index Deletion       : 0.00
% 17.74/9.29  Index Matching       : 0.00
% 17.74/9.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
