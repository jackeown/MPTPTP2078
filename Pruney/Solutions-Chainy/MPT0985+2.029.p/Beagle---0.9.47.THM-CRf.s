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
% DateTime   : Thu Dec  3 10:12:30 EST 2020

% Result     : Theorem 6.74s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :  270 (6305 expanded)
%              Number of leaves         :   37 (2010 expanded)
%              Depth                    :   17
%              Number of atoms          :  483 (16985 expanded)
%              Number of equality atoms :  167 (5734 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_139,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_148,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_139])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_60,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_58,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2909,plain,(
    ! [A_369,B_370,C_371] :
      ( k2_relset_1(A_369,B_370,C_371) = k2_relat_1(C_371)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_369,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2922,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_2909])).

tff(c_2927,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2922])).

tff(c_30,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    ! [A_14] :
      ( v1_funct_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_110,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_113,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_110])).

tff(c_116,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_113])).

tff(c_124,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_131,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_124])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_131])).

tff(c_137,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_158,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_315,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_322,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_315])).

tff(c_325,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_322])).

tff(c_26,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_18,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_156,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_148,c_18])).

tff(c_159,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_326,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_159])).

tff(c_64,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_459,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_476,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_459])).

tff(c_780,plain,(
    ! [B_150,A_151,C_152] :
      ( k1_xboole_0 = B_150
      | k1_relset_1(A_151,B_150,C_152) = A_151
      | ~ v1_funct_2(C_152,A_151,B_150)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_151,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_793,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_780])).

tff(c_802,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_476,c_793])).

tff(c_803,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_802])).

tff(c_246,plain,(
    ! [A_73] :
      ( k2_relat_1(k2_funct_1(A_73)) = k1_relat_1(A_73)
      | ~ v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_52,plain,(
    ! [A_28] :
      ( v1_funct_2(A_28,k1_relat_1(A_28),k2_relat_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1207,plain,(
    ! [A_192] :
      ( v1_funct_2(k2_funct_1(A_192),k1_relat_1(k2_funct_1(A_192)),k1_relat_1(A_192))
      | ~ v1_funct_1(k2_funct_1(A_192))
      | ~ v1_relat_1(k2_funct_1(A_192))
      | ~ v2_funct_1(A_192)
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_52])).

tff(c_1210,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_1207])).

tff(c_1218,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_66,c_60,c_138,c_1210])).

tff(c_1219,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1218])).

tff(c_1222,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_1219])).

tff(c_1226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_66,c_1222])).

tff(c_1228,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1218])).

tff(c_28,plain,(
    ! [A_15] :
      ( k2_relat_1(k2_funct_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_356,plain,(
    ! [A_97] :
      ( m1_subset_1(A_97,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_97),k2_relat_1(A_97))))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1452,plain,(
    ! [A_210] :
      ( m1_subset_1(k2_funct_1(A_210),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_210)),k1_relat_1(A_210))))
      | ~ v1_funct_1(k2_funct_1(A_210))
      | ~ v1_relat_1(k2_funct_1(A_210))
      | ~ v2_funct_1(A_210)
      | ~ v1_funct_1(A_210)
      | ~ v1_relat_1(A_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_356])).

tff(c_1473,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_1452])).

tff(c_1487,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_66,c_60,c_1228,c_138,c_1473])).

tff(c_1508,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1487])).

tff(c_1522,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_66,c_60,c_325,c_1508])).

tff(c_1524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_1522])).

tff(c_1525,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_1526,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_1546,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_1526])).

tff(c_1704,plain,(
    ! [A_243,B_244,C_245] :
      ( k2_relset_1(A_243,B_244,C_245) = k2_relat_1(C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1711,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_1704])).

tff(c_1714,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1546,c_58,c_1711])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1531,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_12])).

tff(c_1726,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_1531])).

tff(c_1728,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_148])).

tff(c_1735,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_66])).

tff(c_1734,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_60])).

tff(c_1724,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_1714,c_1546])).

tff(c_1729,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_138])).

tff(c_1663,plain,(
    ! [A_235] :
      ( k1_relat_1(k2_funct_1(A_235)) = k2_relat_1(A_235)
      | ~ v2_funct_1(A_235)
      | ~ v1_funct_1(A_235)
      | ~ v1_relat_1(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2590,plain,(
    ! [A_327] :
      ( v1_funct_2(k2_funct_1(A_327),k2_relat_1(A_327),k2_relat_1(k2_funct_1(A_327)))
      | ~ v1_funct_1(k2_funct_1(A_327))
      | ~ v1_relat_1(k2_funct_1(A_327))
      | ~ v2_funct_1(A_327)
      | ~ v1_funct_1(A_327)
      | ~ v1_relat_1(A_327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1663,c_52])).

tff(c_2593,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1724,c_2590])).

tff(c_2601,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1728,c_1735,c_1734,c_1729,c_2593])).

tff(c_2602,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2601])).

tff(c_2605,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_2602])).

tff(c_2609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1728,c_1735,c_2605])).

tff(c_2611,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2601])).

tff(c_20,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1528,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != '#skF_5'
      | A_12 = '#skF_5'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_1525,c_20])).

tff(c_1719,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != '#skF_4'
      | A_12 = '#skF_4'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_1714,c_1528])).

tff(c_2619,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2611,c_1719])).

tff(c_2641,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2619])).

tff(c_2644,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2641])).

tff(c_2647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1728,c_1735,c_1734,c_1724,c_2644])).

tff(c_2648,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2619])).

tff(c_104,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_2'(A_41,B_42),A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_41,B_42] :
      ( ~ v1_xboole_0(A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1545,plain,(
    ~ r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_158])).

tff(c_1554,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_108,c_1545])).

tff(c_1721,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_1554])).

tff(c_2656,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2648,c_1721])).

tff(c_2662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1726,c_2656])).

tff(c_2663,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_2665,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_2928,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2927,c_2665])).

tff(c_2887,plain,(
    ! [A_366,B_367,C_368] :
      ( k1_relset_1(A_366,B_367,C_368) = k1_relat_1(C_368)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_366,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2904,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_2887])).

tff(c_3114,plain,(
    ! [B_398,A_399,C_400] :
      ( k1_xboole_0 = B_398
      | k1_relset_1(A_399,B_398,C_400) = A_399
      | ~ v1_funct_2(C_400,A_399,B_398)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_399,B_398))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3130,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3114])).

tff(c_3141,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2904,c_3130])).

tff(c_3142,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2928,c_3141])).

tff(c_155,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_148,c_20])).

tff(c_157,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_3150,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3142,c_157])).

tff(c_2664,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_2902,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2664,c_2887])).

tff(c_3218,plain,(
    ! [B_402,C_403,A_404] :
      ( k1_xboole_0 = B_402
      | v1_funct_2(C_403,A_404,B_402)
      | k1_relset_1(A_404,B_402,C_403) != A_404
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(A_404,B_402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3224,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_2664,c_3218])).

tff(c_3234,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2902,c_3224])).

tff(c_3235,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2663,c_3150,c_3234])).

tff(c_3243,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3235])).

tff(c_3246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_66,c_60,c_2927,c_3243])).

tff(c_3247,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_3249,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3247,c_157])).

tff(c_3248,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_3272,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3247,c_3248])).

tff(c_3410,plain,(
    ! [A_429] :
      ( k1_relat_1(k2_funct_1(A_429)) = k2_relat_1(A_429)
      | ~ v2_funct_1(A_429)
      | ~ v1_funct_1(A_429)
      | ~ v1_relat_1(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_32,plain,(
    ! [C_18,A_16,B_17] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3270,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2664,c_32])).

tff(c_3339,plain,(
    ! [A_418] :
      ( k1_relat_1(A_418) != '#skF_5'
      | A_418 = '#skF_5'
      | ~ v1_relat_1(A_418) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3247,c_3247,c_20])).

tff(c_3353,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3270,c_3339])).

tff(c_3357,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3353])).

tff(c_3416,plain,
    ( k2_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3410,c_3357])).

tff(c_3426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_66,c_60,c_3272,c_3416])).

tff(c_3427,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3353])).

tff(c_3319,plain,(
    ! [A_417] :
      ( k2_relat_1(A_417) != '#skF_5'
      | A_417 = '#skF_5'
      | ~ v1_relat_1(A_417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3247,c_3247,c_18])).

tff(c_3333,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3270,c_3319])).

tff(c_3356,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3333])).

tff(c_3429,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3427,c_3356])).

tff(c_3437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_3429])).

tff(c_3438,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3333])).

tff(c_3513,plain,(
    ! [A_439] :
      ( k1_relat_1(k2_funct_1(A_439)) = k2_relat_1(A_439)
      | ~ v2_funct_1(A_439)
      | ~ v1_funct_1(A_439)
      | ~ v1_relat_1(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3525,plain,
    ( k2_relat_1('#skF_5') = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3438,c_3513])).

tff(c_3529,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_66,c_60,c_3272,c_3525])).

tff(c_3531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3249,c_3529])).

tff(c_3532,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_3533,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_3548,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3532,c_3533])).

tff(c_5792,plain,(
    ! [A_618] :
      ( k2_relat_1(k2_funct_1(A_618)) = k1_relat_1(A_618)
      | ~ v2_funct_1(A_618)
      | ~ v1_funct_1(A_618)
      | ~ v1_relat_1(A_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3537,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3532,c_12])).

tff(c_3711,plain,(
    ! [A_469,B_470,C_471] :
      ( k1_relset_1(A_469,B_470,C_471) = k1_relat_1(C_471)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(A_469,B_470))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3799,plain,(
    ! [A_490,B_491,A_492] :
      ( k1_relset_1(A_490,B_491,A_492) = k1_relat_1(A_492)
      | ~ r1_tarski(A_492,k2_zfmisc_1(A_490,B_491)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3711])).

tff(c_3815,plain,(
    ! [A_493,B_494,A_495] :
      ( k1_relset_1(A_493,B_494,A_495) = k1_relat_1(A_495)
      | ~ v1_xboole_0(A_495) ) ),
    inference(resolution,[status(thm)],[c_108,c_3799])).

tff(c_3817,plain,(
    ! [A_493,B_494] : k1_relset_1(A_493,B_494,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3537,c_3815])).

tff(c_3819,plain,(
    ! [A_493,B_494] : k1_relset_1(A_493,B_494,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3548,c_3817])).

tff(c_48,plain,(
    ! [B_26,A_25,C_27] :
      ( k1_xboole_0 = B_26
      | k1_relset_1(A_25,B_26,C_27) = A_25
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4373,plain,(
    ! [B_549,A_550,C_551] :
      ( B_549 = '#skF_5'
      | k1_relset_1(A_550,B_549,C_551) = A_550
      | ~ v1_funct_2(C_551,A_550,B_549)
      | ~ m1_subset_1(C_551,k1_zfmisc_1(k2_zfmisc_1(A_550,B_549))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3532,c_48])).

tff(c_4386,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_4373])).

tff(c_4394,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3819,c_4386])).

tff(c_4395,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4394])).

tff(c_4434,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4395,c_3537])).

tff(c_4436,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4395,c_148])).

tff(c_4442,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4395,c_66])).

tff(c_4441,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4395,c_60])).

tff(c_4433,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4395,c_4395,c_3548])).

tff(c_4437,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4395,c_138])).

tff(c_3689,plain,(
    ! [A_466,B_467,C_468] :
      ( k2_relset_1(A_466,B_467,C_468) = k2_relat_1(C_468)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(A_466,B_467))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3696,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_3689])).

tff(c_3699,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3696])).

tff(c_4424,plain,(
    k2_relat_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4395,c_3699])).

tff(c_3672,plain,(
    ! [A_464] :
      ( k1_relat_1(k2_funct_1(A_464)) = k2_relat_1(A_464)
      | ~ v2_funct_1(A_464)
      | ~ v1_funct_1(A_464)
      | ~ v1_relat_1(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4595,plain,(
    ! [A_557] :
      ( v1_funct_2(k2_funct_1(A_557),k2_relat_1(A_557),k2_relat_1(k2_funct_1(A_557)))
      | ~ v1_funct_1(k2_funct_1(A_557))
      | ~ v1_relat_1(k2_funct_1(A_557))
      | ~ v2_funct_1(A_557)
      | ~ v1_funct_1(A_557)
      | ~ v1_relat_1(A_557) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3672,c_52])).

tff(c_4598,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_4',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4424,c_4595])).

tff(c_4606,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_4',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4436,c_4442,c_4441,c_4437,c_4598])).

tff(c_4932,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4606])).

tff(c_4935,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_4932])).

tff(c_4939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4436,c_4442,c_4935])).

tff(c_4941,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4606])).

tff(c_3535,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != '#skF_5'
      | A_12 = '#skF_5'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3532,c_3532,c_18])).

tff(c_4428,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != '#skF_3'
      | A_12 = '#skF_3'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4395,c_4395,c_3535])).

tff(c_4949,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4941,c_4428])).

tff(c_4963,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4949])).

tff(c_4966,plain,
    ( k1_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4963])).

tff(c_4969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4436,c_4442,c_4441,c_4433,c_4966])).

tff(c_4970,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4949])).

tff(c_3584,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_3588,plain,(
    ~ r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_3584])).

tff(c_3592,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_108,c_3588])).

tff(c_4430,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4395,c_3592])).

tff(c_4977,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4970,c_4430])).

tff(c_4983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4434,c_4977])).

tff(c_4984,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4394])).

tff(c_5036,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4984,c_3537])).

tff(c_5038,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4984,c_148])).

tff(c_5044,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4984,c_66])).

tff(c_5043,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4984,c_60])).

tff(c_5035,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4984,c_4984,c_3548])).

tff(c_3660,plain,(
    ! [A_463] :
      ( k2_relat_1(k2_funct_1(A_463)) = k1_relat_1(A_463)
      | ~ v2_funct_1(A_463)
      | ~ v1_funct_1(A_463)
      | ~ v1_relat_1(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4986,plain,(
    ! [A_578] :
      ( v1_funct_2(k2_funct_1(A_578),k1_relat_1(k2_funct_1(A_578)),k1_relat_1(A_578))
      | ~ v1_funct_1(k2_funct_1(A_578))
      | ~ v1_relat_1(k2_funct_1(A_578))
      | ~ v2_funct_1(A_578)
      | ~ v1_funct_1(A_578)
      | ~ v1_relat_1(A_578) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_52])).

tff(c_4995,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_5')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3548,c_4986])).

tff(c_4997,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_66,c_60,c_138,c_4995])).

tff(c_5633,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4984,c_4984,c_4984,c_4984,c_4997])).

tff(c_5634,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5633])).

tff(c_5637,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_5634])).

tff(c_5641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5038,c_5044,c_5637])).

tff(c_5643,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5633])).

tff(c_5030,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != '#skF_4'
      | A_12 = '#skF_4'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4984,c_4984,c_3535])).

tff(c_5651,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5643,c_5030])).

tff(c_5657,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5651])).

tff(c_5660,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_5657])).

tff(c_5663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5038,c_5044,c_5043,c_5035,c_5660])).

tff(c_5664,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5651])).

tff(c_5032,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4984,c_3592])).

tff(c_5671,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5664,c_5032])).

tff(c_5678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5036,c_5671])).

tff(c_5680,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_5687,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5680,c_32])).

tff(c_5701,plain,(
    ! [A_608] :
      ( k2_relat_1(A_608) != '#skF_5'
      | A_608 = '#skF_5'
      | ~ v1_relat_1(A_608) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3532,c_3532,c_18])).

tff(c_5714,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5687,c_5701])).

tff(c_5739,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_5714])).

tff(c_5801,plain,
    ( k1_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5792,c_5739])).

tff(c_5808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_66,c_60,c_3548,c_5801])).

tff(c_5809,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5714])).

tff(c_5810,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5714])).

tff(c_5832,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5809,c_5810])).

tff(c_6016,plain,(
    ! [A_638,B_639,C_640] :
      ( k2_relset_1(A_638,B_639,C_640) = k2_relat_1(C_640)
      | ~ m1_subset_1(C_640,k1_zfmisc_1(k2_zfmisc_1(A_638,B_639))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6032,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_6016])).

tff(c_6040,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5832,c_58,c_6032])).

tff(c_5679,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_5814,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5809,c_5679])).

tff(c_6050,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6040,c_5814])).

tff(c_6055,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6040,c_6040,c_3548])).

tff(c_5813,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5809,c_5680])).

tff(c_6049,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6040,c_5813])).

tff(c_34,plain,(
    ! [A_19,B_20,C_21] :
      ( k1_relset_1(A_19,B_20,C_21) = k1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6253,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6049,c_34])).

tff(c_6264,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6055,c_6253])).

tff(c_6057,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6040,c_3532])).

tff(c_42,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6367,plain,(
    ! [C_655,B_656] :
      ( v1_funct_2(C_655,'#skF_4',B_656)
      | k1_relset_1('#skF_4',B_656,C_655) != '#skF_4'
      | ~ m1_subset_1(C_655,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_656))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6057,c_6057,c_6057,c_6057,c_42])).

tff(c_6373,plain,
    ( v1_funct_2('#skF_4','#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_6049,c_6367])).

tff(c_6383,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6264,c_6373])).

tff(c_6385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6050,c_6383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.74/2.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.74/2.40  
% 6.74/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.74/2.40  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 6.74/2.40  
% 6.74/2.40  %Foreground sorts:
% 6.74/2.40  
% 6.74/2.40  
% 6.74/2.40  %Background operators:
% 6.74/2.40  
% 6.74/2.40  
% 6.74/2.40  %Foreground operators:
% 6.74/2.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.74/2.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.74/2.40  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.74/2.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.74/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.74/2.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.74/2.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.74/2.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.74/2.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.74/2.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.74/2.40  tff('#skF_5', type, '#skF_5': $i).
% 6.74/2.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.74/2.40  tff('#skF_3', type, '#skF_3': $i).
% 6.74/2.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.74/2.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.74/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.74/2.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.74/2.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.74/2.40  tff('#skF_4', type, '#skF_4': $i).
% 6.74/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.74/2.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.74/2.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.74/2.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.74/2.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.74/2.40  
% 6.93/2.43  tff(f_130, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.93/2.43  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.93/2.43  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.93/2.43  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.93/2.43  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.93/2.43  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.93/2.43  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.93/2.43  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.93/2.43  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 6.93/2.43  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.93/2.43  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.93/2.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.93/2.43  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.93/2.43  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.93/2.43  tff(c_139, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.93/2.43  tff(c_148, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_139])).
% 6.93/2.43  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.93/2.43  tff(c_60, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.93/2.43  tff(c_58, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.93/2.43  tff(c_2909, plain, (![A_369, B_370, C_371]: (k2_relset_1(A_369, B_370, C_371)=k2_relat_1(C_371) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_369, B_370))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.93/2.43  tff(c_2922, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_2909])).
% 6.93/2.43  tff(c_2927, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2922])).
% 6.93/2.43  tff(c_30, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.93/2.43  tff(c_24, plain, (![A_14]: (v1_funct_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.93/2.43  tff(c_56, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.93/2.43  tff(c_110, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_56])).
% 6.93/2.43  tff(c_113, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_110])).
% 6.93/2.43  tff(c_116, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_113])).
% 6.93/2.43  tff(c_124, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.93/2.43  tff(c_131, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_124])).
% 6.93/2.43  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_131])).
% 6.93/2.43  tff(c_137, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_56])).
% 6.93/2.43  tff(c_158, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_137])).
% 6.93/2.43  tff(c_315, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.93/2.43  tff(c_322, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_315])).
% 6.93/2.43  tff(c_325, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_322])).
% 6.93/2.43  tff(c_26, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.93/2.43  tff(c_138, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_56])).
% 6.93/2.43  tff(c_18, plain, (![A_12]: (k2_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.93/2.43  tff(c_156, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_148, c_18])).
% 6.93/2.43  tff(c_159, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_156])).
% 6.93/2.43  tff(c_326, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_325, c_159])).
% 6.93/2.43  tff(c_64, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.93/2.43  tff(c_459, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.93/2.43  tff(c_476, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_459])).
% 6.93/2.43  tff(c_780, plain, (![B_150, A_151, C_152]: (k1_xboole_0=B_150 | k1_relset_1(A_151, B_150, C_152)=A_151 | ~v1_funct_2(C_152, A_151, B_150) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_151, B_150))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.93/2.43  tff(c_793, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_780])).
% 6.93/2.43  tff(c_802, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_476, c_793])).
% 6.93/2.43  tff(c_803, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_326, c_802])).
% 6.93/2.43  tff(c_246, plain, (![A_73]: (k2_relat_1(k2_funct_1(A_73))=k1_relat_1(A_73) | ~v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.93/2.43  tff(c_52, plain, (![A_28]: (v1_funct_2(A_28, k1_relat_1(A_28), k2_relat_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.93/2.43  tff(c_1207, plain, (![A_192]: (v1_funct_2(k2_funct_1(A_192), k1_relat_1(k2_funct_1(A_192)), k1_relat_1(A_192)) | ~v1_funct_1(k2_funct_1(A_192)) | ~v1_relat_1(k2_funct_1(A_192)) | ~v2_funct_1(A_192) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(superposition, [status(thm), theory('equality')], [c_246, c_52])).
% 6.93/2.43  tff(c_1210, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_803, c_1207])).
% 6.93/2.43  tff(c_1218, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_66, c_60, c_138, c_1210])).
% 6.93/2.43  tff(c_1219, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1218])).
% 6.93/2.43  tff(c_1222, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_1219])).
% 6.93/2.43  tff(c_1226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_66, c_1222])).
% 6.93/2.43  tff(c_1228, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1218])).
% 6.93/2.43  tff(c_28, plain, (![A_15]: (k2_relat_1(k2_funct_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.93/2.43  tff(c_356, plain, (![A_97]: (m1_subset_1(A_97, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_97), k2_relat_1(A_97)))) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.93/2.43  tff(c_1452, plain, (![A_210]: (m1_subset_1(k2_funct_1(A_210), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_210)), k1_relat_1(A_210)))) | ~v1_funct_1(k2_funct_1(A_210)) | ~v1_relat_1(k2_funct_1(A_210)) | ~v2_funct_1(A_210) | ~v1_funct_1(A_210) | ~v1_relat_1(A_210))), inference(superposition, [status(thm), theory('equality')], [c_28, c_356])).
% 6.93/2.43  tff(c_1473, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_803, c_1452])).
% 6.93/2.43  tff(c_1487, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_66, c_60, c_1228, c_138, c_1473])).
% 6.93/2.43  tff(c_1508, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1487])).
% 6.93/2.43  tff(c_1522, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_66, c_60, c_325, c_1508])).
% 6.93/2.43  tff(c_1524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_1522])).
% 6.93/2.43  tff(c_1525, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_156])).
% 6.93/2.43  tff(c_1526, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_156])).
% 6.93/2.43  tff(c_1546, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1525, c_1526])).
% 6.93/2.43  tff(c_1704, plain, (![A_243, B_244, C_245]: (k2_relset_1(A_243, B_244, C_245)=k2_relat_1(C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.93/2.43  tff(c_1711, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_1704])).
% 6.93/2.43  tff(c_1714, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1546, c_58, c_1711])).
% 6.93/2.43  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.93/2.43  tff(c_1531, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1525, c_12])).
% 6.93/2.43  tff(c_1726, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_1531])).
% 6.93/2.43  tff(c_1728, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_148])).
% 6.93/2.43  tff(c_1735, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_66])).
% 6.93/2.43  tff(c_1734, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_60])).
% 6.93/2.43  tff(c_1724, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_1714, c_1546])).
% 6.93/2.43  tff(c_1729, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_138])).
% 6.93/2.43  tff(c_1663, plain, (![A_235]: (k1_relat_1(k2_funct_1(A_235))=k2_relat_1(A_235) | ~v2_funct_1(A_235) | ~v1_funct_1(A_235) | ~v1_relat_1(A_235))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.93/2.43  tff(c_2590, plain, (![A_327]: (v1_funct_2(k2_funct_1(A_327), k2_relat_1(A_327), k2_relat_1(k2_funct_1(A_327))) | ~v1_funct_1(k2_funct_1(A_327)) | ~v1_relat_1(k2_funct_1(A_327)) | ~v2_funct_1(A_327) | ~v1_funct_1(A_327) | ~v1_relat_1(A_327))), inference(superposition, [status(thm), theory('equality')], [c_1663, c_52])).
% 6.93/2.43  tff(c_2593, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1724, c_2590])).
% 6.93/2.43  tff(c_2601, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1728, c_1735, c_1734, c_1729, c_2593])).
% 6.93/2.43  tff(c_2602, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2601])).
% 6.93/2.43  tff(c_2605, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_2602])).
% 6.93/2.43  tff(c_2609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1728, c_1735, c_2605])).
% 6.93/2.43  tff(c_2611, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2601])).
% 6.93/2.43  tff(c_20, plain, (![A_12]: (k1_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.93/2.43  tff(c_1528, plain, (![A_12]: (k1_relat_1(A_12)!='#skF_5' | A_12='#skF_5' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_1525, c_1525, c_20])).
% 6.93/2.43  tff(c_1719, plain, (![A_12]: (k1_relat_1(A_12)!='#skF_4' | A_12='#skF_4' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_1714, c_1528])).
% 6.93/2.43  tff(c_2619, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_2611, c_1719])).
% 6.93/2.43  tff(c_2641, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_2619])).
% 6.93/2.43  tff(c_2644, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2641])).
% 6.93/2.43  tff(c_2647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1728, c_1735, c_1734, c_1724, c_2644])).
% 6.93/2.43  tff(c_2648, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_2619])).
% 6.93/2.43  tff(c_104, plain, (![A_41, B_42]: (r2_hidden('#skF_2'(A_41, B_42), A_41) | r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.93/2.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.93/2.43  tff(c_108, plain, (![A_41, B_42]: (~v1_xboole_0(A_41) | r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_104, c_2])).
% 6.93/2.43  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.93/2.43  tff(c_1545, plain, (~r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_158])).
% 6.93/2.43  tff(c_1554, plain, (~v1_xboole_0(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_108, c_1545])).
% 6.93/2.43  tff(c_1721, plain, (~v1_xboole_0(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_1554])).
% 6.93/2.43  tff(c_2656, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2648, c_1721])).
% 6.93/2.43  tff(c_2662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1726, c_2656])).
% 6.93/2.43  tff(c_2663, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_137])).
% 6.93/2.43  tff(c_2665, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_156])).
% 6.93/2.43  tff(c_2928, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2927, c_2665])).
% 6.93/2.43  tff(c_2887, plain, (![A_366, B_367, C_368]: (k1_relset_1(A_366, B_367, C_368)=k1_relat_1(C_368) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_366, B_367))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.93/2.43  tff(c_2904, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_2887])).
% 6.93/2.43  tff(c_3114, plain, (![B_398, A_399, C_400]: (k1_xboole_0=B_398 | k1_relset_1(A_399, B_398, C_400)=A_399 | ~v1_funct_2(C_400, A_399, B_398) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_399, B_398))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.93/2.43  tff(c_3130, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_3114])).
% 6.93/2.43  tff(c_3141, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2904, c_3130])).
% 6.93/2.43  tff(c_3142, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2928, c_3141])).
% 6.93/2.43  tff(c_155, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_148, c_20])).
% 6.93/2.43  tff(c_157, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_155])).
% 6.93/2.43  tff(c_3150, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3142, c_157])).
% 6.93/2.43  tff(c_2664, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_137])).
% 6.93/2.43  tff(c_2902, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_2664, c_2887])).
% 6.93/2.43  tff(c_3218, plain, (![B_402, C_403, A_404]: (k1_xboole_0=B_402 | v1_funct_2(C_403, A_404, B_402) | k1_relset_1(A_404, B_402, C_403)!=A_404 | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(A_404, B_402))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.93/2.43  tff(c_3224, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_2664, c_3218])).
% 6.93/2.43  tff(c_3234, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2902, c_3224])).
% 6.93/2.43  tff(c_3235, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2663, c_3150, c_3234])).
% 6.93/2.43  tff(c_3243, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_30, c_3235])).
% 6.93/2.43  tff(c_3246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_66, c_60, c_2927, c_3243])).
% 6.93/2.43  tff(c_3247, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_156])).
% 6.93/2.43  tff(c_3249, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3247, c_157])).
% 6.93/2.43  tff(c_3248, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_156])).
% 6.93/2.43  tff(c_3272, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3247, c_3248])).
% 6.93/2.43  tff(c_3410, plain, (![A_429]: (k1_relat_1(k2_funct_1(A_429))=k2_relat_1(A_429) | ~v2_funct_1(A_429) | ~v1_funct_1(A_429) | ~v1_relat_1(A_429))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.93/2.43  tff(c_32, plain, (![C_18, A_16, B_17]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.93/2.43  tff(c_3270, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_2664, c_32])).
% 6.93/2.43  tff(c_3339, plain, (![A_418]: (k1_relat_1(A_418)!='#skF_5' | A_418='#skF_5' | ~v1_relat_1(A_418))), inference(demodulation, [status(thm), theory('equality')], [c_3247, c_3247, c_20])).
% 6.93/2.43  tff(c_3353, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_3270, c_3339])).
% 6.93/2.43  tff(c_3357, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_3353])).
% 6.93/2.43  tff(c_3416, plain, (k2_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3410, c_3357])).
% 6.93/2.43  tff(c_3426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_66, c_60, c_3272, c_3416])).
% 6.93/2.43  tff(c_3427, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_3353])).
% 6.93/2.43  tff(c_3319, plain, (![A_417]: (k2_relat_1(A_417)!='#skF_5' | A_417='#skF_5' | ~v1_relat_1(A_417))), inference(demodulation, [status(thm), theory('equality')], [c_3247, c_3247, c_18])).
% 6.93/2.43  tff(c_3333, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_3270, c_3319])).
% 6.93/2.43  tff(c_3356, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_3333])).
% 6.93/2.43  tff(c_3429, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3427, c_3356])).
% 6.93/2.43  tff(c_3437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3272, c_3429])).
% 6.93/2.43  tff(c_3438, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_3333])).
% 6.93/2.43  tff(c_3513, plain, (![A_439]: (k1_relat_1(k2_funct_1(A_439))=k2_relat_1(A_439) | ~v2_funct_1(A_439) | ~v1_funct_1(A_439) | ~v1_relat_1(A_439))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.93/2.43  tff(c_3525, plain, (k2_relat_1('#skF_5')=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3438, c_3513])).
% 6.93/2.43  tff(c_3529, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_66, c_60, c_3272, c_3525])).
% 6.93/2.43  tff(c_3531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3249, c_3529])).
% 6.93/2.43  tff(c_3532, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_155])).
% 6.93/2.43  tff(c_3533, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_155])).
% 6.93/2.43  tff(c_3548, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3532, c_3533])).
% 6.93/2.43  tff(c_5792, plain, (![A_618]: (k2_relat_1(k2_funct_1(A_618))=k1_relat_1(A_618) | ~v2_funct_1(A_618) | ~v1_funct_1(A_618) | ~v1_relat_1(A_618))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.93/2.43  tff(c_3537, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3532, c_12])).
% 6.93/2.43  tff(c_3711, plain, (![A_469, B_470, C_471]: (k1_relset_1(A_469, B_470, C_471)=k1_relat_1(C_471) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(A_469, B_470))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.93/2.43  tff(c_3799, plain, (![A_490, B_491, A_492]: (k1_relset_1(A_490, B_491, A_492)=k1_relat_1(A_492) | ~r1_tarski(A_492, k2_zfmisc_1(A_490, B_491)))), inference(resolution, [status(thm)], [c_16, c_3711])).
% 6.93/2.43  tff(c_3815, plain, (![A_493, B_494, A_495]: (k1_relset_1(A_493, B_494, A_495)=k1_relat_1(A_495) | ~v1_xboole_0(A_495))), inference(resolution, [status(thm)], [c_108, c_3799])).
% 6.93/2.43  tff(c_3817, plain, (![A_493, B_494]: (k1_relset_1(A_493, B_494, '#skF_5')=k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3537, c_3815])).
% 6.93/2.43  tff(c_3819, plain, (![A_493, B_494]: (k1_relset_1(A_493, B_494, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3548, c_3817])).
% 6.93/2.43  tff(c_48, plain, (![B_26, A_25, C_27]: (k1_xboole_0=B_26 | k1_relset_1(A_25, B_26, C_27)=A_25 | ~v1_funct_2(C_27, A_25, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.93/2.43  tff(c_4373, plain, (![B_549, A_550, C_551]: (B_549='#skF_5' | k1_relset_1(A_550, B_549, C_551)=A_550 | ~v1_funct_2(C_551, A_550, B_549) | ~m1_subset_1(C_551, k1_zfmisc_1(k2_zfmisc_1(A_550, B_549))))), inference(demodulation, [status(thm), theory('equality')], [c_3532, c_48])).
% 6.93/2.43  tff(c_4386, plain, ('#skF_5'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_4373])).
% 6.93/2.43  tff(c_4394, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3819, c_4386])).
% 6.93/2.43  tff(c_4395, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_4394])).
% 6.93/2.43  tff(c_4434, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4395, c_3537])).
% 6.93/2.43  tff(c_4436, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4395, c_148])).
% 6.93/2.43  tff(c_4442, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4395, c_66])).
% 6.93/2.43  tff(c_4441, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4395, c_60])).
% 6.93/2.43  tff(c_4433, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4395, c_4395, c_3548])).
% 6.93/2.43  tff(c_4437, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4395, c_138])).
% 6.93/2.43  tff(c_3689, plain, (![A_466, B_467, C_468]: (k2_relset_1(A_466, B_467, C_468)=k2_relat_1(C_468) | ~m1_subset_1(C_468, k1_zfmisc_1(k2_zfmisc_1(A_466, B_467))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.93/2.43  tff(c_3696, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_3689])).
% 6.93/2.43  tff(c_3699, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3696])).
% 6.93/2.43  tff(c_4424, plain, (k2_relat_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4395, c_3699])).
% 6.93/2.43  tff(c_3672, plain, (![A_464]: (k1_relat_1(k2_funct_1(A_464))=k2_relat_1(A_464) | ~v2_funct_1(A_464) | ~v1_funct_1(A_464) | ~v1_relat_1(A_464))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.93/2.43  tff(c_4595, plain, (![A_557]: (v1_funct_2(k2_funct_1(A_557), k2_relat_1(A_557), k2_relat_1(k2_funct_1(A_557))) | ~v1_funct_1(k2_funct_1(A_557)) | ~v1_relat_1(k2_funct_1(A_557)) | ~v2_funct_1(A_557) | ~v1_funct_1(A_557) | ~v1_relat_1(A_557))), inference(superposition, [status(thm), theory('equality')], [c_3672, c_52])).
% 6.93/2.43  tff(c_4598, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4424, c_4595])).
% 6.93/2.43  tff(c_4606, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4436, c_4442, c_4441, c_4437, c_4598])).
% 6.93/2.43  tff(c_4932, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4606])).
% 6.93/2.43  tff(c_4935, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_4932])).
% 6.93/2.43  tff(c_4939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4436, c_4442, c_4935])).
% 6.93/2.43  tff(c_4941, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4606])).
% 6.93/2.43  tff(c_3535, plain, (![A_12]: (k2_relat_1(A_12)!='#skF_5' | A_12='#skF_5' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_3532, c_3532, c_18])).
% 6.93/2.43  tff(c_4428, plain, (![A_12]: (k2_relat_1(A_12)!='#skF_3' | A_12='#skF_3' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_4395, c_4395, c_3535])).
% 6.93/2.43  tff(c_4949, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_4941, c_4428])).
% 6.93/2.43  tff(c_4963, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_4949])).
% 6.93/2.43  tff(c_4966, plain, (k1_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_4963])).
% 6.93/2.43  tff(c_4969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4436, c_4442, c_4441, c_4433, c_4966])).
% 6.93/2.43  tff(c_4970, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_4949])).
% 6.93/2.43  tff(c_3584, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_137])).
% 6.93/2.43  tff(c_3588, plain, (~r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_3584])).
% 6.93/2.43  tff(c_3592, plain, (~v1_xboole_0(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_108, c_3588])).
% 6.93/2.43  tff(c_4430, plain, (~v1_xboole_0(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4395, c_3592])).
% 6.93/2.43  tff(c_4977, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4970, c_4430])).
% 6.93/2.43  tff(c_4983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4434, c_4977])).
% 6.93/2.43  tff(c_4984, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_4394])).
% 6.93/2.43  tff(c_5036, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4984, c_3537])).
% 6.93/2.43  tff(c_5038, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4984, c_148])).
% 6.93/2.43  tff(c_5044, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4984, c_66])).
% 6.93/2.43  tff(c_5043, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4984, c_60])).
% 6.93/2.43  tff(c_5035, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4984, c_4984, c_3548])).
% 6.93/2.43  tff(c_3660, plain, (![A_463]: (k2_relat_1(k2_funct_1(A_463))=k1_relat_1(A_463) | ~v2_funct_1(A_463) | ~v1_funct_1(A_463) | ~v1_relat_1(A_463))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.93/2.43  tff(c_4986, plain, (![A_578]: (v1_funct_2(k2_funct_1(A_578), k1_relat_1(k2_funct_1(A_578)), k1_relat_1(A_578)) | ~v1_funct_1(k2_funct_1(A_578)) | ~v1_relat_1(k2_funct_1(A_578)) | ~v2_funct_1(A_578) | ~v1_funct_1(A_578) | ~v1_relat_1(A_578))), inference(superposition, [status(thm), theory('equality')], [c_3660, c_52])).
% 6.93/2.43  tff(c_4995, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_5') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3548, c_4986])).
% 6.93/2.43  tff(c_4997, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_66, c_60, c_138, c_4995])).
% 6.93/2.43  tff(c_5633, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4984, c_4984, c_4984, c_4984, c_4997])).
% 6.93/2.43  tff(c_5634, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5633])).
% 6.93/2.43  tff(c_5637, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_5634])).
% 6.93/2.43  tff(c_5641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5038, c_5044, c_5637])).
% 6.93/2.43  tff(c_5643, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5633])).
% 6.93/2.43  tff(c_5030, plain, (![A_12]: (k2_relat_1(A_12)!='#skF_4' | A_12='#skF_4' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_4984, c_4984, c_3535])).
% 6.93/2.43  tff(c_5651, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_5643, c_5030])).
% 6.93/2.43  tff(c_5657, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_5651])).
% 6.93/2.43  tff(c_5660, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_5657])).
% 6.93/2.43  tff(c_5663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5038, c_5044, c_5043, c_5035, c_5660])).
% 6.93/2.43  tff(c_5664, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_5651])).
% 6.93/2.43  tff(c_5032, plain, (~v1_xboole_0(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4984, c_3592])).
% 6.93/2.43  tff(c_5671, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5664, c_5032])).
% 6.93/2.43  tff(c_5678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5036, c_5671])).
% 6.93/2.43  tff(c_5680, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_137])).
% 6.93/2.43  tff(c_5687, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_5680, c_32])).
% 6.93/2.43  tff(c_5701, plain, (![A_608]: (k2_relat_1(A_608)!='#skF_5' | A_608='#skF_5' | ~v1_relat_1(A_608))), inference(demodulation, [status(thm), theory('equality')], [c_3532, c_3532, c_18])).
% 6.93/2.43  tff(c_5714, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_5687, c_5701])).
% 6.93/2.43  tff(c_5739, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_5714])).
% 6.93/2.43  tff(c_5801, plain, (k1_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5792, c_5739])).
% 6.93/2.43  tff(c_5808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_66, c_60, c_3548, c_5801])).
% 6.93/2.43  tff(c_5809, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_5714])).
% 6.93/2.43  tff(c_5810, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_5714])).
% 6.93/2.43  tff(c_5832, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5809, c_5810])).
% 6.93/2.43  tff(c_6016, plain, (![A_638, B_639, C_640]: (k2_relset_1(A_638, B_639, C_640)=k2_relat_1(C_640) | ~m1_subset_1(C_640, k1_zfmisc_1(k2_zfmisc_1(A_638, B_639))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.93/2.43  tff(c_6032, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_6016])).
% 6.93/2.43  tff(c_6040, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5832, c_58, c_6032])).
% 6.93/2.43  tff(c_5679, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_137])).
% 6.93/2.43  tff(c_5814, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5809, c_5679])).
% 6.93/2.43  tff(c_6050, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6040, c_5814])).
% 6.93/2.43  tff(c_6055, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6040, c_6040, c_3548])).
% 6.93/2.43  tff(c_5813, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5809, c_5680])).
% 6.93/2.43  tff(c_6049, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6040, c_5813])).
% 6.93/2.43  tff(c_34, plain, (![A_19, B_20, C_21]: (k1_relset_1(A_19, B_20, C_21)=k1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.93/2.43  tff(c_6253, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6049, c_34])).
% 6.93/2.43  tff(c_6264, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6055, c_6253])).
% 6.93/2.43  tff(c_6057, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6040, c_3532])).
% 6.93/2.43  tff(c_42, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.93/2.43  tff(c_6367, plain, (![C_655, B_656]: (v1_funct_2(C_655, '#skF_4', B_656) | k1_relset_1('#skF_4', B_656, C_655)!='#skF_4' | ~m1_subset_1(C_655, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_656))))), inference(demodulation, [status(thm), theory('equality')], [c_6057, c_6057, c_6057, c_6057, c_42])).
% 6.93/2.43  tff(c_6373, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_6049, c_6367])).
% 6.93/2.43  tff(c_6383, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6264, c_6373])).
% 6.93/2.43  tff(c_6385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6050, c_6383])).
% 6.93/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.43  
% 6.93/2.43  Inference rules
% 6.93/2.43  ----------------------
% 6.93/2.43  #Ref     : 0
% 6.93/2.43  #Sup     : 1331
% 6.93/2.43  #Fact    : 0
% 6.93/2.43  #Define  : 0
% 6.93/2.43  #Split   : 41
% 6.93/2.43  #Chain   : 0
% 6.93/2.43  #Close   : 0
% 6.93/2.43  
% 6.93/2.43  Ordering : KBO
% 6.93/2.43  
% 6.93/2.43  Simplification rules
% 6.93/2.43  ----------------------
% 6.93/2.43  #Subsume      : 248
% 6.93/2.43  #Demod        : 1364
% 6.93/2.43  #Tautology    : 563
% 6.93/2.43  #SimpNegUnit  : 34
% 6.93/2.43  #BackRed      : 221
% 6.93/2.43  
% 6.93/2.43  #Partial instantiations: 0
% 6.93/2.43  #Strategies tried      : 1
% 6.93/2.43  
% 6.93/2.43  Timing (in seconds)
% 6.93/2.43  ----------------------
% 6.93/2.43  Preprocessing        : 0.32
% 6.93/2.43  Parsing              : 0.17
% 6.93/2.43  CNF conversion       : 0.02
% 6.93/2.43  Main loop            : 1.26
% 6.93/2.43  Inferencing          : 0.45
% 6.93/2.43  Reduction            : 0.40
% 6.93/2.43  Demodulation         : 0.27
% 6.93/2.43  BG Simplification    : 0.05
% 6.93/2.43  Subsumption          : 0.24
% 6.93/2.43  Abstraction          : 0.05
% 6.93/2.43  MUC search           : 0.00
% 6.93/2.43  Cooper               : 0.00
% 6.93/2.43  Total                : 1.66
% 6.93/2.43  Index Insertion      : 0.00
% 6.93/2.44  Index Deletion       : 0.00
% 6.93/2.44  Index Matching       : 0.00
% 6.93/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
