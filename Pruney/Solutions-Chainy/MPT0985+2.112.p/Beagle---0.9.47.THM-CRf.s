%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:44 EST 2020

% Result     : Theorem 9.02s
% Output     : CNFRefutation 9.32s
% Verified   : 
% Statistics : Number of formulae       :  422 (8148 expanded)
%              Number of leaves         :   43 (2463 expanded)
%              Depth                    :   19
%              Number of atoms          :  756 (21012 expanded)
%              Number of equality atoms :  225 (7970 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_151,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_111,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_124,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_14152,plain,(
    ! [C_2614,A_2615,B_2616] :
      ( v1_relat_1(C_2614)
      | ~ m1_subset_1(C_2614,k1_zfmisc_1(k2_zfmisc_1(A_2615,B_2616))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14174,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_14152])).

tff(c_90,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_84,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_82,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_14487,plain,(
    ! [A_2665,B_2666,C_2667] :
      ( k2_relset_1(A_2665,B_2666,C_2667) = k2_relat_1(C_2667)
      | ~ m1_subset_1(C_2667,k1_zfmisc_1(k2_zfmisc_1(A_2665,B_2666))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14500,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_14487])).

tff(c_14511,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_14500])).

tff(c_42,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [A_16] :
      ( v1_funct_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_80,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_169,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_172,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_169])).

tff(c_175,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_172])).

tff(c_344,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_354,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_344])).

tff(c_365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_354])).

tff(c_366,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_434,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_621,plain,(
    ! [C_113,B_114,A_115] :
      ( ~ v1_xboole_0(C_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(C_113))
      | ~ r2_hidden(A_115,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_635,plain,(
    ! [A_115] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_115,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_86,c_621])).

tff(c_645,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_635])).

tff(c_88,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_898,plain,(
    ! [A_154,B_155,C_156] :
      ( k1_relset_1(A_154,B_155,C_156) = k1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_917,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_898])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_534,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_552,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_534])).

tff(c_1025,plain,(
    ! [A_170,B_171,C_172] :
      ( k2_relset_1(A_170,B_171,C_172) = k2_relat_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1038,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_1025])).

tff(c_1049,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1038])).

tff(c_34,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_367,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_701,plain,(
    ! [A_127] :
      ( k1_relat_1(k2_funct_1(A_127)) = k2_relat_1(A_127)
      | ~ v2_funct_1(A_127)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_76,plain,(
    ! [A_34] :
      ( v1_funct_2(A_34,k1_relat_1(A_34),k2_relat_1(A_34))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2581,plain,(
    ! [A_304] :
      ( v1_funct_2(k2_funct_1(A_304),k2_relat_1(A_304),k2_relat_1(k2_funct_1(A_304)))
      | ~ v1_funct_1(k2_funct_1(A_304))
      | ~ v1_relat_1(k2_funct_1(A_304))
      | ~ v2_funct_1(A_304)
      | ~ v1_funct_1(A_304)
      | ~ v1_relat_1(A_304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_76])).

tff(c_2587,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_2581])).

tff(c_2596,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_90,c_84,c_367,c_2587])).

tff(c_2597,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2596])).

tff(c_2600,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_2597])).

tff(c_2604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_90,c_2600])).

tff(c_2606,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2596])).

tff(c_1262,plain,(
    ! [B_193,A_194,C_195] :
      ( k1_xboole_0 = B_193
      | k1_relset_1(A_194,B_193,C_195) = A_194
      | ~ v1_funct_2(C_195,A_194,B_193)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1278,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_1262])).

tff(c_1295,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_917,c_1278])).

tff(c_1297,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1295])).

tff(c_40,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_970,plain,(
    ! [A_163] :
      ( m1_subset_1(A_163,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_163),k2_relat_1(A_163))))
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3042,plain,(
    ! [A_331] :
      ( m1_subset_1(k2_funct_1(A_331),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_331)),k1_relat_1(A_331))))
      | ~ v1_funct_1(k2_funct_1(A_331))
      | ~ v1_relat_1(k2_funct_1(A_331))
      | ~ v2_funct_1(A_331)
      | ~ v1_funct_1(A_331)
      | ~ v1_relat_1(A_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_970])).

tff(c_3068,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1297,c_3042])).

tff(c_3088,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_90,c_84,c_2606,c_367,c_3068])).

tff(c_3113,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3088])).

tff(c_3126,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_90,c_84,c_1049,c_3113])).

tff(c_3128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_3126])).

tff(c_3129,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1295])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3171,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3129,c_8])).

tff(c_20,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3166,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3129,c_3129,c_20])).

tff(c_74,plain,(
    ! [A_34] :
      ( m1_subset_1(A_34,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_34),k2_relat_1(A_34))))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1053,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_74])).

tff(c_1060,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_90,c_1053])).

tff(c_28,plain,(
    ! [C_15,B_14,A_13] :
      ( ~ v1_xboole_0(C_15)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(C_15))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1081,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))
      | ~ r2_hidden(A_13,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1060,c_28])).

tff(c_1117,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1081])).

tff(c_3272,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3166,c_1117])).

tff(c_3281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3171,c_3272])).

tff(c_3284,plain,(
    ! [A_339] : ~ r2_hidden(A_339,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1081])).

tff(c_3297,plain,(
    ! [B_340] : r1_tarski('#skF_5',B_340) ),
    inference(resolution,[status(thm)],[c_6,c_3284])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_374,plain,(
    ! [B_85,A_86] :
      ( B_85 = A_86
      | ~ r1_tarski(B_85,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_396,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_374])).

tff(c_3333,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3297,c_396])).

tff(c_60,plain,(
    ! [B_29,A_28,C_30] :
      ( k1_xboole_0 = B_29
      | k1_relset_1(A_28,B_29,C_30) = A_28
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3503,plain,(
    ! [B_349,A_350,C_351] :
      ( B_349 = '#skF_5'
      | k1_relset_1(A_350,B_349,C_351) = A_350
      | ~ v1_funct_2(C_351,A_350,B_349)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(A_350,B_349))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3333,c_60])).

tff(c_3525,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_3503])).

tff(c_3537,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_917,c_3525])).

tff(c_3649,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3537])).

tff(c_3283,plain,(
    v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1081])).

tff(c_3650,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3649,c_3283])).

tff(c_3657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_645,c_3650])).

tff(c_3658,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3537])).

tff(c_3364,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3333,c_8])).

tff(c_3673,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3658,c_3364])).

tff(c_3359,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3333,c_3333,c_20])).

tff(c_3666,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3658,c_3658,c_3359])).

tff(c_4000,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3666,c_645])).

tff(c_4004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3673,c_4000])).

tff(c_4006,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4353,plain,(
    ! [B_391,A_392,A_393] :
      ( ~ v1_xboole_0(B_391)
      | ~ r2_hidden(A_392,A_393)
      | ~ r1_tarski(A_393,B_391) ) ),
    inference(resolution,[status(thm)],[c_26,c_621])).

tff(c_4357,plain,(
    ! [B_394,A_395,B_396] :
      ( ~ v1_xboole_0(B_394)
      | ~ r1_tarski(A_395,B_394)
      | r1_tarski(A_395,B_396) ) ),
    inference(resolution,[status(thm)],[c_6,c_4353])).

tff(c_4396,plain,(
    ! [B_400,B_401] :
      ( ~ v1_xboole_0(B_400)
      | r1_tarski(B_400,B_401) ) ),
    inference(resolution,[status(thm)],[c_14,c_4357])).

tff(c_141,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_149,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_86,c_141])).

tff(c_391,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_149,c_374])).

tff(c_502,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_4416,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4396,c_502])).

tff(c_4427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4006,c_4416])).

tff(c_4428,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_4431,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4428,c_86])).

tff(c_4477,plain,(
    ! [C_404,A_405,B_406] :
      ( v1_relat_1(C_404)
      | ~ m1_subset_1(C_404,k1_zfmisc_1(k2_zfmisc_1(A_405,B_406))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4525,plain,(
    ! [C_411] :
      ( v1_relat_1(C_411)
      | ~ m1_subset_1(C_411,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4428,c_4477])).

tff(c_4538,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4431,c_4525])).

tff(c_8017,plain,(
    ! [B_708,C_709,A_710] :
      ( k1_xboole_0 = B_708
      | v1_funct_2(C_709,A_710,B_708)
      | k1_relset_1(A_710,B_708,C_709) != A_710
      | ~ m1_subset_1(C_709,k1_zfmisc_1(k2_zfmisc_1(A_710,B_708))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8026,plain,(
    ! [C_709] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(C_709,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',C_709) != '#skF_3'
      | ~ m1_subset_1(C_709,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4428,c_8017])).

tff(c_8081,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8026])).

tff(c_4591,plain,(
    ! [B_418,A_419] :
      ( k1_xboole_0 = B_418
      | k1_xboole_0 = A_419
      | k2_zfmisc_1(A_419,B_418) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4594,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4428,c_4591])).

tff(c_4609,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4594])).

tff(c_8106,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8081,c_4609])).

tff(c_152,plain,(
    ! [A_59,B_60] : m1_subset_1('#skF_2'(A_59,B_60),k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_368,plain,(
    ! [A_83] : m1_subset_1('#skF_2'(A_83,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_152])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_372,plain,(
    ! [A_83] : r1_tarski('#skF_2'(A_83,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_368,c_24])).

tff(c_376,plain,(
    ! [A_83] :
      ( '#skF_2'(A_83,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,'#skF_2'(A_83,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_372,c_374])).

tff(c_387,plain,(
    ! [A_83] : '#skF_2'(A_83,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_376])).

tff(c_8117,plain,(
    ! [A_83] : '#skF_2'(A_83,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8081,c_8081,c_387])).

tff(c_4848,plain,(
    ! [A_457,B_458,C_459] :
      ( k2_relset_1(A_457,B_458,C_459) = k2_relat_1(C_459)
      | ~ m1_subset_1(C_459,k1_zfmisc_1(k2_zfmisc_1(A_457,B_458))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4906,plain,(
    ! [C_464] :
      ( k2_relset_1('#skF_3','#skF_4',C_464) = k2_relat_1(C_464)
      | ~ m1_subset_1(C_464,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4428,c_4848])).

tff(c_4912,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4431,c_4906])).

tff(c_4920,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4912])).

tff(c_5065,plain,(
    ! [A_474,B_475,C_476] :
      ( k1_relset_1(A_474,B_475,C_476) = k1_relat_1(C_476)
      | ~ m1_subset_1(C_476,k1_zfmisc_1(k2_zfmisc_1(A_474,B_475))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5124,plain,(
    ! [C_481] :
      ( k1_relset_1('#skF_3','#skF_4',C_481) = k1_relat_1(C_481)
      | ~ m1_subset_1(C_481,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4428,c_5065])).

tff(c_5136,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4431,c_5124])).

tff(c_5597,plain,(
    ! [B_531,C_532,A_533] :
      ( k1_xboole_0 = B_531
      | v1_funct_2(C_532,A_533,B_531)
      | k1_relset_1(A_533,B_531,C_532) != A_533
      | ~ m1_subset_1(C_532,k1_zfmisc_1(k2_zfmisc_1(A_533,B_531))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5606,plain,(
    ! [C_532] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(C_532,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',C_532) != '#skF_3'
      | ~ m1_subset_1(C_532,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4428,c_5597])).

tff(c_5664,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5606])).

tff(c_5702,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5664,c_8])).

tff(c_5697,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5664,c_5664,c_20])).

tff(c_4968,plain,(
    ! [A_467] :
      ( m1_subset_1(A_467,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_467),k2_relat_1(A_467))))
      | ~ v1_funct_1(A_467)
      | ~ v1_relat_1(A_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4982,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4920,c_4968])).

tff(c_4994,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_90,c_4982])).

tff(c_5008,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))
      | ~ r2_hidden(A_13,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4994,c_28])).

tff(c_5031,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5008])).

tff(c_5843,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5697,c_5031])).

tff(c_5849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5702,c_5843])).

tff(c_5851,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5606])).

tff(c_5852,plain,(
    ! [B_548,A_549,C_550] :
      ( k1_xboole_0 = B_548
      | k1_relset_1(A_549,B_548,C_550) = A_549
      | ~ v1_funct_2(C_550,A_549,B_548)
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k2_zfmisc_1(A_549,B_548))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5861,plain,(
    ! [C_550] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_550) = '#skF_3'
      | ~ v1_funct_2(C_550,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_550,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4428,c_5852])).

tff(c_5971,plain,(
    ! [C_559] :
      ( k1_relset_1('#skF_3','#skF_4',C_559) = '#skF_3'
      | ~ v1_funct_2(C_559,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_559,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5851,c_5861])).

tff(c_5977,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_4431,c_5971])).

tff(c_5987,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5136,c_5977])).

tff(c_4836,plain,(
    ! [A_456] :
      ( k2_relat_1(k2_funct_1(A_456)) = k1_relat_1(A_456)
      | ~ v2_funct_1(A_456)
      | ~ v1_funct_1(A_456)
      | ~ v1_relat_1(A_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6962,plain,(
    ! [A_615] :
      ( v1_funct_2(k2_funct_1(A_615),k1_relat_1(k2_funct_1(A_615)),k1_relat_1(A_615))
      | ~ v1_funct_1(k2_funct_1(A_615))
      | ~ v1_relat_1(k2_funct_1(A_615))
      | ~ v2_funct_1(A_615)
      | ~ v1_funct_1(A_615)
      | ~ v1_relat_1(A_615) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4836,c_76])).

tff(c_6971,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5987,c_6962])).

tff(c_6988,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_90,c_84,c_367,c_6971])).

tff(c_6993,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6988])).

tff(c_6996,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_6993])).

tff(c_7000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_90,c_6996])).

tff(c_7002,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6988])).

tff(c_7262,plain,(
    ! [A_645] :
      ( m1_subset_1(k2_funct_1(A_645),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_645)),k1_relat_1(A_645))))
      | ~ v1_funct_1(k2_funct_1(A_645))
      | ~ v1_relat_1(k2_funct_1(A_645))
      | ~ v2_funct_1(A_645)
      | ~ v1_funct_1(A_645)
      | ~ v1_relat_1(A_645) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4968])).

tff(c_7288,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5987,c_7262])).

tff(c_7311,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_90,c_84,c_7002,c_367,c_7288])).

tff(c_7338,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_7311])).

tff(c_7351,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_90,c_84,c_4920,c_7338])).

tff(c_7353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_7351])).

tff(c_7356,plain,(
    ! [A_646] : ~ r2_hidden(A_646,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5008])).

tff(c_7361,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_7356])).

tff(c_72,plain,(
    ! [A_31,B_32] : m1_subset_1('#skF_2'(A_31,B_32),k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4436,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4428,c_72])).

tff(c_4449,plain,(
    r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_4436,c_24])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4452,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4449,c_10])).

tff(c_4800,plain,(
    ~ r1_tarski('#skF_5','#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4452])).

tff(c_7365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7361,c_4800])).

tff(c_7366,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4452])).

tff(c_8307,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8117,c_7366])).

tff(c_8309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8106,c_8307])).

tff(c_8311,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8026])).

tff(c_62,plain,(
    ! [A_31,B_32] : v1_funct_2('#skF_2'(A_31,B_32),A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7614,plain,(
    ! [A_670,B_671,C_672] :
      ( k1_relset_1(A_670,B_671,C_672) = k1_relat_1(C_672)
      | ~ m1_subset_1(C_672,k1_zfmisc_1(k2_zfmisc_1(A_670,B_671))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7635,plain,(
    ! [A_31,B_32] : k1_relset_1(A_31,B_32,'#skF_2'(A_31,B_32)) = k1_relat_1('#skF_2'(A_31,B_32)) ),
    inference(resolution,[status(thm)],[c_72,c_7614])).

tff(c_8312,plain,(
    ! [B_725,A_726,C_727] :
      ( k1_xboole_0 = B_725
      | k1_relset_1(A_726,B_725,C_727) = A_726
      | ~ v1_funct_2(C_727,A_726,B_725)
      | ~ m1_subset_1(C_727,k1_zfmisc_1(k2_zfmisc_1(A_726,B_725))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8324,plain,(
    ! [B_32,A_31] :
      ( k1_xboole_0 = B_32
      | k1_relset_1(A_31,B_32,'#skF_2'(A_31,B_32)) = A_31
      | ~ v1_funct_2('#skF_2'(A_31,B_32),A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_72,c_8312])).

tff(c_8346,plain,(
    ! [B_728,A_729] :
      ( k1_xboole_0 = B_728
      | k1_relat_1('#skF_2'(A_729,B_728)) = A_729 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_7635,c_8324])).

tff(c_8364,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7366,c_8346])).

tff(c_8379,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_8311,c_8364])).

tff(c_7551,plain,(
    ! [A_665,B_666,C_667] :
      ( k2_relset_1(A_665,B_666,C_667) = k2_relat_1(C_667)
      | ~ m1_subset_1(C_667,k1_zfmisc_1(k2_zfmisc_1(A_665,B_666))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7574,plain,(
    ! [A_668,B_669] : k2_relset_1(A_668,B_669,'#skF_2'(A_668,B_669)) = k2_relat_1('#skF_2'(A_668,B_669)) ),
    inference(resolution,[status(thm)],[c_72,c_7551])).

tff(c_7583,plain,(
    k2_relat_1('#skF_2'('#skF_3','#skF_4')) = k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7366,c_7574])).

tff(c_7592,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7366,c_82,c_7583])).

tff(c_7428,plain,(
    ! [A_652] :
      ( k1_relat_1(k2_funct_1(A_652)) = k2_relat_1(A_652)
      | ~ v2_funct_1(A_652)
      | ~ v1_funct_1(A_652)
      | ~ v1_relat_1(A_652) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9529,plain,(
    ! [A_830] :
      ( v1_funct_2(k2_funct_1(A_830),k2_relat_1(A_830),k2_relat_1(k2_funct_1(A_830)))
      | ~ v1_funct_1(k2_funct_1(A_830))
      | ~ v1_relat_1(k2_funct_1(A_830))
      | ~ v2_funct_1(A_830)
      | ~ v1_funct_1(A_830)
      | ~ v1_relat_1(A_830) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7428,c_76])).

tff(c_9535,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7592,c_9529])).

tff(c_9544,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_90,c_84,c_367,c_9535])).

tff(c_9545,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_9544])).

tff(c_9548,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_9545])).

tff(c_9552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_90,c_9548])).

tff(c_9554,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_9544])).

tff(c_7493,plain,(
    ! [A_659] :
      ( m1_subset_1(A_659,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_659),k2_relat_1(A_659))))
      | ~ v1_funct_1(A_659)
      | ~ v1_relat_1(A_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_10037,plain,(
    ! [A_872] :
      ( m1_subset_1(k2_funct_1(A_872),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_872),k2_relat_1(k2_funct_1(A_872)))))
      | ~ v1_funct_1(k2_funct_1(A_872))
      | ~ v1_relat_1(k2_funct_1(A_872))
      | ~ v2_funct_1(A_872)
      | ~ v1_funct_1(A_872)
      | ~ v1_relat_1(A_872) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_7493])).

tff(c_10060,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7592,c_10037])).

tff(c_10075,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_90,c_84,c_9554,c_367,c_10060])).

tff(c_10098,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_10075])).

tff(c_10111,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_90,c_84,c_8379,c_10098])).

tff(c_10113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_10111])).

tff(c_10115,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4594])).

tff(c_10114,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4594])).

tff(c_10141,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10115,c_10115,c_10114])).

tff(c_10142,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10141])).

tff(c_22,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10127,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_5',B_10) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10115,c_10115,c_22])).

tff(c_10232,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10142,c_10142,c_10127])).

tff(c_10153,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10142,c_434])).

tff(c_10437,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10232,c_10153])).

tff(c_10146,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10142,c_4538])).

tff(c_10158,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10142,c_90])).

tff(c_10157,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10142,c_84])).

tff(c_10154,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10142,c_367])).

tff(c_10126,plain,(
    ! [A_83] : '#skF_2'(A_83,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10115,c_10115,c_387])).

tff(c_10200,plain,(
    ! [A_83] : '#skF_2'(A_83,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10142,c_10142,c_10126])).

tff(c_10694,plain,(
    ! [A_920,B_921,C_922] :
      ( k2_relset_1(A_920,B_921,C_922) = k2_relat_1(C_922)
      | ~ m1_subset_1(C_922,k1_zfmisc_1(k2_zfmisc_1(A_920,B_921))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10787,plain,(
    ! [A_932,B_933] : k2_relset_1(A_932,B_933,'#skF_2'(A_932,B_933)) = k2_relat_1('#skF_2'(A_932,B_933)) ),
    inference(resolution,[status(thm)],[c_72,c_10694])).

tff(c_10799,plain,(
    ! [A_83] : k2_relat_1('#skF_2'(A_83,'#skF_4')) = k2_relset_1(A_83,'#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10200,c_10787])).

tff(c_10811,plain,(
    ! [A_935] : k2_relset_1(A_935,'#skF_4','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10200,c_10799])).

tff(c_10155,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10142,c_82])).

tff(c_10818,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_10811,c_10155])).

tff(c_10499,plain,(
    ! [A_893] :
      ( k1_relat_1(k2_funct_1(A_893)) = k2_relat_1(A_893)
      | ~ v2_funct_1(A_893)
      | ~ v1_funct_1(A_893)
      | ~ v1_relat_1(A_893) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_11778,plain,(
    ! [A_1049] :
      ( v1_funct_2(k2_funct_1(A_1049),k2_relat_1(A_1049),k2_relat_1(k2_funct_1(A_1049)))
      | ~ v1_funct_1(k2_funct_1(A_1049))
      | ~ v1_relat_1(k2_funct_1(A_1049))
      | ~ v2_funct_1(A_1049)
      | ~ v1_funct_1(A_1049)
      | ~ v1_relat_1(A_1049) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10499,c_76])).

tff(c_11781,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10818,c_11778])).

tff(c_11789,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10146,c_10158,c_10157,c_10154,c_11781])).

tff(c_11790,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11789])).

tff(c_11793,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_11790])).

tff(c_11797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10146,c_10158,c_11793])).

tff(c_11799,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11789])).

tff(c_10584,plain,(
    ! [A_907] :
      ( m1_subset_1(A_907,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_907),k2_relat_1(A_907))))
      | ~ v1_funct_1(A_907)
      | ~ v1_relat_1(A_907) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_11984,plain,(
    ! [A_1070] :
      ( m1_subset_1(k2_funct_1(A_1070),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1070),k2_relat_1(k2_funct_1(A_1070)))))
      | ~ v1_funct_1(k2_funct_1(A_1070))
      | ~ v1_relat_1(k2_funct_1(A_1070))
      | ~ v2_funct_1(A_1070)
      | ~ v1_funct_1(A_1070)
      | ~ v1_relat_1(A_1070) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_10584])).

tff(c_12007,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10818,c_11984])).

tff(c_12022,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10146,c_10158,c_10157,c_11799,c_10154,c_10232,c_12007])).

tff(c_12024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10437,c_12022])).

tff(c_12025,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10141])).

tff(c_12026,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10141])).

tff(c_12047,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12025,c_12026])).

tff(c_10128,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10115,c_10115,c_20])).

tff(c_12106,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12025,c_12025,c_10128])).

tff(c_12037,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12025,c_434])).

tff(c_12269,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12106,c_12037])).

tff(c_12030,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12025,c_4538])).

tff(c_12042,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12025,c_90])).

tff(c_12041,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12025,c_84])).

tff(c_163,plain,(
    ! [B_61] : m1_subset_1('#skF_2'(k1_xboole_0,B_61),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_152])).

tff(c_167,plain,(
    ! [B_61] : r1_tarski('#skF_2'(k1_xboole_0,B_61),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_163,c_24])).

tff(c_378,plain,(
    ! [B_61] :
      ( '#skF_2'(k1_xboole_0,B_61) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,'#skF_2'(k1_xboole_0,B_61)) ) ),
    inference(resolution,[status(thm)],[c_167,c_374])).

tff(c_390,plain,(
    ! [B_61] : '#skF_2'(k1_xboole_0,B_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_378])).

tff(c_10123,plain,(
    ! [B_61] : '#skF_2'('#skF_5',B_61) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10115,c_10115,c_390])).

tff(c_12136,plain,(
    ! [B_61] : '#skF_2'('#skF_3',B_61) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12025,c_12025,c_10123])).

tff(c_12662,plain,(
    ! [A_1130,B_1131,C_1132] :
      ( k1_relset_1(A_1130,B_1131,C_1132) = k1_relat_1(C_1132)
      | ~ m1_subset_1(C_1132,k1_zfmisc_1(k2_zfmisc_1(A_1130,B_1131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12684,plain,(
    ! [A_31,B_32] : k1_relset_1(A_31,B_32,'#skF_2'(A_31,B_32)) = k1_relat_1('#skF_2'(A_31,B_32)) ),
    inference(resolution,[status(thm)],[c_72,c_12662])).

tff(c_12028,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12025,c_10115])).

tff(c_12841,plain,(
    ! [B_1156,A_1157,C_1158] :
      ( B_1156 = '#skF_3'
      | k1_relset_1(A_1157,B_1156,C_1158) = A_1157
      | ~ v1_funct_2(C_1158,A_1157,B_1156)
      | ~ m1_subset_1(C_1158,k1_zfmisc_1(k2_zfmisc_1(A_1157,B_1156))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12028,c_60])).

tff(c_12856,plain,(
    ! [B_32,A_31] :
      ( B_32 = '#skF_3'
      | k1_relset_1(A_31,B_32,'#skF_2'(A_31,B_32)) = A_31
      | ~ v1_funct_2('#skF_2'(A_31,B_32),A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_72,c_12841])).

tff(c_12873,plain,(
    ! [B_1159,A_1160] :
      ( B_1159 = '#skF_3'
      | k1_relat_1('#skF_2'(A_1160,B_1159)) = A_1160 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12684,c_12856])).

tff(c_12891,plain,(
    ! [B_61] :
      ( B_61 = '#skF_3'
      | k1_relat_1('#skF_3') = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12136,c_12873])).

tff(c_12899,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12891])).

tff(c_12038,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12025,c_367])).

tff(c_12480,plain,(
    ! [A_1114,B_1115,C_1116] :
      ( k2_relset_1(A_1114,B_1115,C_1116) = k2_relat_1(C_1116)
      | ~ m1_subset_1(C_1116,k1_zfmisc_1(k2_zfmisc_1(A_1114,B_1115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12507,plain,(
    ! [A_1119,B_1120] : k2_relset_1(A_1119,B_1120,'#skF_2'(A_1119,B_1120)) = k2_relat_1('#skF_2'(A_1119,B_1120)) ),
    inference(resolution,[status(thm)],[c_72,c_12480])).

tff(c_12519,plain,(
    ! [B_61] : k2_relat_1('#skF_2'('#skF_3',B_61)) = k2_relset_1('#skF_3',B_61,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12136,c_12507])).

tff(c_12531,plain,(
    ! [B_1122] : k2_relset_1('#skF_3',B_1122,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12136,c_12519])).

tff(c_12039,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12025,c_82])).

tff(c_12538,plain,(
    k2_relat_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_12531,c_12039])).

tff(c_12276,plain,(
    ! [A_1087] :
      ( k1_relat_1(k2_funct_1(A_1087)) = k2_relat_1(A_1087)
      | ~ v2_funct_1(A_1087)
      | ~ v1_funct_1(A_1087)
      | ~ v1_relat_1(A_1087) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_13480,plain,(
    ! [A_1222] :
      ( v1_funct_2(k2_funct_1(A_1222),k2_relat_1(A_1222),k2_relat_1(k2_funct_1(A_1222)))
      | ~ v1_funct_1(k2_funct_1(A_1222))
      | ~ v1_relat_1(k2_funct_1(A_1222))
      | ~ v2_funct_1(A_1222)
      | ~ v1_funct_1(A_1222)
      | ~ v1_relat_1(A_1222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12276,c_76])).

tff(c_13483,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_4',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12538,c_13480])).

tff(c_13491,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_4',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12030,c_12042,c_12041,c_12038,c_13483])).

tff(c_13492,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_13491])).

tff(c_13495,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_13492])).

tff(c_13499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12030,c_12042,c_13495])).

tff(c_13501,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_13491])).

tff(c_12550,plain,(
    ! [A_1123] :
      ( m1_subset_1(A_1123,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1123),k2_relat_1(A_1123))))
      | ~ v1_funct_1(A_1123)
      | ~ v1_relat_1(A_1123) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_13713,plain,(
    ! [A_1253] :
      ( m1_subset_1(k2_funct_1(A_1253),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1253),k2_relat_1(k2_funct_1(A_1253)))))
      | ~ v1_funct_1(k2_funct_1(A_1253))
      | ~ v1_relat_1(k2_funct_1(A_1253))
      | ~ v2_funct_1(A_1253)
      | ~ v1_funct_1(A_1253)
      | ~ v1_relat_1(A_1253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_12550])).

tff(c_13736,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12538,c_13713])).

tff(c_13751,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12030,c_12042,c_12041,c_13501,c_12038,c_13736])).

tff(c_13774,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_13751])).

tff(c_13787,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12030,c_12042,c_12041,c_12106,c_12899,c_13774])).

tff(c_13789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12269,c_13787])).

tff(c_13792,plain,(
    ! [B_1254] : B_1254 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12891])).

tff(c_12577,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_4')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12538,c_74])).

tff(c_12584,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12030,c_12042,c_12577])).

tff(c_48,plain,(
    ! [A_25,B_26,C_27] :
      ( k2_relset_1(A_25,B_26,C_27) = k2_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12614,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_4','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12584,c_48])).

tff(c_12624,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12538,c_12614])).

tff(c_13867,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_13792,c_12624])).

tff(c_14058,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12047,c_13867])).

tff(c_14059,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_14060,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_14645,plain,(
    ! [A_2678,B_2679,C_2680] :
      ( k1_relset_1(A_2678,B_2679,C_2680) = k1_relat_1(C_2680)
      | ~ m1_subset_1(C_2680,k1_zfmisc_1(k2_zfmisc_1(A_2678,B_2679))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14673,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_14060,c_14645])).

tff(c_15199,plain,(
    ! [B_2733,C_2734,A_2735] :
      ( k1_xboole_0 = B_2733
      | v1_funct_2(C_2734,A_2735,B_2733)
      | k1_relset_1(A_2735,B_2733,C_2734) != A_2735
      | ~ m1_subset_1(C_2734,k1_zfmisc_1(k2_zfmisc_1(A_2735,B_2733))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_15205,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_14060,c_15199])).

tff(c_15224,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14673,c_15205])).

tff(c_15225,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_14059,c_15224])).

tff(c_15248,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_15225])).

tff(c_15251,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_15248])).

tff(c_15254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14174,c_90,c_84,c_14511,c_15251])).

tff(c_15255,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_15225])).

tff(c_15297,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15255,c_8])).

tff(c_15291,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_3',B_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15255,c_15255,c_22])).

tff(c_14256,plain,(
    ! [C_2628,B_2629,A_2630] :
      ( ~ v1_xboole_0(C_2628)
      | ~ m1_subset_1(B_2629,k1_zfmisc_1(C_2628))
      | ~ r2_hidden(A_2630,B_2629) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14273,plain,(
    ! [A_2630] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_2630,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_86,c_14256])).

tff(c_14285,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14273])).

tff(c_15421,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15291,c_14285])).

tff(c_15427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15297,c_15421])).

tff(c_15429,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_14273])).

tff(c_15771,plain,(
    ! [B_2761,A_2762,A_2763] :
      ( ~ v1_xboole_0(B_2761)
      | ~ r2_hidden(A_2762,A_2763)
      | ~ r1_tarski(A_2763,B_2761) ) ),
    inference(resolution,[status(thm)],[c_26,c_14256])).

tff(c_15775,plain,(
    ! [B_2764,A_2765,B_2766] :
      ( ~ v1_xboole_0(B_2764)
      | ~ r1_tarski(A_2765,B_2764)
      | r1_tarski(A_2765,B_2766) ) ),
    inference(resolution,[status(thm)],[c_6,c_15771])).

tff(c_15789,plain,(
    ! [B_2767,B_2768] :
      ( ~ v1_xboole_0(B_2767)
      | r1_tarski(B_2767,B_2768) ) ),
    inference(resolution,[status(thm)],[c_14,c_15775])).

tff(c_14131,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_15809,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_15789,c_14131])).

tff(c_15820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15429,c_15809])).

tff(c_15821,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_15824,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15821,c_86])).

tff(c_15870,plain,(
    ! [C_2771,A_2772,B_2773] :
      ( v1_relat_1(C_2771)
      | ~ m1_subset_1(C_2771,k1_zfmisc_1(k2_zfmisc_1(A_2772,B_2773))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_15915,plain,(
    ! [C_2776] :
      ( v1_relat_1(C_2776)
      | ~ m1_subset_1(C_2776,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15821,c_15870])).

tff(c_15928,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_15824,c_15915])).

tff(c_16507,plain,(
    ! [A_2846,B_2847,C_2848] :
      ( k2_relset_1(A_2846,B_2847,C_2848) = k2_relat_1(C_2848)
      | ~ m1_subset_1(C_2848,k1_zfmisc_1(k2_zfmisc_1(A_2846,B_2847))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16552,plain,(
    ! [C_2852] :
      ( k2_relset_1('#skF_3','#skF_4',C_2852) = k2_relat_1(C_2852)
      | ~ m1_subset_1(C_2852,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15821,c_16507])).

tff(c_16558,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_15824,c_16552])).

tff(c_16565,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_16558])).

tff(c_16387,plain,(
    ! [A_2837,B_2838,C_2839] :
      ( k1_relset_1(A_2837,B_2838,C_2839) = k1_relat_1(C_2839)
      | ~ m1_subset_1(C_2839,k1_zfmisc_1(k2_zfmisc_1(A_2837,B_2838))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16411,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_14060,c_16387])).

tff(c_17076,plain,(
    ! [B_2884,C_2885,A_2886] :
      ( k1_xboole_0 = B_2884
      | v1_funct_2(C_2885,A_2886,B_2884)
      | k1_relset_1(A_2886,B_2884,C_2885) != A_2886
      | ~ m1_subset_1(C_2885,k1_zfmisc_1(k2_zfmisc_1(A_2886,B_2884))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_17088,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_14060,c_17076])).

tff(c_17109,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16411,c_17088])).

tff(c_17110,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_14059,c_17109])).

tff(c_17115,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_17110])).

tff(c_17118,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_17115])).

tff(c_17121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15928,c_90,c_84,c_16565,c_17118])).

tff(c_17122,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17110])).

tff(c_15986,plain,(
    ! [B_2783,A_2784] :
      ( k1_xboole_0 = B_2783
      | k1_xboole_0 = A_2784
      | k2_zfmisc_1(A_2784,B_2783) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_15989,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_15821,c_15986])).

tff(c_16000,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_15989])).

tff(c_17147,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17122,c_16000])).

tff(c_17159,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_3',B_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17122,c_17122,c_22])).

tff(c_17303,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17159,c_15821])).

tff(c_17305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17147,c_17303])).

tff(c_17307,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_15989])).

tff(c_17306,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15989])).

tff(c_17516,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17307,c_17307,c_17306])).

tff(c_17517,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_17516])).

tff(c_14070,plain,(
    ! [B_2607] : '#skF_2'(k1_xboole_0,B_2607) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_378])).

tff(c_14081,plain,(
    ! [B_2607] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_2607) ),
    inference(superposition,[status(thm),theory(equality)],[c_14070,c_62])).

tff(c_17312,plain,(
    ! [B_2607] : v1_funct_2('#skF_5','#skF_5',B_2607) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17307,c_17307,c_14081])).

tff(c_17931,plain,(
    ! [B_2607] : v1_funct_2('#skF_4','#skF_4',B_2607) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17517,c_17517,c_17312])).

tff(c_17325,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17307,c_8])).

tff(c_17528,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17517,c_17325])).

tff(c_17319,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_5',B_10) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17307,c_17307,c_22])).

tff(c_17522,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17517,c_17517,c_17319])).

tff(c_17449,plain,(
    ! [C_2899,B_2900,A_2901] :
      ( ~ v1_xboole_0(C_2899)
      | ~ m1_subset_1(B_2900,k1_zfmisc_1(C_2899))
      | ~ r2_hidden(A_2901,B_2900) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_17466,plain,(
    ! [A_2901] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3'))
      | ~ r2_hidden(A_2901,k2_funct_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_14060,c_17449])).

tff(c_17518,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_17466])).

tff(c_17654,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17522,c_17518])).

tff(c_17657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17528,c_17654])).

tff(c_17658,plain,(
    ! [A_2901] : ~ r2_hidden(A_2901,k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_17466])).

tff(c_17734,plain,(
    ! [A_2922] : ~ r2_hidden(A_2922,k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17517,c_17658])).

tff(c_17739,plain,(
    ! [B_2] : r1_tarski(k2_funct_1('#skF_4'),B_2) ),
    inference(resolution,[status(thm)],[c_6,c_17734])).

tff(c_17311,plain,(
    ! [A_8] :
      ( A_8 = '#skF_5'
      | ~ r1_tarski(A_8,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17307,c_17307,c_396])).

tff(c_17947,plain,(
    ! [A_2932] :
      ( A_2932 = '#skF_4'
      | ~ r1_tarski(A_2932,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17517,c_17517,c_17311])).

tff(c_17960,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_17739,c_17947])).

tff(c_17681,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17517,c_14059])).

tff(c_17966,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17960,c_17681])).

tff(c_17973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17931,c_17966])).

tff(c_17974,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17516])).

tff(c_17318,plain,(
    ! [A_83] : '#skF_2'(A_83,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17307,c_17307,c_387])).

tff(c_18237,plain,(
    ! [A_2950] : '#skF_2'(A_2950,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17974,c_17974,c_17318])).

tff(c_18248,plain,(
    ! [A_2950] : v1_funct_2('#skF_3',A_2950,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18237,c_62])).

tff(c_17320,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17307,c_17307,c_20])).

tff(c_17984,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17974,c_17974,c_17320])).

tff(c_18000,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17974,c_14060])).

tff(c_18413,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17984,c_18000])).

tff(c_18422,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_18413,c_24])).

tff(c_18384,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17974,c_17974,c_17311])).

tff(c_18434,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18422,c_18384])).

tff(c_18001,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17974,c_14059])).

tff(c_18441,plain,(
    ~ v1_funct_2('#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18434,c_18001])).

tff(c_18448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18248,c_18441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:18:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.02/3.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.53  
% 9.32/3.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.53  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 9.32/3.53  
% 9.32/3.53  %Foreground sorts:
% 9.32/3.53  
% 9.32/3.53  
% 9.32/3.53  %Background operators:
% 9.32/3.53  
% 9.32/3.53  
% 9.32/3.53  %Foreground operators:
% 9.32/3.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.32/3.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.32/3.53  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.32/3.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.32/3.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.32/3.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.32/3.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.32/3.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.32/3.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.32/3.53  tff('#skF_5', type, '#skF_5': $i).
% 9.32/3.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.32/3.53  tff('#skF_3', type, '#skF_3': $i).
% 9.32/3.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.32/3.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.32/3.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.32/3.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.32/3.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.32/3.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.32/3.53  tff('#skF_4', type, '#skF_4': $i).
% 9.32/3.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.32/3.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.32/3.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.32/3.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.32/3.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.32/3.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.32/3.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.32/3.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.32/3.53  
% 9.32/3.57  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 9.32/3.57  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.32/3.57  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.32/3.57  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.32/3.57  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.32/3.57  tff(f_58, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 9.32/3.57  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.32/3.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.32/3.57  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 9.32/3.57  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.32/3.57  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.32/3.57  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.32/3.57  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.32/3.57  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.32/3.57  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.32/3.57  tff(f_124, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 9.32/3.57  tff(c_86, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.32/3.57  tff(c_14152, plain, (![C_2614, A_2615, B_2616]: (v1_relat_1(C_2614) | ~m1_subset_1(C_2614, k1_zfmisc_1(k2_zfmisc_1(A_2615, B_2616))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.32/3.57  tff(c_14174, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_14152])).
% 9.32/3.57  tff(c_90, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.32/3.57  tff(c_84, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.32/3.57  tff(c_82, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.32/3.57  tff(c_14487, plain, (![A_2665, B_2666, C_2667]: (k2_relset_1(A_2665, B_2666, C_2667)=k2_relat_1(C_2667) | ~m1_subset_1(C_2667, k1_zfmisc_1(k2_zfmisc_1(A_2665, B_2666))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.32/3.57  tff(c_14500, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_14487])).
% 9.32/3.57  tff(c_14511, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_14500])).
% 9.32/3.57  tff(c_42, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.32/3.57  tff(c_32, plain, (![A_16]: (v1_funct_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.32/3.57  tff(c_80, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.32/3.57  tff(c_169, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_80])).
% 9.32/3.57  tff(c_172, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_169])).
% 9.32/3.57  tff(c_175, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_172])).
% 9.32/3.57  tff(c_344, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.32/3.57  tff(c_354, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_344])).
% 9.32/3.57  tff(c_365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_354])).
% 9.32/3.57  tff(c_366, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_80])).
% 9.32/3.57  tff(c_434, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_366])).
% 9.32/3.57  tff(c_621, plain, (![C_113, B_114, A_115]: (~v1_xboole_0(C_113) | ~m1_subset_1(B_114, k1_zfmisc_1(C_113)) | ~r2_hidden(A_115, B_114))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.32/3.57  tff(c_635, plain, (![A_115]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_115, '#skF_5'))), inference(resolution, [status(thm)], [c_86, c_621])).
% 9.32/3.57  tff(c_645, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_635])).
% 9.32/3.57  tff(c_88, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.32/3.57  tff(c_898, plain, (![A_154, B_155, C_156]: (k1_relset_1(A_154, B_155, C_156)=k1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.32/3.57  tff(c_917, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_898])).
% 9.32/3.57  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.32/3.57  tff(c_534, plain, (![C_98, A_99, B_100]: (v1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.32/3.57  tff(c_552, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_534])).
% 9.32/3.57  tff(c_1025, plain, (![A_170, B_171, C_172]: (k2_relset_1(A_170, B_171, C_172)=k2_relat_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.32/3.57  tff(c_1038, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_1025])).
% 9.32/3.57  tff(c_1049, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1038])).
% 9.32/3.57  tff(c_34, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.32/3.57  tff(c_367, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_80])).
% 9.32/3.57  tff(c_701, plain, (![A_127]: (k1_relat_1(k2_funct_1(A_127))=k2_relat_1(A_127) | ~v2_funct_1(A_127) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.32/3.57  tff(c_76, plain, (![A_34]: (v1_funct_2(A_34, k1_relat_1(A_34), k2_relat_1(A_34)) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.32/3.57  tff(c_2581, plain, (![A_304]: (v1_funct_2(k2_funct_1(A_304), k2_relat_1(A_304), k2_relat_1(k2_funct_1(A_304))) | ~v1_funct_1(k2_funct_1(A_304)) | ~v1_relat_1(k2_funct_1(A_304)) | ~v2_funct_1(A_304) | ~v1_funct_1(A_304) | ~v1_relat_1(A_304))), inference(superposition, [status(thm), theory('equality')], [c_701, c_76])).
% 9.32/3.57  tff(c_2587, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1049, c_2581])).
% 9.32/3.57  tff(c_2596, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_90, c_84, c_367, c_2587])).
% 9.32/3.57  tff(c_2597, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_2596])).
% 9.32/3.57  tff(c_2600, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_2597])).
% 9.32/3.57  tff(c_2604, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_552, c_90, c_2600])).
% 9.32/3.57  tff(c_2606, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_2596])).
% 9.32/3.57  tff(c_1262, plain, (![B_193, A_194, C_195]: (k1_xboole_0=B_193 | k1_relset_1(A_194, B_193, C_195)=A_194 | ~v1_funct_2(C_195, A_194, B_193) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.32/3.57  tff(c_1278, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_1262])).
% 9.32/3.57  tff(c_1295, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_917, c_1278])).
% 9.32/3.57  tff(c_1297, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1295])).
% 9.32/3.57  tff(c_40, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.32/3.57  tff(c_970, plain, (![A_163]: (m1_subset_1(A_163, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_163), k2_relat_1(A_163)))) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.32/3.57  tff(c_3042, plain, (![A_331]: (m1_subset_1(k2_funct_1(A_331), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_331)), k1_relat_1(A_331)))) | ~v1_funct_1(k2_funct_1(A_331)) | ~v1_relat_1(k2_funct_1(A_331)) | ~v2_funct_1(A_331) | ~v1_funct_1(A_331) | ~v1_relat_1(A_331))), inference(superposition, [status(thm), theory('equality')], [c_40, c_970])).
% 9.32/3.57  tff(c_3068, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1297, c_3042])).
% 9.32/3.57  tff(c_3088, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_90, c_84, c_2606, c_367, c_3068])).
% 9.32/3.57  tff(c_3113, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_42, c_3088])).
% 9.32/3.57  tff(c_3126, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_90, c_84, c_1049, c_3113])).
% 9.32/3.57  tff(c_3128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_3126])).
% 9.32/3.57  tff(c_3129, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1295])).
% 9.32/3.57  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.32/3.57  tff(c_3171, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3129, c_8])).
% 9.32/3.57  tff(c_20, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.32/3.57  tff(c_3166, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3129, c_3129, c_20])).
% 9.32/3.57  tff(c_74, plain, (![A_34]: (m1_subset_1(A_34, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_34), k2_relat_1(A_34)))) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.32/3.57  tff(c_1053, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1049, c_74])).
% 9.32/3.57  tff(c_1060, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_90, c_1053])).
% 9.32/3.57  tff(c_28, plain, (![C_15, B_14, A_13]: (~v1_xboole_0(C_15) | ~m1_subset_1(B_14, k1_zfmisc_1(C_15)) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.32/3.57  tff(c_1081, plain, (![A_13]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')) | ~r2_hidden(A_13, '#skF_5'))), inference(resolution, [status(thm)], [c_1060, c_28])).
% 9.32/3.57  tff(c_1117, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_1081])).
% 9.32/3.57  tff(c_3272, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3166, c_1117])).
% 9.32/3.57  tff(c_3281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3171, c_3272])).
% 9.32/3.57  tff(c_3284, plain, (![A_339]: (~r2_hidden(A_339, '#skF_5'))), inference(splitRight, [status(thm)], [c_1081])).
% 9.32/3.57  tff(c_3297, plain, (![B_340]: (r1_tarski('#skF_5', B_340))), inference(resolution, [status(thm)], [c_6, c_3284])).
% 9.32/3.57  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.32/3.57  tff(c_374, plain, (![B_85, A_86]: (B_85=A_86 | ~r1_tarski(B_85, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.32/3.57  tff(c_396, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_374])).
% 9.32/3.57  tff(c_3333, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3297, c_396])).
% 9.32/3.57  tff(c_60, plain, (![B_29, A_28, C_30]: (k1_xboole_0=B_29 | k1_relset_1(A_28, B_29, C_30)=A_28 | ~v1_funct_2(C_30, A_28, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.32/3.57  tff(c_3503, plain, (![B_349, A_350, C_351]: (B_349='#skF_5' | k1_relset_1(A_350, B_349, C_351)=A_350 | ~v1_funct_2(C_351, A_350, B_349) | ~m1_subset_1(C_351, k1_zfmisc_1(k2_zfmisc_1(A_350, B_349))))), inference(demodulation, [status(thm), theory('equality')], [c_3333, c_60])).
% 9.32/3.57  tff(c_3525, plain, ('#skF_5'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_3503])).
% 9.32/3.57  tff(c_3537, plain, ('#skF_5'='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_917, c_3525])).
% 9.32/3.57  tff(c_3649, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_3537])).
% 9.32/3.57  tff(c_3283, plain, (v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(splitRight, [status(thm)], [c_1081])).
% 9.32/3.57  tff(c_3650, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3649, c_3283])).
% 9.32/3.57  tff(c_3657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_645, c_3650])).
% 9.32/3.57  tff(c_3658, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_3537])).
% 9.32/3.57  tff(c_3364, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3333, c_8])).
% 9.32/3.57  tff(c_3673, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3658, c_3364])).
% 9.32/3.57  tff(c_3359, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3333, c_3333, c_20])).
% 9.32/3.57  tff(c_3666, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3658, c_3658, c_3359])).
% 9.32/3.57  tff(c_4000, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3666, c_645])).
% 9.32/3.57  tff(c_4004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3673, c_4000])).
% 9.32/3.57  tff(c_4006, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_635])).
% 9.32/3.57  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.32/3.57  tff(c_26, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.32/3.57  tff(c_4353, plain, (![B_391, A_392, A_393]: (~v1_xboole_0(B_391) | ~r2_hidden(A_392, A_393) | ~r1_tarski(A_393, B_391))), inference(resolution, [status(thm)], [c_26, c_621])).
% 9.32/3.57  tff(c_4357, plain, (![B_394, A_395, B_396]: (~v1_xboole_0(B_394) | ~r1_tarski(A_395, B_394) | r1_tarski(A_395, B_396))), inference(resolution, [status(thm)], [c_6, c_4353])).
% 9.32/3.57  tff(c_4396, plain, (![B_400, B_401]: (~v1_xboole_0(B_400) | r1_tarski(B_400, B_401))), inference(resolution, [status(thm)], [c_14, c_4357])).
% 9.32/3.57  tff(c_141, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.32/3.57  tff(c_149, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_141])).
% 9.32/3.57  tff(c_391, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_149, c_374])).
% 9.32/3.57  tff(c_502, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_391])).
% 9.32/3.57  tff(c_4416, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4396, c_502])).
% 9.32/3.57  tff(c_4427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4006, c_4416])).
% 9.32/3.57  tff(c_4428, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_391])).
% 9.32/3.57  tff(c_4431, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4428, c_86])).
% 9.32/3.57  tff(c_4477, plain, (![C_404, A_405, B_406]: (v1_relat_1(C_404) | ~m1_subset_1(C_404, k1_zfmisc_1(k2_zfmisc_1(A_405, B_406))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.32/3.57  tff(c_4525, plain, (![C_411]: (v1_relat_1(C_411) | ~m1_subset_1(C_411, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4428, c_4477])).
% 9.32/3.57  tff(c_4538, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4431, c_4525])).
% 9.32/3.57  tff(c_8017, plain, (![B_708, C_709, A_710]: (k1_xboole_0=B_708 | v1_funct_2(C_709, A_710, B_708) | k1_relset_1(A_710, B_708, C_709)!=A_710 | ~m1_subset_1(C_709, k1_zfmisc_1(k2_zfmisc_1(A_710, B_708))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.32/3.57  tff(c_8026, plain, (![C_709]: (k1_xboole_0='#skF_4' | v1_funct_2(C_709, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', C_709)!='#skF_3' | ~m1_subset_1(C_709, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4428, c_8017])).
% 9.32/3.57  tff(c_8081, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_8026])).
% 9.32/3.57  tff(c_4591, plain, (![B_418, A_419]: (k1_xboole_0=B_418 | k1_xboole_0=A_419 | k2_zfmisc_1(A_419, B_418)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.32/3.57  tff(c_4594, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_4428, c_4591])).
% 9.32/3.57  tff(c_4609, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_4594])).
% 9.32/3.57  tff(c_8106, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8081, c_4609])).
% 9.32/3.57  tff(c_152, plain, (![A_59, B_60]: (m1_subset_1('#skF_2'(A_59, B_60), k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.32/3.57  tff(c_368, plain, (![A_83]: (m1_subset_1('#skF_2'(A_83, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_152])).
% 9.32/3.57  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.32/3.57  tff(c_372, plain, (![A_83]: (r1_tarski('#skF_2'(A_83, k1_xboole_0), k1_xboole_0))), inference(resolution, [status(thm)], [c_368, c_24])).
% 9.32/3.57  tff(c_376, plain, (![A_83]: ('#skF_2'(A_83, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_2'(A_83, k1_xboole_0)))), inference(resolution, [status(thm)], [c_372, c_374])).
% 9.32/3.57  tff(c_387, plain, (![A_83]: ('#skF_2'(A_83, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_376])).
% 9.32/3.57  tff(c_8117, plain, (![A_83]: ('#skF_2'(A_83, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8081, c_8081, c_387])).
% 9.32/3.57  tff(c_4848, plain, (![A_457, B_458, C_459]: (k2_relset_1(A_457, B_458, C_459)=k2_relat_1(C_459) | ~m1_subset_1(C_459, k1_zfmisc_1(k2_zfmisc_1(A_457, B_458))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.32/3.57  tff(c_4906, plain, (![C_464]: (k2_relset_1('#skF_3', '#skF_4', C_464)=k2_relat_1(C_464) | ~m1_subset_1(C_464, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4428, c_4848])).
% 9.32/3.57  tff(c_4912, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4431, c_4906])).
% 9.32/3.57  tff(c_4920, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4912])).
% 9.32/3.57  tff(c_5065, plain, (![A_474, B_475, C_476]: (k1_relset_1(A_474, B_475, C_476)=k1_relat_1(C_476) | ~m1_subset_1(C_476, k1_zfmisc_1(k2_zfmisc_1(A_474, B_475))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.32/3.57  tff(c_5124, plain, (![C_481]: (k1_relset_1('#skF_3', '#skF_4', C_481)=k1_relat_1(C_481) | ~m1_subset_1(C_481, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4428, c_5065])).
% 9.32/3.57  tff(c_5136, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4431, c_5124])).
% 9.32/3.57  tff(c_5597, plain, (![B_531, C_532, A_533]: (k1_xboole_0=B_531 | v1_funct_2(C_532, A_533, B_531) | k1_relset_1(A_533, B_531, C_532)!=A_533 | ~m1_subset_1(C_532, k1_zfmisc_1(k2_zfmisc_1(A_533, B_531))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.32/3.57  tff(c_5606, plain, (![C_532]: (k1_xboole_0='#skF_4' | v1_funct_2(C_532, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', C_532)!='#skF_3' | ~m1_subset_1(C_532, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4428, c_5597])).
% 9.32/3.57  tff(c_5664, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5606])).
% 9.32/3.57  tff(c_5702, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5664, c_8])).
% 9.32/3.57  tff(c_5697, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5664, c_5664, c_20])).
% 9.32/3.57  tff(c_4968, plain, (![A_467]: (m1_subset_1(A_467, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_467), k2_relat_1(A_467)))) | ~v1_funct_1(A_467) | ~v1_relat_1(A_467))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.32/3.57  tff(c_4982, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4920, c_4968])).
% 9.32/3.57  tff(c_4994, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4538, c_90, c_4982])).
% 9.32/3.57  tff(c_5008, plain, (![A_13]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')) | ~r2_hidden(A_13, '#skF_5'))), inference(resolution, [status(thm)], [c_4994, c_28])).
% 9.32/3.57  tff(c_5031, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_5008])).
% 9.32/3.57  tff(c_5843, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5697, c_5031])).
% 9.32/3.57  tff(c_5849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5702, c_5843])).
% 9.32/3.57  tff(c_5851, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_5606])).
% 9.32/3.57  tff(c_5852, plain, (![B_548, A_549, C_550]: (k1_xboole_0=B_548 | k1_relset_1(A_549, B_548, C_550)=A_549 | ~v1_funct_2(C_550, A_549, B_548) | ~m1_subset_1(C_550, k1_zfmisc_1(k2_zfmisc_1(A_549, B_548))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.32/3.57  tff(c_5861, plain, (![C_550]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_550)='#skF_3' | ~v1_funct_2(C_550, '#skF_3', '#skF_4') | ~m1_subset_1(C_550, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4428, c_5852])).
% 9.32/3.57  tff(c_5971, plain, (![C_559]: (k1_relset_1('#skF_3', '#skF_4', C_559)='#skF_3' | ~v1_funct_2(C_559, '#skF_3', '#skF_4') | ~m1_subset_1(C_559, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_5851, c_5861])).
% 9.32/3.57  tff(c_5977, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_4431, c_5971])).
% 9.32/3.57  tff(c_5987, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5136, c_5977])).
% 9.32/3.57  tff(c_4836, plain, (![A_456]: (k2_relat_1(k2_funct_1(A_456))=k1_relat_1(A_456) | ~v2_funct_1(A_456) | ~v1_funct_1(A_456) | ~v1_relat_1(A_456))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.32/3.57  tff(c_6962, plain, (![A_615]: (v1_funct_2(k2_funct_1(A_615), k1_relat_1(k2_funct_1(A_615)), k1_relat_1(A_615)) | ~v1_funct_1(k2_funct_1(A_615)) | ~v1_relat_1(k2_funct_1(A_615)) | ~v2_funct_1(A_615) | ~v1_funct_1(A_615) | ~v1_relat_1(A_615))), inference(superposition, [status(thm), theory('equality')], [c_4836, c_76])).
% 9.32/3.57  tff(c_6971, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5987, c_6962])).
% 9.32/3.57  tff(c_6988, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4538, c_90, c_84, c_367, c_6971])).
% 9.32/3.57  tff(c_6993, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_6988])).
% 9.32/3.57  tff(c_6996, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_6993])).
% 9.32/3.57  tff(c_7000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4538, c_90, c_6996])).
% 9.32/3.57  tff(c_7002, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_6988])).
% 9.32/3.57  tff(c_7262, plain, (![A_645]: (m1_subset_1(k2_funct_1(A_645), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_645)), k1_relat_1(A_645)))) | ~v1_funct_1(k2_funct_1(A_645)) | ~v1_relat_1(k2_funct_1(A_645)) | ~v2_funct_1(A_645) | ~v1_funct_1(A_645) | ~v1_relat_1(A_645))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4968])).
% 9.32/3.57  tff(c_7288, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5987, c_7262])).
% 9.32/3.57  tff(c_7311, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4538, c_90, c_84, c_7002, c_367, c_7288])).
% 9.32/3.57  tff(c_7338, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_42, c_7311])).
% 9.32/3.57  tff(c_7351, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4538, c_90, c_84, c_4920, c_7338])).
% 9.32/3.57  tff(c_7353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_7351])).
% 9.32/3.57  tff(c_7356, plain, (![A_646]: (~r2_hidden(A_646, '#skF_5'))), inference(splitRight, [status(thm)], [c_5008])).
% 9.32/3.57  tff(c_7361, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_7356])).
% 9.32/3.57  tff(c_72, plain, (![A_31, B_32]: (m1_subset_1('#skF_2'(A_31, B_32), k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.32/3.57  tff(c_4436, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4428, c_72])).
% 9.32/3.57  tff(c_4449, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_4436, c_24])).
% 9.32/3.57  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.32/3.57  tff(c_4452, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski('#skF_5', '#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4449, c_10])).
% 9.32/3.57  tff(c_4800, plain, (~r1_tarski('#skF_5', '#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_4452])).
% 9.32/3.57  tff(c_7365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7361, c_4800])).
% 9.32/3.57  tff(c_7366, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_4452])).
% 9.32/3.57  tff(c_8307, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8117, c_7366])).
% 9.32/3.57  tff(c_8309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8106, c_8307])).
% 9.32/3.57  tff(c_8311, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_8026])).
% 9.32/3.57  tff(c_62, plain, (![A_31, B_32]: (v1_funct_2('#skF_2'(A_31, B_32), A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.32/3.57  tff(c_7614, plain, (![A_670, B_671, C_672]: (k1_relset_1(A_670, B_671, C_672)=k1_relat_1(C_672) | ~m1_subset_1(C_672, k1_zfmisc_1(k2_zfmisc_1(A_670, B_671))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.32/3.57  tff(c_7635, plain, (![A_31, B_32]: (k1_relset_1(A_31, B_32, '#skF_2'(A_31, B_32))=k1_relat_1('#skF_2'(A_31, B_32)))), inference(resolution, [status(thm)], [c_72, c_7614])).
% 9.32/3.57  tff(c_8312, plain, (![B_725, A_726, C_727]: (k1_xboole_0=B_725 | k1_relset_1(A_726, B_725, C_727)=A_726 | ~v1_funct_2(C_727, A_726, B_725) | ~m1_subset_1(C_727, k1_zfmisc_1(k2_zfmisc_1(A_726, B_725))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.32/3.57  tff(c_8324, plain, (![B_32, A_31]: (k1_xboole_0=B_32 | k1_relset_1(A_31, B_32, '#skF_2'(A_31, B_32))=A_31 | ~v1_funct_2('#skF_2'(A_31, B_32), A_31, B_32))), inference(resolution, [status(thm)], [c_72, c_8312])).
% 9.32/3.57  tff(c_8346, plain, (![B_728, A_729]: (k1_xboole_0=B_728 | k1_relat_1('#skF_2'(A_729, B_728))=A_729)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_7635, c_8324])).
% 9.32/3.57  tff(c_8364, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7366, c_8346])).
% 9.32/3.57  tff(c_8379, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_8311, c_8364])).
% 9.32/3.57  tff(c_7551, plain, (![A_665, B_666, C_667]: (k2_relset_1(A_665, B_666, C_667)=k2_relat_1(C_667) | ~m1_subset_1(C_667, k1_zfmisc_1(k2_zfmisc_1(A_665, B_666))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.32/3.57  tff(c_7574, plain, (![A_668, B_669]: (k2_relset_1(A_668, B_669, '#skF_2'(A_668, B_669))=k2_relat_1('#skF_2'(A_668, B_669)))), inference(resolution, [status(thm)], [c_72, c_7551])).
% 9.32/3.57  tff(c_7583, plain, (k2_relat_1('#skF_2'('#skF_3', '#skF_4'))=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7366, c_7574])).
% 9.32/3.57  tff(c_7592, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7366, c_82, c_7583])).
% 9.32/3.57  tff(c_7428, plain, (![A_652]: (k1_relat_1(k2_funct_1(A_652))=k2_relat_1(A_652) | ~v2_funct_1(A_652) | ~v1_funct_1(A_652) | ~v1_relat_1(A_652))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.32/3.57  tff(c_9529, plain, (![A_830]: (v1_funct_2(k2_funct_1(A_830), k2_relat_1(A_830), k2_relat_1(k2_funct_1(A_830))) | ~v1_funct_1(k2_funct_1(A_830)) | ~v1_relat_1(k2_funct_1(A_830)) | ~v2_funct_1(A_830) | ~v1_funct_1(A_830) | ~v1_relat_1(A_830))), inference(superposition, [status(thm), theory('equality')], [c_7428, c_76])).
% 9.32/3.57  tff(c_9535, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7592, c_9529])).
% 9.32/3.57  tff(c_9544, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4538, c_90, c_84, c_367, c_9535])).
% 9.32/3.57  tff(c_9545, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_9544])).
% 9.32/3.57  tff(c_9548, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_9545])).
% 9.32/3.57  tff(c_9552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4538, c_90, c_9548])).
% 9.32/3.57  tff(c_9554, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_9544])).
% 9.32/3.57  tff(c_7493, plain, (![A_659]: (m1_subset_1(A_659, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_659), k2_relat_1(A_659)))) | ~v1_funct_1(A_659) | ~v1_relat_1(A_659))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.32/3.57  tff(c_10037, plain, (![A_872]: (m1_subset_1(k2_funct_1(A_872), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_872), k2_relat_1(k2_funct_1(A_872))))) | ~v1_funct_1(k2_funct_1(A_872)) | ~v1_relat_1(k2_funct_1(A_872)) | ~v2_funct_1(A_872) | ~v1_funct_1(A_872) | ~v1_relat_1(A_872))), inference(superposition, [status(thm), theory('equality')], [c_42, c_7493])).
% 9.32/3.57  tff(c_10060, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7592, c_10037])).
% 9.32/3.57  tff(c_10075, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_4538, c_90, c_84, c_9554, c_367, c_10060])).
% 9.32/3.57  tff(c_10098, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_10075])).
% 9.32/3.57  tff(c_10111, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4538, c_90, c_84, c_8379, c_10098])).
% 9.32/3.57  tff(c_10113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_10111])).
% 9.32/3.57  tff(c_10115, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_4594])).
% 9.32/3.57  tff(c_10114, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4594])).
% 9.32/3.57  tff(c_10141, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10115, c_10115, c_10114])).
% 9.32/3.57  tff(c_10142, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_10141])).
% 9.32/3.57  tff(c_22, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.32/3.57  tff(c_10127, plain, (![B_10]: (k2_zfmisc_1('#skF_5', B_10)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10115, c_10115, c_22])).
% 9.32/3.57  tff(c_10232, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10142, c_10142, c_10127])).
% 9.32/3.57  tff(c_10153, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_10142, c_434])).
% 9.32/3.57  tff(c_10437, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10232, c_10153])).
% 9.32/3.57  tff(c_10146, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10142, c_4538])).
% 9.32/3.57  tff(c_10158, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10142, c_90])).
% 9.32/3.57  tff(c_10157, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10142, c_84])).
% 9.32/3.57  tff(c_10154, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10142, c_367])).
% 9.32/3.57  tff(c_10126, plain, (![A_83]: ('#skF_2'(A_83, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10115, c_10115, c_387])).
% 9.32/3.57  tff(c_10200, plain, (![A_83]: ('#skF_2'(A_83, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10142, c_10142, c_10126])).
% 9.32/3.57  tff(c_10694, plain, (![A_920, B_921, C_922]: (k2_relset_1(A_920, B_921, C_922)=k2_relat_1(C_922) | ~m1_subset_1(C_922, k1_zfmisc_1(k2_zfmisc_1(A_920, B_921))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.32/3.57  tff(c_10787, plain, (![A_932, B_933]: (k2_relset_1(A_932, B_933, '#skF_2'(A_932, B_933))=k2_relat_1('#skF_2'(A_932, B_933)))), inference(resolution, [status(thm)], [c_72, c_10694])).
% 9.32/3.57  tff(c_10799, plain, (![A_83]: (k2_relat_1('#skF_2'(A_83, '#skF_4'))=k2_relset_1(A_83, '#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10200, c_10787])).
% 9.32/3.57  tff(c_10811, plain, (![A_935]: (k2_relset_1(A_935, '#skF_4', '#skF_4')=k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10200, c_10799])).
% 9.32/3.57  tff(c_10155, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10142, c_82])).
% 9.32/3.57  tff(c_10818, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_10811, c_10155])).
% 9.32/3.57  tff(c_10499, plain, (![A_893]: (k1_relat_1(k2_funct_1(A_893))=k2_relat_1(A_893) | ~v2_funct_1(A_893) | ~v1_funct_1(A_893) | ~v1_relat_1(A_893))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.32/3.57  tff(c_11778, plain, (![A_1049]: (v1_funct_2(k2_funct_1(A_1049), k2_relat_1(A_1049), k2_relat_1(k2_funct_1(A_1049))) | ~v1_funct_1(k2_funct_1(A_1049)) | ~v1_relat_1(k2_funct_1(A_1049)) | ~v2_funct_1(A_1049) | ~v1_funct_1(A_1049) | ~v1_relat_1(A_1049))), inference(superposition, [status(thm), theory('equality')], [c_10499, c_76])).
% 9.32/3.57  tff(c_11781, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10818, c_11778])).
% 9.32/3.57  tff(c_11789, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10146, c_10158, c_10157, c_10154, c_11781])).
% 9.32/3.57  tff(c_11790, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_11789])).
% 9.32/3.57  tff(c_11793, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_11790])).
% 9.32/3.57  tff(c_11797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10146, c_10158, c_11793])).
% 9.32/3.57  tff(c_11799, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_11789])).
% 9.32/3.57  tff(c_10584, plain, (![A_907]: (m1_subset_1(A_907, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_907), k2_relat_1(A_907)))) | ~v1_funct_1(A_907) | ~v1_relat_1(A_907))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.32/3.57  tff(c_11984, plain, (![A_1070]: (m1_subset_1(k2_funct_1(A_1070), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1070), k2_relat_1(k2_funct_1(A_1070))))) | ~v1_funct_1(k2_funct_1(A_1070)) | ~v1_relat_1(k2_funct_1(A_1070)) | ~v2_funct_1(A_1070) | ~v1_funct_1(A_1070) | ~v1_relat_1(A_1070))), inference(superposition, [status(thm), theory('equality')], [c_42, c_10584])).
% 9.32/3.57  tff(c_12007, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10818, c_11984])).
% 9.32/3.57  tff(c_12022, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10146, c_10158, c_10157, c_11799, c_10154, c_10232, c_12007])).
% 9.32/3.57  tff(c_12024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10437, c_12022])).
% 9.32/3.57  tff(c_12025, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_10141])).
% 9.32/3.57  tff(c_12026, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_10141])).
% 9.32/3.57  tff(c_12047, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12025, c_12026])).
% 9.32/3.57  tff(c_10128, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10115, c_10115, c_20])).
% 9.32/3.57  tff(c_12106, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12025, c_12025, c_10128])).
% 9.32/3.57  tff(c_12037, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12025, c_434])).
% 9.32/3.57  tff(c_12269, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12106, c_12037])).
% 9.32/3.57  tff(c_12030, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12025, c_4538])).
% 9.32/3.57  tff(c_12042, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12025, c_90])).
% 9.32/3.57  tff(c_12041, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12025, c_84])).
% 9.32/3.57  tff(c_163, plain, (![B_61]: (m1_subset_1('#skF_2'(k1_xboole_0, B_61), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_152])).
% 9.32/3.57  tff(c_167, plain, (![B_61]: (r1_tarski('#skF_2'(k1_xboole_0, B_61), k1_xboole_0))), inference(resolution, [status(thm)], [c_163, c_24])).
% 9.32/3.57  tff(c_378, plain, (![B_61]: ('#skF_2'(k1_xboole_0, B_61)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_2'(k1_xboole_0, B_61)))), inference(resolution, [status(thm)], [c_167, c_374])).
% 9.32/3.57  tff(c_390, plain, (![B_61]: ('#skF_2'(k1_xboole_0, B_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_378])).
% 9.32/3.57  tff(c_10123, plain, (![B_61]: ('#skF_2'('#skF_5', B_61)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10115, c_10115, c_390])).
% 9.32/3.57  tff(c_12136, plain, (![B_61]: ('#skF_2'('#skF_3', B_61)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12025, c_12025, c_10123])).
% 9.32/3.57  tff(c_12662, plain, (![A_1130, B_1131, C_1132]: (k1_relset_1(A_1130, B_1131, C_1132)=k1_relat_1(C_1132) | ~m1_subset_1(C_1132, k1_zfmisc_1(k2_zfmisc_1(A_1130, B_1131))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.32/3.57  tff(c_12684, plain, (![A_31, B_32]: (k1_relset_1(A_31, B_32, '#skF_2'(A_31, B_32))=k1_relat_1('#skF_2'(A_31, B_32)))), inference(resolution, [status(thm)], [c_72, c_12662])).
% 9.32/3.57  tff(c_12028, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12025, c_10115])).
% 9.32/3.57  tff(c_12841, plain, (![B_1156, A_1157, C_1158]: (B_1156='#skF_3' | k1_relset_1(A_1157, B_1156, C_1158)=A_1157 | ~v1_funct_2(C_1158, A_1157, B_1156) | ~m1_subset_1(C_1158, k1_zfmisc_1(k2_zfmisc_1(A_1157, B_1156))))), inference(demodulation, [status(thm), theory('equality')], [c_12028, c_60])).
% 9.32/3.57  tff(c_12856, plain, (![B_32, A_31]: (B_32='#skF_3' | k1_relset_1(A_31, B_32, '#skF_2'(A_31, B_32))=A_31 | ~v1_funct_2('#skF_2'(A_31, B_32), A_31, B_32))), inference(resolution, [status(thm)], [c_72, c_12841])).
% 9.32/3.57  tff(c_12873, plain, (![B_1159, A_1160]: (B_1159='#skF_3' | k1_relat_1('#skF_2'(A_1160, B_1159))=A_1160)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12684, c_12856])).
% 9.32/3.57  tff(c_12891, plain, (![B_61]: (B_61='#skF_3' | k1_relat_1('#skF_3')='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12136, c_12873])).
% 9.32/3.57  tff(c_12899, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_12891])).
% 9.32/3.57  tff(c_12038, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12025, c_367])).
% 9.32/3.57  tff(c_12480, plain, (![A_1114, B_1115, C_1116]: (k2_relset_1(A_1114, B_1115, C_1116)=k2_relat_1(C_1116) | ~m1_subset_1(C_1116, k1_zfmisc_1(k2_zfmisc_1(A_1114, B_1115))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.32/3.57  tff(c_12507, plain, (![A_1119, B_1120]: (k2_relset_1(A_1119, B_1120, '#skF_2'(A_1119, B_1120))=k2_relat_1('#skF_2'(A_1119, B_1120)))), inference(resolution, [status(thm)], [c_72, c_12480])).
% 9.32/3.57  tff(c_12519, plain, (![B_61]: (k2_relat_1('#skF_2'('#skF_3', B_61))=k2_relset_1('#skF_3', B_61, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12136, c_12507])).
% 9.32/3.57  tff(c_12531, plain, (![B_1122]: (k2_relset_1('#skF_3', B_1122, '#skF_3')=k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12136, c_12519])).
% 9.32/3.57  tff(c_12039, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12025, c_82])).
% 9.32/3.57  tff(c_12538, plain, (k2_relat_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_12531, c_12039])).
% 9.32/3.57  tff(c_12276, plain, (![A_1087]: (k1_relat_1(k2_funct_1(A_1087))=k2_relat_1(A_1087) | ~v2_funct_1(A_1087) | ~v1_funct_1(A_1087) | ~v1_relat_1(A_1087))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.32/3.57  tff(c_13480, plain, (![A_1222]: (v1_funct_2(k2_funct_1(A_1222), k2_relat_1(A_1222), k2_relat_1(k2_funct_1(A_1222))) | ~v1_funct_1(k2_funct_1(A_1222)) | ~v1_relat_1(k2_funct_1(A_1222)) | ~v2_funct_1(A_1222) | ~v1_funct_1(A_1222) | ~v1_relat_1(A_1222))), inference(superposition, [status(thm), theory('equality')], [c_12276, c_76])).
% 9.32/3.57  tff(c_13483, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12538, c_13480])).
% 9.32/3.57  tff(c_13491, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12030, c_12042, c_12041, c_12038, c_13483])).
% 9.32/3.57  tff(c_13492, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_13491])).
% 9.32/3.57  tff(c_13495, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_13492])).
% 9.32/3.57  tff(c_13499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12030, c_12042, c_13495])).
% 9.32/3.57  tff(c_13501, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_13491])).
% 9.32/3.57  tff(c_12550, plain, (![A_1123]: (m1_subset_1(A_1123, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1123), k2_relat_1(A_1123)))) | ~v1_funct_1(A_1123) | ~v1_relat_1(A_1123))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.32/3.57  tff(c_13713, plain, (![A_1253]: (m1_subset_1(k2_funct_1(A_1253), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1253), k2_relat_1(k2_funct_1(A_1253))))) | ~v1_funct_1(k2_funct_1(A_1253)) | ~v1_relat_1(k2_funct_1(A_1253)) | ~v2_funct_1(A_1253) | ~v1_funct_1(A_1253) | ~v1_relat_1(A_1253))), inference(superposition, [status(thm), theory('equality')], [c_42, c_12550])).
% 9.32/3.57  tff(c_13736, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12538, c_13713])).
% 9.32/3.57  tff(c_13751, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_12030, c_12042, c_12041, c_13501, c_12038, c_13736])).
% 9.32/3.57  tff(c_13774, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_13751])).
% 9.32/3.57  tff(c_13787, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12030, c_12042, c_12041, c_12106, c_12899, c_13774])).
% 9.32/3.57  tff(c_13789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12269, c_13787])).
% 9.32/3.57  tff(c_13792, plain, (![B_1254]: (B_1254='#skF_3')), inference(splitRight, [status(thm)], [c_12891])).
% 9.32/3.57  tff(c_12577, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_4'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12538, c_74])).
% 9.32/3.57  tff(c_12584, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_12030, c_12042, c_12577])).
% 9.32/3.57  tff(c_48, plain, (![A_25, B_26, C_27]: (k2_relset_1(A_25, B_26, C_27)=k2_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.32/3.57  tff(c_12614, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_4', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12584, c_48])).
% 9.32/3.57  tff(c_12624, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12538, c_12614])).
% 9.32/3.57  tff(c_13867, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_13792, c_12624])).
% 9.32/3.57  tff(c_14058, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12047, c_13867])).
% 9.32/3.57  tff(c_14059, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_366])).
% 9.32/3.57  tff(c_14060, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_366])).
% 9.32/3.57  tff(c_14645, plain, (![A_2678, B_2679, C_2680]: (k1_relset_1(A_2678, B_2679, C_2680)=k1_relat_1(C_2680) | ~m1_subset_1(C_2680, k1_zfmisc_1(k2_zfmisc_1(A_2678, B_2679))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.32/3.57  tff(c_14673, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_14060, c_14645])).
% 9.32/3.57  tff(c_15199, plain, (![B_2733, C_2734, A_2735]: (k1_xboole_0=B_2733 | v1_funct_2(C_2734, A_2735, B_2733) | k1_relset_1(A_2735, B_2733, C_2734)!=A_2735 | ~m1_subset_1(C_2734, k1_zfmisc_1(k2_zfmisc_1(A_2735, B_2733))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.32/3.57  tff(c_15205, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_14060, c_15199])).
% 9.32/3.57  tff(c_15224, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14673, c_15205])).
% 9.32/3.57  tff(c_15225, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_14059, c_15224])).
% 9.32/3.57  tff(c_15248, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_15225])).
% 9.32/3.57  tff(c_15251, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_42, c_15248])).
% 9.32/3.57  tff(c_15254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14174, c_90, c_84, c_14511, c_15251])).
% 9.32/3.57  tff(c_15255, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_15225])).
% 9.32/3.57  tff(c_15297, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15255, c_8])).
% 9.32/3.57  tff(c_15291, plain, (![B_10]: (k2_zfmisc_1('#skF_3', B_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15255, c_15255, c_22])).
% 9.32/3.57  tff(c_14256, plain, (![C_2628, B_2629, A_2630]: (~v1_xboole_0(C_2628) | ~m1_subset_1(B_2629, k1_zfmisc_1(C_2628)) | ~r2_hidden(A_2630, B_2629))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.32/3.57  tff(c_14273, plain, (![A_2630]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_2630, '#skF_5'))), inference(resolution, [status(thm)], [c_86, c_14256])).
% 9.32/3.57  tff(c_14285, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_14273])).
% 9.32/3.57  tff(c_15421, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15291, c_14285])).
% 9.32/3.57  tff(c_15427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15297, c_15421])).
% 9.32/3.57  tff(c_15429, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_14273])).
% 9.32/3.57  tff(c_15771, plain, (![B_2761, A_2762, A_2763]: (~v1_xboole_0(B_2761) | ~r2_hidden(A_2762, A_2763) | ~r1_tarski(A_2763, B_2761))), inference(resolution, [status(thm)], [c_26, c_14256])).
% 9.32/3.57  tff(c_15775, plain, (![B_2764, A_2765, B_2766]: (~v1_xboole_0(B_2764) | ~r1_tarski(A_2765, B_2764) | r1_tarski(A_2765, B_2766))), inference(resolution, [status(thm)], [c_6, c_15771])).
% 9.32/3.57  tff(c_15789, plain, (![B_2767, B_2768]: (~v1_xboole_0(B_2767) | r1_tarski(B_2767, B_2768))), inference(resolution, [status(thm)], [c_14, c_15775])).
% 9.32/3.57  tff(c_14131, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_391])).
% 9.32/3.57  tff(c_15809, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_15789, c_14131])).
% 9.32/3.57  tff(c_15820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15429, c_15809])).
% 9.32/3.57  tff(c_15821, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_391])).
% 9.32/3.57  tff(c_15824, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_15821, c_86])).
% 9.32/3.57  tff(c_15870, plain, (![C_2771, A_2772, B_2773]: (v1_relat_1(C_2771) | ~m1_subset_1(C_2771, k1_zfmisc_1(k2_zfmisc_1(A_2772, B_2773))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.32/3.57  tff(c_15915, plain, (![C_2776]: (v1_relat_1(C_2776) | ~m1_subset_1(C_2776, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_15821, c_15870])).
% 9.32/3.57  tff(c_15928, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_15824, c_15915])).
% 9.32/3.57  tff(c_16507, plain, (![A_2846, B_2847, C_2848]: (k2_relset_1(A_2846, B_2847, C_2848)=k2_relat_1(C_2848) | ~m1_subset_1(C_2848, k1_zfmisc_1(k2_zfmisc_1(A_2846, B_2847))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.32/3.57  tff(c_16552, plain, (![C_2852]: (k2_relset_1('#skF_3', '#skF_4', C_2852)=k2_relat_1(C_2852) | ~m1_subset_1(C_2852, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_15821, c_16507])).
% 9.32/3.57  tff(c_16558, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_15824, c_16552])).
% 9.32/3.57  tff(c_16565, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_16558])).
% 9.32/3.57  tff(c_16387, plain, (![A_2837, B_2838, C_2839]: (k1_relset_1(A_2837, B_2838, C_2839)=k1_relat_1(C_2839) | ~m1_subset_1(C_2839, k1_zfmisc_1(k2_zfmisc_1(A_2837, B_2838))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.32/3.57  tff(c_16411, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_14060, c_16387])).
% 9.32/3.57  tff(c_17076, plain, (![B_2884, C_2885, A_2886]: (k1_xboole_0=B_2884 | v1_funct_2(C_2885, A_2886, B_2884) | k1_relset_1(A_2886, B_2884, C_2885)!=A_2886 | ~m1_subset_1(C_2885, k1_zfmisc_1(k2_zfmisc_1(A_2886, B_2884))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.32/3.57  tff(c_17088, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_14060, c_17076])).
% 9.32/3.57  tff(c_17109, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16411, c_17088])).
% 9.32/3.57  tff(c_17110, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_14059, c_17109])).
% 9.32/3.57  tff(c_17115, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_17110])).
% 9.32/3.57  tff(c_17118, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_42, c_17115])).
% 9.32/3.57  tff(c_17121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15928, c_90, c_84, c_16565, c_17118])).
% 9.32/3.57  tff(c_17122, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_17110])).
% 9.32/3.57  tff(c_15986, plain, (![B_2783, A_2784]: (k1_xboole_0=B_2783 | k1_xboole_0=A_2784 | k2_zfmisc_1(A_2784, B_2783)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.32/3.57  tff(c_15989, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_15821, c_15986])).
% 9.32/3.57  tff(c_16000, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_15989])).
% 9.32/3.57  tff(c_17147, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17122, c_16000])).
% 9.32/3.57  tff(c_17159, plain, (![B_10]: (k2_zfmisc_1('#skF_3', B_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17122, c_17122, c_22])).
% 9.32/3.57  tff(c_17303, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17159, c_15821])).
% 9.32/3.57  tff(c_17305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17147, c_17303])).
% 9.32/3.57  tff(c_17307, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_15989])).
% 9.32/3.57  tff(c_17306, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_15989])).
% 9.32/3.57  tff(c_17516, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17307, c_17307, c_17306])).
% 9.32/3.57  tff(c_17517, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_17516])).
% 9.32/3.57  tff(c_14070, plain, (![B_2607]: ('#skF_2'(k1_xboole_0, B_2607)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_378])).
% 9.32/3.57  tff(c_14081, plain, (![B_2607]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2607))), inference(superposition, [status(thm), theory('equality')], [c_14070, c_62])).
% 9.32/3.57  tff(c_17312, plain, (![B_2607]: (v1_funct_2('#skF_5', '#skF_5', B_2607))), inference(demodulation, [status(thm), theory('equality')], [c_17307, c_17307, c_14081])).
% 9.32/3.57  tff(c_17931, plain, (![B_2607]: (v1_funct_2('#skF_4', '#skF_4', B_2607))), inference(demodulation, [status(thm), theory('equality')], [c_17517, c_17517, c_17312])).
% 9.32/3.57  tff(c_17325, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17307, c_8])).
% 9.32/3.57  tff(c_17528, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17517, c_17325])).
% 9.32/3.57  tff(c_17319, plain, (![B_10]: (k2_zfmisc_1('#skF_5', B_10)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17307, c_17307, c_22])).
% 9.32/3.57  tff(c_17522, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17517, c_17517, c_17319])).
% 9.32/3.57  tff(c_17449, plain, (![C_2899, B_2900, A_2901]: (~v1_xboole_0(C_2899) | ~m1_subset_1(B_2900, k1_zfmisc_1(C_2899)) | ~r2_hidden(A_2901, B_2900))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.32/3.57  tff(c_17466, plain, (![A_2901]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3')) | ~r2_hidden(A_2901, k2_funct_1('#skF_5')))), inference(resolution, [status(thm)], [c_14060, c_17449])).
% 9.32/3.57  tff(c_17518, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_17466])).
% 9.32/3.57  tff(c_17654, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17522, c_17518])).
% 9.32/3.57  tff(c_17657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17528, c_17654])).
% 9.32/3.57  tff(c_17658, plain, (![A_2901]: (~r2_hidden(A_2901, k2_funct_1('#skF_5')))), inference(splitRight, [status(thm)], [c_17466])).
% 9.32/3.57  tff(c_17734, plain, (![A_2922]: (~r2_hidden(A_2922, k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_17517, c_17658])).
% 9.32/3.57  tff(c_17739, plain, (![B_2]: (r1_tarski(k2_funct_1('#skF_4'), B_2))), inference(resolution, [status(thm)], [c_6, c_17734])).
% 9.32/3.57  tff(c_17311, plain, (![A_8]: (A_8='#skF_5' | ~r1_tarski(A_8, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_17307, c_17307, c_396])).
% 9.32/3.57  tff(c_17947, plain, (![A_2932]: (A_2932='#skF_4' | ~r1_tarski(A_2932, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_17517, c_17517, c_17311])).
% 9.32/3.57  tff(c_17960, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_17739, c_17947])).
% 9.32/3.57  tff(c_17681, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17517, c_14059])).
% 9.32/3.57  tff(c_17966, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17960, c_17681])).
% 9.32/3.57  tff(c_17973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17931, c_17966])).
% 9.32/3.57  tff(c_17974, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_17516])).
% 9.32/3.57  tff(c_17318, plain, (![A_83]: ('#skF_2'(A_83, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17307, c_17307, c_387])).
% 9.32/3.57  tff(c_18237, plain, (![A_2950]: ('#skF_2'(A_2950, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17974, c_17974, c_17318])).
% 9.32/3.57  tff(c_18248, plain, (![A_2950]: (v1_funct_2('#skF_3', A_2950, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18237, c_62])).
% 9.32/3.57  tff(c_17320, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17307, c_17307, c_20])).
% 9.32/3.57  tff(c_17984, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17974, c_17974, c_17320])).
% 9.32/3.57  tff(c_18000, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_17974, c_14060])).
% 9.32/3.57  tff(c_18413, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17984, c_18000])).
% 9.32/3.57  tff(c_18422, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_18413, c_24])).
% 9.32/3.57  tff(c_18384, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17974, c_17974, c_17311])).
% 9.32/3.57  tff(c_18434, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_18422, c_18384])).
% 9.32/3.57  tff(c_18001, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17974, c_14059])).
% 9.32/3.57  tff(c_18441, plain, (~v1_funct_2('#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18434, c_18001])).
% 9.32/3.57  tff(c_18448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18248, c_18441])).
% 9.32/3.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.57  
% 9.32/3.57  Inference rules
% 9.32/3.57  ----------------------
% 9.32/3.57  #Ref     : 0
% 9.32/3.57  #Sup     : 4118
% 9.32/3.57  #Fact    : 0
% 9.32/3.57  #Define  : 0
% 9.32/3.58  #Split   : 59
% 9.32/3.58  #Chain   : 0
% 9.32/3.58  #Close   : 0
% 9.32/3.58  
% 9.32/3.58  Ordering : KBO
% 9.32/3.58  
% 9.32/3.58  Simplification rules
% 9.32/3.58  ----------------------
% 9.32/3.58  #Subsume      : 671
% 9.32/3.58  #Demod        : 4690
% 9.32/3.58  #Tautology    : 2204
% 9.32/3.58  #SimpNegUnit  : 70
% 9.32/3.58  #BackRed      : 679
% 9.32/3.58  
% 9.32/3.58  #Partial instantiations: 77
% 9.32/3.58  #Strategies tried      : 1
% 9.32/3.58  
% 9.32/3.58  Timing (in seconds)
% 9.32/3.58  ----------------------
% 9.32/3.58  Preprocessing        : 0.36
% 9.32/3.58  Parsing              : 0.19
% 9.32/3.58  CNF conversion       : 0.02
% 9.32/3.58  Main loop            : 2.31
% 9.32/3.58  Inferencing          : 0.76
% 9.32/3.58  Reduction            : 0.86
% 9.32/3.58  Demodulation         : 0.63
% 9.32/3.58  BG Simplification    : 0.07
% 9.32/3.58  Subsumption          : 0.43
% 9.32/3.58  Abstraction          : 0.09
% 9.32/3.58  MUC search           : 0.00
% 9.32/3.58  Cooper               : 0.00
% 9.32/3.58  Total                : 2.79
% 9.32/3.58  Index Insertion      : 0.00
% 9.32/3.58  Index Deletion       : 0.00
% 9.32/3.58  Index Matching       : 0.00
% 9.32/3.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
