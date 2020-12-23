%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:42 EST 2020

% Result     : Theorem 14.20s
% Output     : CNFRefutation 14.42s
% Verified   : 
% Statistics : Number of formulae       :  490 (19157 expanded)
%              Number of leaves         :   40 (6143 expanded)
%              Depth                    :   20
%              Number of atoms          :  844 (45538 expanded)
%              Number of equality atoms :  285 (9550 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_157,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_100,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_128,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_80,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_40189,plain,(
    ! [C_2340,A_2341,B_2342] :
      ( v1_xboole_0(C_2340)
      | ~ m1_subset_1(C_2340,k1_zfmisc_1(k2_zfmisc_1(A_2341,B_2342)))
      | ~ v1_xboole_0(A_2341) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40214,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_40189])).

tff(c_40219,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40214])).

tff(c_38536,plain,(
    ! [C_2209,A_2210,B_2211] :
      ( v1_relat_1(C_2209)
      | ~ m1_subset_1(C_2209,k1_zfmisc_1(k2_zfmisc_1(A_2210,B_2211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38557,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_38536])).

tff(c_84,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_78,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_76,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_40570,plain,(
    ! [A_2375,B_2376,C_2377] :
      ( k2_relset_1(A_2375,B_2376,C_2377) = k2_relat_1(C_2377)
      | ~ m1_subset_1(C_2377,k1_zfmisc_1(k2_zfmisc_1(A_2375,B_2376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40587,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_40570])).

tff(c_40603,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_40587])).

tff(c_40,plain,(
    ! [A_21] :
      ( k1_relat_1(k2_funct_1(A_21)) = k2_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_407,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_xboole_0(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_426,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_407])).

tff(c_431,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_82,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_34,plain,(
    ! [A_20] :
      ( v1_funct_1(k2_funct_1(A_20))
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_74,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_143,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_146,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_143])).

tff(c_149,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_146])).

tff(c_188,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_195,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_188])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_195])).

tff(c_209,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_224,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_307,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_324,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_307])).

tff(c_913,plain,(
    ! [A_144,B_145,C_146] :
      ( k2_relset_1(A_144,B_145,C_146) = k2_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_930,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_913])).

tff(c_946,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_930])).

tff(c_36,plain,(
    ! [A_20] :
      ( v1_relat_1(k2_funct_1(A_20))
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_210,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_739,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_766,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_739])).

tff(c_1697,plain,(
    ! [B_219,A_220,C_221] :
      ( k1_xboole_0 = B_219
      | k1_relset_1(A_220,B_219,C_221) = A_220
      | ~ v1_funct_2(C_221,A_220,B_219)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_220,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1720,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_1697])).

tff(c_1741,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_766,c_1720])).

tff(c_1747,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1741])).

tff(c_692,plain,(
    ! [A_131] :
      ( k2_relat_1(k2_funct_1(A_131)) = k1_relat_1(A_131)
      | ~ v2_funct_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_64,plain,(
    ! [A_38] :
      ( v1_funct_2(A_38,k1_relat_1(A_38),k2_relat_1(A_38))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4889,plain,(
    ! [A_390] :
      ( v1_funct_2(k2_funct_1(A_390),k1_relat_1(k2_funct_1(A_390)),k1_relat_1(A_390))
      | ~ v1_funct_1(k2_funct_1(A_390))
      | ~ v1_relat_1(k2_funct_1(A_390))
      | ~ v2_funct_1(A_390)
      | ~ v1_funct_1(A_390)
      | ~ v1_relat_1(A_390) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_64])).

tff(c_4895,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1747,c_4889])).

tff(c_4905,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_84,c_78,c_210,c_4895])).

tff(c_4906,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4905])).

tff(c_4909,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_4906])).

tff(c_4913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_84,c_4909])).

tff(c_4915,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4905])).

tff(c_38,plain,(
    ! [A_21] :
      ( k2_relat_1(k2_funct_1(A_21)) = k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_801,plain,(
    ! [A_137] :
      ( m1_subset_1(A_137,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_137),k2_relat_1(A_137))))
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_5933,plain,(
    ! [A_438] :
      ( m1_subset_1(k2_funct_1(A_438),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_438)),k1_relat_1(A_438))))
      | ~ v1_funct_1(k2_funct_1(A_438))
      | ~ v1_relat_1(k2_funct_1(A_438))
      | ~ v2_funct_1(A_438)
      | ~ v1_funct_1(A_438)
      | ~ v1_relat_1(A_438) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_801])).

tff(c_5962,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1747,c_5933])).

tff(c_5980,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_84,c_78,c_4915,c_210,c_5962])).

tff(c_6006,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5980])).

tff(c_6022,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_84,c_78,c_946,c_6006])).

tff(c_6024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_6022])).

tff(c_6025,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1741])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_128,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_140,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_26,c_128])).

tff(c_6067,plain,(
    ! [A_14] : r1_tarski('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6025,c_140])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6070,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6025,c_6025,c_22])).

tff(c_62,plain,(
    ! [A_38] :
      ( m1_subset_1(A_38,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_38),k2_relat_1(A_38))))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_953,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_62])).

tff(c_960,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_84,c_953])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1001,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_960,c_28])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1033,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1001,c_14])).

tff(c_1290,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1033])).

tff(c_6222,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6070,c_1290])).

tff(c_6234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6067,c_6222])).

tff(c_6235,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1033])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_326,plain,(
    ! [C_85,B_86,A_87] :
      ( r2_hidden(C_85,B_86)
      | ~ r2_hidden(C_85,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_629,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_1'(A_125),B_126)
      | ~ r1_tarski(A_125,B_126)
      | v1_xboole_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_4,c_326])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_643,plain,(
    ! [B_126,A_125] :
      ( ~ v1_xboole_0(B_126)
      | ~ r1_tarski(A_125,B_126)
      | v1_xboole_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_629,c_2])).

tff(c_1028,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1001,c_643])).

tff(c_1039,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1028])).

tff(c_6238,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6235,c_1039])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7108,plain,(
    ! [B_503,A_504,C_505] :
      ( k1_xboole_0 = B_503
      | k1_relset_1(A_504,B_503,C_505) = A_504
      | ~ v1_funct_2(C_505,A_504,B_503)
      | ~ m1_subset_1(C_505,k1_zfmisc_1(k2_zfmisc_1(A_504,B_503))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7131,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_7108])).

tff(c_7149,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_766,c_7131])).

tff(c_7155,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7149])).

tff(c_7159,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7155,c_6235])).

tff(c_139,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_128])).

tff(c_211,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_218,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_139,c_211])).

tff(c_363,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_7204,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7159,c_363])).

tff(c_7210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7204])).

tff(c_7211,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7149])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6272,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6235,c_20])).

tff(c_6355,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_6272])).

tff(c_7228,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7211,c_6355])).

tff(c_7255,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7211,c_7211,c_22])).

tff(c_7333,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7255,c_6235])).

tff(c_7340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7228,c_7333])).

tff(c_7342,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6272])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7378,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7342,c_12])).

tff(c_7382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6238,c_7378])).

tff(c_7383,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1028])).

tff(c_7384,plain,(
    v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1028])).

tff(c_242,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_2'(A_69,B_70),A_69)
      | r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_246,plain,(
    ! [A_69,B_70] :
      ( ~ v1_xboole_0(A_69)
      | r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_242,c_2])).

tff(c_247,plain,(
    ! [A_71,B_72] :
      ( ~ v1_xboole_0(A_71)
      | r1_tarski(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_242,c_2])).

tff(c_277,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_247,c_14])).

tff(c_290,plain,(
    ! [B_70,A_69] :
      ( B_70 = A_69
      | ~ v1_xboole_0(B_70)
      | ~ v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_246,c_277])).

tff(c_7401,plain,(
    ! [A_69] :
      ( A_69 = '#skF_5'
      | ~ v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_7383,c_290])).

tff(c_7616,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_7384,c_7401])).

tff(c_219,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_140,c_211])).

tff(c_258,plain,(
    ! [A_71] :
      ( k1_xboole_0 = A_71
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_247,c_219])).

tff(c_7402,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_7383,c_258])).

tff(c_7973,plain,(
    ! [B_543,A_544] :
      ( B_543 = '#skF_5'
      | A_544 = '#skF_5'
      | k2_zfmisc_1(A_544,B_543) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7402,c_7402,c_7402,c_20])).

tff(c_7983,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_7616,c_7973])).

tff(c_7988,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_7983])).

tff(c_44,plain,(
    ! [C_28,A_25,B_26] :
      ( v1_xboole_0(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_998,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_960,c_44])).

tff(c_1002,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_998])).

tff(c_8030,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7988,c_1002])).

tff(c_8035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7383,c_8030])).

tff(c_8036,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7983])).

tff(c_8066,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8036,c_7383])).

tff(c_7425,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7402,c_7402,c_22])).

tff(c_8058,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8036,c_8036,c_7425])).

tff(c_291,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_139,c_277])).

tff(c_295,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_8266,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8058,c_295])).

tff(c_8269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8066,c_8266])).

tff(c_8271,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_998])).

tff(c_8270,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_998])).

tff(c_8393,plain,(
    ! [A_559] :
      ( A_559 = '#skF_5'
      | ~ v1_xboole_0(A_559) ) ),
    inference(resolution,[status(thm)],[c_8270,c_290])).

tff(c_8403,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8271,c_8393])).

tff(c_8289,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8270,c_258])).

tff(c_8513,plain,(
    ! [A_562] : m1_subset_1('#skF_5',k1_zfmisc_1(A_562)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8289,c_26])).

tff(c_46,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8521,plain,(
    ! [A_29,B_30] : k1_relset_1(A_29,B_30,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8513,c_46])).

tff(c_8540,plain,(
    ! [A_29,B_30] : k1_relset_1(A_29,B_30,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8403,c_8521])).

tff(c_8334,plain,(
    ! [A_14] : m1_subset_1('#skF_5',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8289,c_26])).

tff(c_60,plain,(
    ! [B_36,A_35,C_37] :
      ( k1_xboole_0 = B_36
      | k1_relset_1(A_35,B_36,C_37) = A_35
      | ~ v1_funct_2(C_37,A_35,B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_8860,plain,(
    ! [B_590,A_591,C_592] :
      ( B_590 = '#skF_5'
      | k1_relset_1(A_591,B_590,C_592) = A_591
      | ~ v1_funct_2(C_592,A_591,B_590)
      | ~ m1_subset_1(C_592,k1_zfmisc_1(k2_zfmisc_1(A_591,B_590))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8289,c_60])).

tff(c_8867,plain,(
    ! [B_590,A_591] :
      ( B_590 = '#skF_5'
      | k1_relset_1(A_591,B_590,'#skF_5') = A_591
      | ~ v1_funct_2('#skF_5',A_591,B_590) ) ),
    inference(resolution,[status(thm)],[c_8334,c_8860])).

tff(c_9028,plain,(
    ! [B_602,A_603] :
      ( B_602 = '#skF_5'
      | A_603 = '#skF_5'
      | ~ v1_funct_2('#skF_5',A_603,B_602) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8540,c_8867])).

tff(c_9069,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_82,c_9028])).

tff(c_9070,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9069])).

tff(c_9104,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9070,c_8270])).

tff(c_9116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_431,c_9104])).

tff(c_9117,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9069])).

tff(c_9152,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9117,c_8270])).

tff(c_8333,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8289,c_8289,c_22])).

tff(c_9145,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9117,c_9117,c_8333])).

tff(c_9318,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9145,c_295])).

tff(c_9321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9152,c_9318])).

tff(c_9323,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_9346,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9323,c_258])).

tff(c_9322,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_9335,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9322,c_258])).

tff(c_9375,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9346,c_9335])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9365,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_5',B_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9335,c_9335,c_24])).

tff(c_9457,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_3',B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9375,c_9375,c_9365])).

tff(c_9458,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9457,c_295])).

tff(c_9461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9323,c_9458])).

tff(c_9462,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_9464,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9462,c_295])).

tff(c_9466,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9462,c_80])).

tff(c_10471,plain,(
    ! [A_705,B_706,C_707] :
      ( k2_relset_1(A_705,B_706,C_707) = k2_relat_1(C_707)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(k2_zfmisc_1(A_705,B_706))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10559,plain,(
    ! [C_714] :
      ( k2_relset_1('#skF_3','#skF_4',C_714) = k2_relat_1(C_714)
      | ~ m1_subset_1(C_714,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9462,c_10471])).

tff(c_10566,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9466,c_10559])).

tff(c_10577,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10566])).

tff(c_10049,plain,(
    ! [A_670,B_671,C_672] :
      ( k1_relset_1(A_670,B_671,C_672) = k1_relat_1(C_672)
      | ~ m1_subset_1(C_672,k1_zfmisc_1(k2_zfmisc_1(A_670,B_671))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10186,plain,(
    ! [C_680] :
      ( k1_relset_1('#skF_3','#skF_4',C_680) = k1_relat_1(C_680)
      | ~ m1_subset_1(C_680,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9462,c_10049])).

tff(c_10203,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9466,c_10186])).

tff(c_12417,plain,(
    ! [B_828,C_829,A_830] :
      ( k1_xboole_0 = B_828
      | v1_funct_2(C_829,A_830,B_828)
      | k1_relset_1(A_830,B_828,C_829) != A_830
      | ~ m1_subset_1(C_829,k1_zfmisc_1(k2_zfmisc_1(A_830,B_828))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12436,plain,(
    ! [C_829] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(C_829,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',C_829) != '#skF_3'
      | ~ m1_subset_1(C_829,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9462,c_12417])).

tff(c_12511,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_12436])).

tff(c_9473,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_9462,c_20])).

tff(c_9524,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_9473])).

tff(c_12543,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12511,c_9524])).

tff(c_12552,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12511,c_12511,c_22])).

tff(c_11276,plain,(
    ! [B_776,C_777,A_778] :
      ( k1_xboole_0 = B_776
      | v1_funct_2(C_777,A_778,B_776)
      | k1_relset_1(A_778,B_776,C_777) != A_778
      | ~ m1_subset_1(C_777,k1_zfmisc_1(k2_zfmisc_1(A_778,B_776))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_11295,plain,(
    ! [C_777] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(C_777,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',C_777) != '#skF_3'
      | ~ m1_subset_1(C_777,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9462,c_11276])).

tff(c_11405,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11295])).

tff(c_11445,plain,(
    ! [A_14] : r1_tarski('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11405,c_140])).

tff(c_11448,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11405,c_11405,c_22])).

tff(c_10259,plain,(
    ! [A_687] :
      ( m1_subset_1(A_687,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_687),k2_relat_1(A_687))))
      | ~ v1_funct_1(A_687)
      | ~ v1_relat_1(A_687) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10284,plain,(
    ! [A_687] :
      ( r1_tarski(A_687,k2_zfmisc_1(k1_relat_1(A_687),k2_relat_1(A_687)))
      | ~ v1_funct_1(A_687)
      | ~ v1_relat_1(A_687) ) ),
    inference(resolution,[status(thm)],[c_10259,c_28])).

tff(c_10584,plain,
    ( r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10577,c_10284])).

tff(c_10594,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_84,c_10584])).

tff(c_10627,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_10594,c_14])).

tff(c_11203,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_10627])).

tff(c_11601,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11448,c_11203])).

tff(c_11609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11445,c_11601])).

tff(c_11611,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11295])).

tff(c_11724,plain,(
    ! [B_798,A_799,C_800] :
      ( k1_xboole_0 = B_798
      | k1_relset_1(A_799,B_798,C_800) = A_799
      | ~ v1_funct_2(C_800,A_799,B_798)
      | ~ m1_subset_1(C_800,k1_zfmisc_1(k2_zfmisc_1(A_799,B_798))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_11747,plain,(
    ! [C_800] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_800) = '#skF_3'
      | ~ v1_funct_2(C_800,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_800,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9462,c_11724])).

tff(c_12261,plain,(
    ! [C_823] :
      ( k1_relset_1('#skF_3','#skF_4',C_823) = '#skF_3'
      | ~ v1_funct_2(C_823,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_823,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_11611,c_11747])).

tff(c_12276,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_9466,c_12261])).

tff(c_12290,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_10203,c_12276])).

tff(c_12295,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12290,c_11203])).

tff(c_12308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_9462,c_12295])).

tff(c_12309,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10627])).

tff(c_12702,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12552,c_12309])).

tff(c_12705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12543,c_12702])).

tff(c_12707,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12436])).

tff(c_12851,plain,(
    ! [B_848,A_849,C_850] :
      ( k1_xboole_0 = B_848
      | k1_relset_1(A_849,B_848,C_850) = A_849
      | ~ v1_funct_2(C_850,A_849,B_848)
      | ~ m1_subset_1(C_850,k1_zfmisc_1(k2_zfmisc_1(A_849,B_848))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12870,plain,(
    ! [C_850] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_850) = '#skF_3'
      | ~ v1_funct_2(C_850,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_850,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9462,c_12851])).

tff(c_13656,plain,(
    ! [C_886] :
      ( k1_relset_1('#skF_3','#skF_4',C_886) = '#skF_3'
      | ~ v1_funct_2(C_886,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_886,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12707,c_12870])).

tff(c_13671,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_9466,c_13656])).

tff(c_13685,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_10203,c_13671])).

tff(c_9868,plain,(
    ! [A_661] :
      ( k2_relat_1(k2_funct_1(A_661)) = k1_relat_1(A_661)
      | ~ v2_funct_1(A_661)
      | ~ v1_funct_1(A_661)
      | ~ v1_relat_1(A_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_15626,plain,(
    ! [A_978] :
      ( v1_funct_2(k2_funct_1(A_978),k1_relat_1(k2_funct_1(A_978)),k1_relat_1(A_978))
      | ~ v1_funct_1(k2_funct_1(A_978))
      | ~ v1_relat_1(k2_funct_1(A_978))
      | ~ v2_funct_1(A_978)
      | ~ v1_funct_1(A_978)
      | ~ v1_relat_1(A_978) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9868,c_64])).

tff(c_15629,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13685,c_15626])).

tff(c_15640,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_84,c_78,c_210,c_15629])).

tff(c_15643,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_15640])).

tff(c_15646,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_15643])).

tff(c_15650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_84,c_15646])).

tff(c_15652,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_15640])).

tff(c_16197,plain,(
    ! [A_1005] :
      ( m1_subset_1(k2_funct_1(A_1005),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1005)),k1_relat_1(A_1005))))
      | ~ v1_funct_1(k2_funct_1(A_1005))
      | ~ v1_relat_1(k2_funct_1(A_1005))
      | ~ v2_funct_1(A_1005)
      | ~ v1_funct_1(A_1005)
      | ~ v1_relat_1(A_1005) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10259])).

tff(c_16223,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13685,c_16197])).

tff(c_16242,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_84,c_78,c_15652,c_210,c_16223])).

tff(c_16270,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_16242])).

tff(c_16286,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_84,c_78,c_10577,c_16270])).

tff(c_16288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_16286])).

tff(c_16290,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9473])).

tff(c_16303,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16290,c_12])).

tff(c_16306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9464,c_16303])).

tff(c_16307,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_16308,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_16324,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16307,c_16308])).

tff(c_16328,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16324,c_258])).

tff(c_16315,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_16307,c_20])).

tff(c_16472,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16328,c_16328,c_16328,c_16315])).

tff(c_16473,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_16472])).

tff(c_16335,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16328,c_16328,c_22])).

tff(c_16480,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16473,c_16473,c_16335])).

tff(c_16489,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16473,c_224])).

tff(c_16644,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16480,c_16489])).

tff(c_16392,plain,(
    ! [A_1013] : m1_subset_1('#skF_5',k1_zfmisc_1(A_1013)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16328,c_26])).

tff(c_42,plain,(
    ! [C_24,A_22,B_23] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16400,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16392,c_42])).

tff(c_16478,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16473,c_16400])).

tff(c_16494,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16473,c_84])).

tff(c_16493,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16473,c_78])).

tff(c_16336,plain,(
    ! [A_14] : m1_subset_1('#skF_5',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16328,c_26])).

tff(c_16479,plain,(
    ! [A_14] : m1_subset_1('#skF_3',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16473,c_16336])).

tff(c_16986,plain,(
    ! [A_1084,B_1085,C_1086] :
      ( k1_relset_1(A_1084,B_1085,C_1086) = k1_relat_1(C_1086)
      | ~ m1_subset_1(C_1086,k1_zfmisc_1(k2_zfmisc_1(A_1084,B_1085))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_17004,plain,(
    ! [A_1084,B_1085] : k1_relset_1(A_1084,B_1085,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16479,c_16986])).

tff(c_16492,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16473,c_82])).

tff(c_16484,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16473,c_16328])).

tff(c_58,plain,(
    ! [B_36,C_37] :
      ( k1_relset_1(k1_xboole_0,B_36,C_37) = k1_xboole_0
      | ~ v1_funct_2(C_37,k1_xboole_0,B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_87,plain,(
    ! [B_36,C_37] :
      ( k1_relset_1(k1_xboole_0,B_36,C_37) = k1_xboole_0
      | ~ v1_funct_2(C_37,k1_xboole_0,B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_58])).

tff(c_21478,plain,(
    ! [B_1349,C_1350] :
      ( k1_relset_1('#skF_3',B_1349,C_1350) = '#skF_3'
      | ~ v1_funct_2(C_1350,'#skF_3',B_1349)
      | ~ m1_subset_1(C_1350,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16484,c_16484,c_16484,c_16484,c_87])).

tff(c_21483,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16492,c_21478])).

tff(c_21490,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16479,c_17004,c_21483])).

tff(c_16490,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16473,c_210])).

tff(c_16732,plain,(
    ! [A_1049] :
      ( k2_relat_1(k2_funct_1(A_1049)) = k1_relat_1(A_1049)
      | ~ v2_funct_1(A_1049)
      | ~ v1_funct_1(A_1049)
      | ~ v1_relat_1(A_1049) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26368,plain,(
    ! [A_1562] :
      ( v1_funct_2(k2_funct_1(A_1562),k1_relat_1(k2_funct_1(A_1562)),k1_relat_1(A_1562))
      | ~ v1_funct_1(k2_funct_1(A_1562))
      | ~ v1_relat_1(k2_funct_1(A_1562))
      | ~ v2_funct_1(A_1562)
      | ~ v1_funct_1(A_1562)
      | ~ v1_relat_1(A_1562) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16732,c_64])).

tff(c_26377,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21490,c_26368])).

tff(c_26389,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16478,c_16494,c_16493,c_16490,c_26377])).

tff(c_26390,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_26389])).

tff(c_26393,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_26390])).

tff(c_26397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16478,c_16494,c_26393])).

tff(c_26399,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26389])).

tff(c_16858,plain,(
    ! [A_1067,B_1068,C_1069] :
      ( k2_relset_1(A_1067,B_1068,C_1069) = k2_relat_1(C_1069)
      | ~ m1_subset_1(C_1069,k1_zfmisc_1(k2_zfmisc_1(A_1067,B_1068))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_16883,plain,(
    ! [A_1072,B_1073] : k2_relset_1(A_1072,B_1073,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16479,c_16858])).

tff(c_16491,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16473,c_76])).

tff(c_16887,plain,(
    k2_relat_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_16883,c_16491])).

tff(c_21371,plain,(
    ! [A_1346] :
      ( m1_subset_1(A_1346,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1346),k2_relat_1(A_1346))))
      | ~ v1_funct_1(A_1346)
      | ~ v1_relat_1(A_1346) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_26967,plain,(
    ! [A_1588] :
      ( m1_subset_1(k2_funct_1(A_1588),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1588),k2_relat_1(k2_funct_1(A_1588)))))
      | ~ v1_funct_1(k2_funct_1(A_1588))
      | ~ v1_relat_1(k2_funct_1(A_1588))
      | ~ v2_funct_1(A_1588)
      | ~ v1_funct_1(A_1588)
      | ~ v1_relat_1(A_1588) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_21371])).

tff(c_26999,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16887,c_26967])).

tff(c_27019,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16478,c_16494,c_16493,c_26399,c_16490,c_26999])).

tff(c_27045,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_27019])).

tff(c_27061,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16478,c_16494,c_16493,c_16480,c_21490,c_27045])).

tff(c_27063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16644,c_27061])).

tff(c_27064,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16472])).

tff(c_16334,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_5',B_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16328,c_16328,c_24])).

tff(c_27073,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27064,c_27064,c_16334])).

tff(c_27081,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27064,c_224])).

tff(c_27232,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27073,c_27081])).

tff(c_27070,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27064,c_16400])).

tff(c_27086,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27064,c_84])).

tff(c_27085,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27064,c_78])).

tff(c_27082,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27064,c_210])).

tff(c_27071,plain,(
    ! [A_14] : m1_subset_1('#skF_4',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27064,c_16336])).

tff(c_32957,plain,(
    ! [A_1972,B_1973,C_1974] :
      ( k2_relset_1(A_1972,B_1973,C_1974) = k2_relat_1(C_1974)
      | ~ m1_subset_1(C_1974,k1_zfmisc_1(k2_zfmisc_1(A_1972,B_1973))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32986,plain,(
    ! [A_1975,B_1976] : k2_relset_1(A_1975,B_1976,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_27071,c_32957])).

tff(c_27083,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27064,c_76])).

tff(c_32990,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_32986,c_27083])).

tff(c_27338,plain,(
    ! [A_1619] :
      ( k1_relat_1(k2_funct_1(A_1619)) = k2_relat_1(A_1619)
      | ~ v2_funct_1(A_1619)
      | ~ v1_funct_1(A_1619)
      | ~ v1_relat_1(A_1619) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_37599,plain,(
    ! [A_2168] :
      ( v1_funct_2(k2_funct_1(A_2168),k2_relat_1(A_2168),k2_relat_1(k2_funct_1(A_2168)))
      | ~ v1_funct_1(k2_funct_1(A_2168))
      | ~ v1_relat_1(k2_funct_1(A_2168))
      | ~ v2_funct_1(A_2168)
      | ~ v1_funct_1(A_2168)
      | ~ v1_relat_1(A_2168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27338,c_64])).

tff(c_37608,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32990,c_37599])).

tff(c_37620,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27070,c_27086,c_27085,c_27082,c_37608])).

tff(c_37621,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_37620])).

tff(c_37624,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_37621])).

tff(c_37628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27070,c_27086,c_37624])).

tff(c_37630,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_37620])).

tff(c_27515,plain,(
    ! [A_1641] :
      ( m1_subset_1(A_1641,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1641),k2_relat_1(A_1641))))
      | ~ v1_funct_1(A_1641)
      | ~ v1_relat_1(A_1641) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38396,plain,(
    ! [A_2196] :
      ( m1_subset_1(k2_funct_1(A_2196),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_2196),k2_relat_1(k2_funct_1(A_2196)))))
      | ~ v1_funct_1(k2_funct_1(A_2196))
      | ~ v1_relat_1(k2_funct_1(A_2196))
      | ~ v2_funct_1(A_2196)
      | ~ v1_funct_1(A_2196)
      | ~ v1_relat_1(A_2196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_27515])).

tff(c_38428,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32990,c_38396])).

tff(c_38448,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27070,c_27086,c_27085,c_37630,c_27082,c_27073,c_38428])).

tff(c_38450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27232,c_38448])).

tff(c_38451,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_38452,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_40706,plain,(
    ! [A_2384,B_2385,C_2386] :
      ( k1_relset_1(A_2384,B_2385,C_2386) = k1_relat_1(C_2386)
      | ~ m1_subset_1(C_2386,k1_zfmisc_1(k2_zfmisc_1(A_2384,B_2385))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40736,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38452,c_40706])).

tff(c_41577,plain,(
    ! [B_2461,C_2462,A_2463] :
      ( k1_xboole_0 = B_2461
      | v1_funct_2(C_2462,A_2463,B_2461)
      | k1_relset_1(A_2463,B_2461,C_2462) != A_2463
      | ~ m1_subset_1(C_2462,k1_zfmisc_1(k2_zfmisc_1(A_2463,B_2461))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_41596,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_38452,c_41577])).

tff(c_41620,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40736,c_41596])).

tff(c_41621,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_38451,c_41620])).

tff(c_41635,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_41621])).

tff(c_41638,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_41635])).

tff(c_41641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38557,c_84,c_78,c_40603,c_41638])).

tff(c_41642,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_41621])).

tff(c_41686,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41642,c_12])).

tff(c_41688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40219,c_41686])).

tff(c_41690,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_40214])).

tff(c_38474,plain,(
    ! [A_2198,B_2199] :
      ( r2_hidden('#skF_2'(A_2198,B_2199),A_2198)
      | r1_tarski(A_2198,B_2199) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38479,plain,(
    ! [A_2200,B_2201] :
      ( ~ v1_xboole_0(A_2200)
      | r1_tarski(A_2200,B_2201) ) ),
    inference(resolution,[status(thm)],[c_38474,c_2])).

tff(c_38490,plain,(
    ! [A_2200] :
      ( k1_xboole_0 = A_2200
      | ~ v1_xboole_0(A_2200) ) ),
    inference(resolution,[status(thm)],[c_38479,c_219])).

tff(c_41713,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_41690,c_38490])).

tff(c_41689,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_40214])).

tff(c_41702,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_41689,c_38490])).

tff(c_41733,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41713,c_41702])).

tff(c_41724,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41702,c_41702,c_22])).

tff(c_41779,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41733,c_41733,c_41724])).

tff(c_38469,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38452,c_28])).

tff(c_38509,plain,(
    ! [B_2205,A_2206] :
      ( B_2205 = A_2206
      | ~ r1_tarski(B_2205,A_2206)
      | ~ v1_xboole_0(A_2206) ) ),
    inference(resolution,[status(thm)],[c_38479,c_14])).

tff(c_38526,plain,
    ( k2_zfmisc_1('#skF_4','#skF_3') = k2_funct_1('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38469,c_38509])).

tff(c_38535,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_38526])).

tff(c_41780,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41779,c_38535])).

tff(c_41783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41690,c_41780])).

tff(c_41785,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_38526])).

tff(c_41816,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41785,c_38490])).

tff(c_41829,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_41816,c_20])).

tff(c_41876,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_41829])).

tff(c_41890,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41876,c_12])).

tff(c_41888,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41876,c_41876,c_22])).

tff(c_38470,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_38489,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_38479,c_38470])).

tff(c_41927,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41888,c_38489])).

tff(c_41933,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41890,c_41927])).

tff(c_41934,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_41829])).

tff(c_41950,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41934,c_12])).

tff(c_41947,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_3',B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41934,c_41934,c_24])).

tff(c_42010,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41947,c_38489])).

tff(c_42016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41950,c_42010])).

tff(c_42017,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_42276,plain,(
    ! [C_2518,A_2519,B_2520] :
      ( v1_xboole_0(C_2518)
      | ~ m1_subset_1(C_2518,k1_zfmisc_1(k2_zfmisc_1(A_2519,B_2520)))
      | ~ v1_xboole_0(A_2519) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42279,plain,(
    ! [C_2518] :
      ( v1_xboole_0(C_2518)
      | ~ m1_subset_1(C_2518,k1_zfmisc_1('#skF_5'))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42017,c_42276])).

tff(c_42395,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42279])).

tff(c_42020,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42017,c_80])).

tff(c_42092,plain,(
    ! [C_2492,A_2493,B_2494] :
      ( v1_relat_1(C_2492)
      | ~ m1_subset_1(C_2492,k1_zfmisc_1(k2_zfmisc_1(A_2493,B_2494))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42125,plain,(
    ! [C_2496] :
      ( v1_relat_1(C_2496)
      | ~ m1_subset_1(C_2496,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42017,c_42092])).

tff(c_42137,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42020,c_42125])).

tff(c_43606,plain,(
    ! [A_2612,B_2613,C_2614] :
      ( k2_relset_1(A_2612,B_2613,C_2614) = k2_relat_1(C_2614)
      | ~ m1_subset_1(C_2614,k1_zfmisc_1(k2_zfmisc_1(A_2612,B_2613))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_43886,plain,(
    ! [C_2628] :
      ( k2_relset_1('#skF_3','#skF_4',C_2628) = k2_relat_1(C_2628)
      | ~ m1_subset_1(C_2628,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42017,c_43606])).

tff(c_43893,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42020,c_43886])).

tff(c_43904,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_43893])).

tff(c_43711,plain,(
    ! [A_2620,B_2621,C_2622] :
      ( k1_relset_1(A_2620,B_2621,C_2622) = k1_relat_1(C_2622)
      | ~ m1_subset_1(C_2622,k1_zfmisc_1(k2_zfmisc_1(A_2620,B_2621))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_43741,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38452,c_43711])).

tff(c_44737,plain,(
    ! [B_2712,C_2713,A_2714] :
      ( k1_xboole_0 = B_2712
      | v1_funct_2(C_2713,A_2714,B_2712)
      | k1_relset_1(A_2714,B_2712,C_2713) != A_2714
      | ~ m1_subset_1(C_2713,k1_zfmisc_1(k2_zfmisc_1(A_2714,B_2712))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44759,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_38452,c_44737])).

tff(c_44782,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43741,c_44759])).

tff(c_44783,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_38451,c_44782])).

tff(c_44790,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_44783])).

tff(c_44793,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_44790])).

tff(c_44796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42137,c_84,c_78,c_43904,c_44793])).

tff(c_44797,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44783])).

tff(c_44842,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44797,c_12])).

tff(c_44844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42395,c_44842])).

tff(c_44846,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_42279])).

tff(c_42031,plain,(
    ! [A_2481,B_2482] :
      ( r2_hidden('#skF_2'(A_2481,B_2482),A_2481)
      | r1_tarski(A_2481,B_2482) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42036,plain,(
    ! [A_2483,B_2484] :
      ( ~ v1_xboole_0(A_2483)
      | r1_tarski(A_2483,B_2484) ) ),
    inference(resolution,[status(thm)],[c_42031,c_2])).

tff(c_42043,plain,(
    ! [A_2483] :
      ( k1_xboole_0 = A_2483
      | ~ v1_xboole_0(A_2483) ) ),
    inference(resolution,[status(thm)],[c_42036,c_219])).

tff(c_44858,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44846,c_42043])).

tff(c_42077,plain,(
    ! [B_2490,A_2491] :
      ( k1_xboole_0 = B_2490
      | k1_xboole_0 = A_2491
      | k2_zfmisc_1(A_2491,B_2490) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42080,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_42017,c_42077])).

tff(c_42091,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_42080])).

tff(c_44865,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44858,c_42091])).

tff(c_44871,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_3',B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44858,c_44858,c_24])).

tff(c_44918,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44871,c_42017])).

tff(c_44920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44865,c_44918])).

tff(c_44922,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42080])).

tff(c_44921,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42080])).

tff(c_45156,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44922,c_44922,c_44921])).

tff(c_45157,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_45156])).

tff(c_44930,plain,(
    ! [A_14] : m1_subset_1('#skF_5',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44922,c_26])).

tff(c_45209,plain,(
    ! [A_2745] : m1_subset_1('#skF_4',k1_zfmisc_1(A_2745)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45157,c_44930])).

tff(c_45217,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_45209,c_42])).

tff(c_45171,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45157,c_84])).

tff(c_45170,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45157,c_78])).

tff(c_44928,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_5',B_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44922,c_44922,c_24])).

tff(c_45198,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45157,c_45157,c_44928])).

tff(c_44948,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44922,c_44922,c_44921])).

tff(c_44949,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_44948])).

tff(c_44931,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44922,c_12])).

tff(c_44951,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44949,c_44931])).

tff(c_44996,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44949,c_44949,c_44928])).

tff(c_42055,plain,(
    ! [B_2486,A_2487] :
      ( B_2486 = A_2487
      | ~ r1_tarski(B_2486,A_2487)
      | ~ v1_xboole_0(A_2487) ) ),
    inference(resolution,[status(thm)],[c_42036,c_14])).

tff(c_42068,plain,
    ( k2_zfmisc_1('#skF_4','#skF_3') = k2_funct_1('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38469,c_42055])).

tff(c_44939,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_42068])).

tff(c_45043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44951,c_44996,c_44939])).

tff(c_45044,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44948])).

tff(c_45047,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45044,c_44931])).

tff(c_44929,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44922,c_44922,c_22])).

tff(c_45107,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45044,c_45044,c_44929])).

tff(c_45133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45047,c_45107,c_44939])).

tff(c_45134,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_42068])).

tff(c_45261,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45198,c_45157,c_45134])).

tff(c_45508,plain,(
    ! [A_2781] :
      ( k1_relat_1(k2_funct_1(A_2781)) = k2_relat_1(A_2781)
      | ~ v2_funct_1(A_2781)
      | ~ v1_funct_1(A_2781)
      | ~ v1_relat_1(A_2781) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_45520,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_45261,c_45508])).

tff(c_45524,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45217,c_45171,c_45170,c_45520])).

tff(c_45208,plain,(
    ! [A_14] : m1_subset_1('#skF_4',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45157,c_44930])).

tff(c_46516,plain,(
    ! [A_2868,B_2869,C_2870] :
      ( k2_relset_1(A_2868,B_2869,C_2870) = k2_relat_1(C_2870)
      | ~ m1_subset_1(C_2870,k1_zfmisc_1(k2_zfmisc_1(A_2868,B_2869))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_46530,plain,(
    ! [A_2868,B_2869] : k2_relset_1(A_2868,B_2869,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_45208,c_46516])).

tff(c_46542,plain,(
    ! [A_2871,B_2872] : k2_relset_1(A_2871,B_2872,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45524,c_46530])).

tff(c_45168,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45157,c_76])).

tff(c_46546,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_46542,c_45168])).

tff(c_46790,plain,(
    ! [A_2891,B_2892,C_2893] :
      ( k1_relset_1(A_2891,B_2892,C_2893) = k1_relat_1(C_2893)
      | ~ m1_subset_1(C_2893,k1_zfmisc_1(k2_zfmisc_1(A_2891,B_2892))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46807,plain,(
    ! [A_2891,B_2892] : k1_relset_1(A_2891,B_2892,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_45208,c_46790])).

tff(c_46818,plain,(
    ! [A_2891,B_2892] : k1_relset_1(A_2891,B_2892,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46546,c_46807])).

tff(c_45161,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45157,c_44922])).

tff(c_54,plain,(
    ! [C_37,B_36] :
      ( v1_funct_2(C_37,k1_xboole_0,B_36)
      | k1_relset_1(k1_xboole_0,B_36,C_37) != k1_xboole_0
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_88,plain,(
    ! [C_37,B_36] :
      ( v1_funct_2(C_37,k1_xboole_0,B_36)
      | k1_relset_1(k1_xboole_0,B_36,C_37) != k1_xboole_0
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_54])).

tff(c_47026,plain,(
    ! [C_2909,B_2910] :
      ( v1_funct_2(C_2909,'#skF_4',B_2910)
      | k1_relset_1('#skF_4',B_2910,C_2909) != '#skF_4'
      | ~ m1_subset_1(C_2909,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45161,c_45161,c_45161,c_45161,c_88])).

tff(c_47032,plain,(
    ! [B_2910] :
      ( v1_funct_2('#skF_4','#skF_4',B_2910)
      | k1_relset_1('#skF_4',B_2910,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_45208,c_47026])).

tff(c_47039,plain,(
    ! [B_2910] : v1_funct_2('#skF_4','#skF_4',B_2910) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46818,c_47032])).

tff(c_45166,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45157,c_38451])).

tff(c_45299,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45261,c_45166])).

tff(c_47044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47039,c_45299])).

tff(c_47045,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_45156])).

tff(c_47046,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_45156])).

tff(c_47065,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47045,c_47046])).

tff(c_50,plain,(
    ! [A_35] :
      ( v1_funct_2(k1_xboole_0,A_35,k1_xboole_0)
      | k1_xboole_0 = A_35
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_35,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_86,plain,(
    ! [A_35] :
      ( v1_funct_2(k1_xboole_0,A_35,k1_xboole_0)
      | k1_xboole_0 = A_35 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_50])).

tff(c_44927,plain,(
    ! [A_35] :
      ( v1_funct_2('#skF_5',A_35,'#skF_5')
      | A_35 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44922,c_44922,c_44922,c_86])).

tff(c_47238,plain,(
    ! [A_2928] :
      ( v1_funct_2('#skF_3',A_2928,'#skF_3')
      | A_2928 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47045,c_47045,c_47045,c_44927])).

tff(c_47110,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47045,c_47045,c_44929])).

tff(c_47170,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47110,c_47045,c_45134])).

tff(c_47055,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47045,c_38451])).

tff(c_47171,plain,(
    ~ v1_funct_2('#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47170,c_47055])).

tff(c_47241,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_47238,c_47171])).

tff(c_47245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47065,c_47241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n012.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 16:16:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.20/6.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.42/6.35  
% 14.42/6.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.42/6.36  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 14.42/6.36  
% 14.42/6.36  %Foreground sorts:
% 14.42/6.36  
% 14.42/6.36  
% 14.42/6.36  %Background operators:
% 14.42/6.36  
% 14.42/6.36  
% 14.42/6.36  %Foreground operators:
% 14.42/6.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.42/6.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.42/6.36  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.42/6.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.42/6.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.42/6.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.42/6.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.42/6.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.42/6.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.42/6.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.42/6.36  tff('#skF_5', type, '#skF_5': $i).
% 14.42/6.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.42/6.36  tff('#skF_3', type, '#skF_3': $i).
% 14.42/6.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.42/6.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.42/6.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.42/6.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.42/6.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.42/6.36  tff('#skF_4', type, '#skF_4': $i).
% 14.42/6.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.42/6.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.42/6.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.42/6.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.42/6.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.42/6.36  
% 14.42/6.40  tff(f_157, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 14.42/6.40  tff(f_92, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 14.42/6.40  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.42/6.40  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 14.42/6.40  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 14.42/6.40  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 14.42/6.40  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.42/6.40  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 14.42/6.40  tff(f_128, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 14.42/6.40  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 14.42/6.40  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.42/6.40  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.42/6.40  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.42/6.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 14.42/6.40  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 14.42/6.40  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.42/6.40  tff(c_80, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.42/6.40  tff(c_40189, plain, (![C_2340, A_2341, B_2342]: (v1_xboole_0(C_2340) | ~m1_subset_1(C_2340, k1_zfmisc_1(k2_zfmisc_1(A_2341, B_2342))) | ~v1_xboole_0(A_2341))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.42/6.40  tff(c_40214, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_40189])).
% 14.42/6.40  tff(c_40219, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_40214])).
% 14.42/6.40  tff(c_38536, plain, (![C_2209, A_2210, B_2211]: (v1_relat_1(C_2209) | ~m1_subset_1(C_2209, k1_zfmisc_1(k2_zfmisc_1(A_2210, B_2211))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.42/6.40  tff(c_38557, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_38536])).
% 14.42/6.40  tff(c_84, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.42/6.40  tff(c_78, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.42/6.40  tff(c_76, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.42/6.40  tff(c_40570, plain, (![A_2375, B_2376, C_2377]: (k2_relset_1(A_2375, B_2376, C_2377)=k2_relat_1(C_2377) | ~m1_subset_1(C_2377, k1_zfmisc_1(k2_zfmisc_1(A_2375, B_2376))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.42/6.40  tff(c_40587, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_40570])).
% 14.42/6.40  tff(c_40603, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_40587])).
% 14.42/6.40  tff(c_40, plain, (![A_21]: (k1_relat_1(k2_funct_1(A_21))=k2_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.42/6.40  tff(c_407, plain, (![C_96, A_97, B_98]: (v1_xboole_0(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_xboole_0(A_97))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.42/6.40  tff(c_426, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_407])).
% 14.42/6.40  tff(c_431, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_426])).
% 14.42/6.40  tff(c_82, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.42/6.40  tff(c_34, plain, (![A_20]: (v1_funct_1(k2_funct_1(A_20)) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.42/6.40  tff(c_74, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.42/6.40  tff(c_143, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_74])).
% 14.42/6.40  tff(c_146, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_143])).
% 14.42/6.40  tff(c_149, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_146])).
% 14.42/6.40  tff(c_188, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.42/6.40  tff(c_195, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_188])).
% 14.42/6.40  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_195])).
% 14.42/6.40  tff(c_209, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_74])).
% 14.42/6.40  tff(c_224, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_209])).
% 14.42/6.40  tff(c_307, plain, (![C_82, A_83, B_84]: (v1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.42/6.40  tff(c_324, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_307])).
% 14.42/6.40  tff(c_913, plain, (![A_144, B_145, C_146]: (k2_relset_1(A_144, B_145, C_146)=k2_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.42/6.40  tff(c_930, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_913])).
% 14.42/6.40  tff(c_946, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_930])).
% 14.42/6.40  tff(c_36, plain, (![A_20]: (v1_relat_1(k2_funct_1(A_20)) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.42/6.40  tff(c_210, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_74])).
% 14.42/6.40  tff(c_739, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.42/6.40  tff(c_766, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_739])).
% 14.42/6.40  tff(c_1697, plain, (![B_219, A_220, C_221]: (k1_xboole_0=B_219 | k1_relset_1(A_220, B_219, C_221)=A_220 | ~v1_funct_2(C_221, A_220, B_219) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_220, B_219))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.42/6.40  tff(c_1720, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_1697])).
% 14.42/6.40  tff(c_1741, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_766, c_1720])).
% 14.42/6.40  tff(c_1747, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1741])).
% 14.42/6.40  tff(c_692, plain, (![A_131]: (k2_relat_1(k2_funct_1(A_131))=k1_relat_1(A_131) | ~v2_funct_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.42/6.40  tff(c_64, plain, (![A_38]: (v1_funct_2(A_38, k1_relat_1(A_38), k2_relat_1(A_38)) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.42/6.40  tff(c_4889, plain, (![A_390]: (v1_funct_2(k2_funct_1(A_390), k1_relat_1(k2_funct_1(A_390)), k1_relat_1(A_390)) | ~v1_funct_1(k2_funct_1(A_390)) | ~v1_relat_1(k2_funct_1(A_390)) | ~v2_funct_1(A_390) | ~v1_funct_1(A_390) | ~v1_relat_1(A_390))), inference(superposition, [status(thm), theory('equality')], [c_692, c_64])).
% 14.42/6.40  tff(c_4895, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1747, c_4889])).
% 14.42/6.40  tff(c_4905, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_84, c_78, c_210, c_4895])).
% 14.42/6.40  tff(c_4906, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4905])).
% 14.42/6.40  tff(c_4909, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_4906])).
% 14.42/6.40  tff(c_4913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_324, c_84, c_4909])).
% 14.42/6.40  tff(c_4915, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_4905])).
% 14.42/6.40  tff(c_38, plain, (![A_21]: (k2_relat_1(k2_funct_1(A_21))=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.42/6.40  tff(c_801, plain, (![A_137]: (m1_subset_1(A_137, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_137), k2_relat_1(A_137)))) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.42/6.40  tff(c_5933, plain, (![A_438]: (m1_subset_1(k2_funct_1(A_438), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_438)), k1_relat_1(A_438)))) | ~v1_funct_1(k2_funct_1(A_438)) | ~v1_relat_1(k2_funct_1(A_438)) | ~v2_funct_1(A_438) | ~v1_funct_1(A_438) | ~v1_relat_1(A_438))), inference(superposition, [status(thm), theory('equality')], [c_38, c_801])).
% 14.42/6.40  tff(c_5962, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1747, c_5933])).
% 14.42/6.40  tff(c_5980, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_84, c_78, c_4915, c_210, c_5962])).
% 14.42/6.40  tff(c_6006, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_5980])).
% 14.42/6.40  tff(c_6022, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_84, c_78, c_946, c_6006])).
% 14.42/6.40  tff(c_6024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_6022])).
% 14.42/6.40  tff(c_6025, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1741])).
% 14.42/6.40  tff(c_26, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.42/6.40  tff(c_128, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.42/6.40  tff(c_140, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_26, c_128])).
% 14.42/6.40  tff(c_6067, plain, (![A_14]: (r1_tarski('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_6025, c_140])).
% 14.42/6.40  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.42/6.40  tff(c_6070, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6025, c_6025, c_22])).
% 14.42/6.40  tff(c_62, plain, (![A_38]: (m1_subset_1(A_38, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_38), k2_relat_1(A_38)))) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.42/6.40  tff(c_953, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_946, c_62])).
% 14.42/6.40  tff(c_960, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_84, c_953])).
% 14.42/6.40  tff(c_28, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.42/6.40  tff(c_1001, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_960, c_28])).
% 14.42/6.40  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.42/6.40  tff(c_1033, plain, (k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_1001, c_14])).
% 14.42/6.40  tff(c_1290, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1033])).
% 14.42/6.40  tff(c_6222, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6070, c_1290])).
% 14.42/6.40  tff(c_6234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6067, c_6222])).
% 14.42/6.40  tff(c_6235, plain, (k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_1033])).
% 14.42/6.40  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.42/6.40  tff(c_326, plain, (![C_85, B_86, A_87]: (r2_hidden(C_85, B_86) | ~r2_hidden(C_85, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.42/6.40  tff(c_629, plain, (![A_125, B_126]: (r2_hidden('#skF_1'(A_125), B_126) | ~r1_tarski(A_125, B_126) | v1_xboole_0(A_125))), inference(resolution, [status(thm)], [c_4, c_326])).
% 14.42/6.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.42/6.40  tff(c_643, plain, (![B_126, A_125]: (~v1_xboole_0(B_126) | ~r1_tarski(A_125, B_126) | v1_xboole_0(A_125))), inference(resolution, [status(thm)], [c_629, c_2])).
% 14.42/6.40  tff(c_1028, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1001, c_643])).
% 14.42/6.40  tff(c_1039, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_1028])).
% 14.42/6.40  tff(c_6238, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6235, c_1039])).
% 14.42/6.40  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.42/6.40  tff(c_7108, plain, (![B_503, A_504, C_505]: (k1_xboole_0=B_503 | k1_relset_1(A_504, B_503, C_505)=A_504 | ~v1_funct_2(C_505, A_504, B_503) | ~m1_subset_1(C_505, k1_zfmisc_1(k2_zfmisc_1(A_504, B_503))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.42/6.40  tff(c_7131, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_7108])).
% 14.42/6.40  tff(c_7149, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_766, c_7131])).
% 14.42/6.40  tff(c_7155, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_7149])).
% 14.42/6.40  tff(c_7159, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7155, c_6235])).
% 14.42/6.40  tff(c_139, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_128])).
% 14.42/6.40  tff(c_211, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.42/6.40  tff(c_218, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_139, c_211])).
% 14.42/6.40  tff(c_363, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_218])).
% 14.42/6.40  tff(c_7204, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7159, c_363])).
% 14.42/6.40  tff(c_7210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_7204])).
% 14.42/6.40  tff(c_7211, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_7149])).
% 14.42/6.40  tff(c_20, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.42/6.40  tff(c_6272, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')=k1_xboole_0 | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6235, c_20])).
% 14.42/6.40  tff(c_6355, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_6272])).
% 14.42/6.40  tff(c_7228, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7211, c_6355])).
% 14.42/6.40  tff(c_7255, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7211, c_7211, c_22])).
% 14.42/6.40  tff(c_7333, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7255, c_6235])).
% 14.42/6.40  tff(c_7340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7228, c_7333])).
% 14.42/6.40  tff(c_7342, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_6272])).
% 14.42/6.40  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.42/6.40  tff(c_7378, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7342, c_12])).
% 14.42/6.40  tff(c_7382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6238, c_7378])).
% 14.42/6.40  tff(c_7383, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1028])).
% 14.42/6.40  tff(c_7384, plain, (v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(splitRight, [status(thm)], [c_1028])).
% 14.42/6.40  tff(c_242, plain, (![A_69, B_70]: (r2_hidden('#skF_2'(A_69, B_70), A_69) | r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.42/6.40  tff(c_246, plain, (![A_69, B_70]: (~v1_xboole_0(A_69) | r1_tarski(A_69, B_70))), inference(resolution, [status(thm)], [c_242, c_2])).
% 14.42/6.40  tff(c_247, plain, (![A_71, B_72]: (~v1_xboole_0(A_71) | r1_tarski(A_71, B_72))), inference(resolution, [status(thm)], [c_242, c_2])).
% 14.42/6.40  tff(c_277, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_247, c_14])).
% 14.42/6.40  tff(c_290, plain, (![B_70, A_69]: (B_70=A_69 | ~v1_xboole_0(B_70) | ~v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_246, c_277])).
% 14.42/6.40  tff(c_7401, plain, (![A_69]: (A_69='#skF_5' | ~v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_7383, c_290])).
% 14.42/6.40  tff(c_7616, plain, (k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_7384, c_7401])).
% 14.42/6.40  tff(c_219, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(resolution, [status(thm)], [c_140, c_211])).
% 14.42/6.40  tff(c_258, plain, (![A_71]: (k1_xboole_0=A_71 | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_247, c_219])).
% 14.42/6.40  tff(c_7402, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_7383, c_258])).
% 14.42/6.40  tff(c_7973, plain, (![B_543, A_544]: (B_543='#skF_5' | A_544='#skF_5' | k2_zfmisc_1(A_544, B_543)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7402, c_7402, c_7402, c_20])).
% 14.42/6.40  tff(c_7983, plain, ('#skF_5'='#skF_4' | k1_relat_1('#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_7616, c_7973])).
% 14.42/6.40  tff(c_7988, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(splitLeft, [status(thm)], [c_7983])).
% 14.42/6.40  tff(c_44, plain, (![C_28, A_25, B_26]: (v1_xboole_0(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.42/6.40  tff(c_998, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_960, c_44])).
% 14.42/6.40  tff(c_1002, plain, (~v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_998])).
% 14.42/6.40  tff(c_8030, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7988, c_1002])).
% 14.42/6.40  tff(c_8035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7383, c_8030])).
% 14.42/6.40  tff(c_8036, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_7983])).
% 14.42/6.40  tff(c_8066, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8036, c_7383])).
% 14.42/6.40  tff(c_7425, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7402, c_7402, c_22])).
% 14.42/6.40  tff(c_8058, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8036, c_8036, c_7425])).
% 14.42/6.40  tff(c_291, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_139, c_277])).
% 14.42/6.40  tff(c_295, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_291])).
% 14.42/6.40  tff(c_8266, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8058, c_295])).
% 14.42/6.40  tff(c_8269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8066, c_8266])).
% 14.42/6.40  tff(c_8271, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_998])).
% 14.42/6.40  tff(c_8270, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_998])).
% 14.42/6.40  tff(c_8393, plain, (![A_559]: (A_559='#skF_5' | ~v1_xboole_0(A_559))), inference(resolution, [status(thm)], [c_8270, c_290])).
% 14.42/6.40  tff(c_8403, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_8271, c_8393])).
% 14.42/6.40  tff(c_8289, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8270, c_258])).
% 14.42/6.40  tff(c_8513, plain, (![A_562]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_562)))), inference(demodulation, [status(thm), theory('equality')], [c_8289, c_26])).
% 14.42/6.40  tff(c_46, plain, (![A_29, B_30, C_31]: (k1_relset_1(A_29, B_30, C_31)=k1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.42/6.40  tff(c_8521, plain, (![A_29, B_30]: (k1_relset_1(A_29, B_30, '#skF_5')=k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_8513, c_46])).
% 14.42/6.40  tff(c_8540, plain, (![A_29, B_30]: (k1_relset_1(A_29, B_30, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8403, c_8521])).
% 14.42/6.40  tff(c_8334, plain, (![A_14]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_8289, c_26])).
% 14.42/6.40  tff(c_60, plain, (![B_36, A_35, C_37]: (k1_xboole_0=B_36 | k1_relset_1(A_35, B_36, C_37)=A_35 | ~v1_funct_2(C_37, A_35, B_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.42/6.40  tff(c_8860, plain, (![B_590, A_591, C_592]: (B_590='#skF_5' | k1_relset_1(A_591, B_590, C_592)=A_591 | ~v1_funct_2(C_592, A_591, B_590) | ~m1_subset_1(C_592, k1_zfmisc_1(k2_zfmisc_1(A_591, B_590))))), inference(demodulation, [status(thm), theory('equality')], [c_8289, c_60])).
% 14.42/6.40  tff(c_8867, plain, (![B_590, A_591]: (B_590='#skF_5' | k1_relset_1(A_591, B_590, '#skF_5')=A_591 | ~v1_funct_2('#skF_5', A_591, B_590))), inference(resolution, [status(thm)], [c_8334, c_8860])).
% 14.42/6.40  tff(c_9028, plain, (![B_602, A_603]: (B_602='#skF_5' | A_603='#skF_5' | ~v1_funct_2('#skF_5', A_603, B_602))), inference(demodulation, [status(thm), theory('equality')], [c_8540, c_8867])).
% 14.42/6.40  tff(c_9069, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_82, c_9028])).
% 14.42/6.40  tff(c_9070, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_9069])).
% 14.42/6.40  tff(c_9104, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9070, c_8270])).
% 14.42/6.40  tff(c_9116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_431, c_9104])).
% 14.42/6.40  tff(c_9117, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_9069])).
% 14.42/6.40  tff(c_9152, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9117, c_8270])).
% 14.42/6.40  tff(c_8333, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8289, c_8289, c_22])).
% 14.42/6.40  tff(c_9145, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9117, c_9117, c_8333])).
% 14.42/6.40  tff(c_9318, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9145, c_295])).
% 14.42/6.40  tff(c_9321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9152, c_9318])).
% 14.42/6.40  tff(c_9323, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_426])).
% 14.42/6.40  tff(c_9346, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_9323, c_258])).
% 14.42/6.40  tff(c_9322, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_426])).
% 14.42/6.40  tff(c_9335, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_9322, c_258])).
% 14.42/6.40  tff(c_9375, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9346, c_9335])).
% 14.42/6.40  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.42/6.40  tff(c_9365, plain, (![B_13]: (k2_zfmisc_1('#skF_5', B_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9335, c_9335, c_24])).
% 14.42/6.40  tff(c_9457, plain, (![B_13]: (k2_zfmisc_1('#skF_3', B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9375, c_9375, c_9365])).
% 14.42/6.40  tff(c_9458, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9457, c_295])).
% 14.42/6.40  tff(c_9461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9323, c_9458])).
% 14.42/6.40  tff(c_9462, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_218])).
% 14.42/6.40  tff(c_9464, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9462, c_295])).
% 14.42/6.40  tff(c_9466, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_9462, c_80])).
% 14.42/6.40  tff(c_10471, plain, (![A_705, B_706, C_707]: (k2_relset_1(A_705, B_706, C_707)=k2_relat_1(C_707) | ~m1_subset_1(C_707, k1_zfmisc_1(k2_zfmisc_1(A_705, B_706))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.42/6.40  tff(c_10559, plain, (![C_714]: (k2_relset_1('#skF_3', '#skF_4', C_714)=k2_relat_1(C_714) | ~m1_subset_1(C_714, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_9462, c_10471])).
% 14.42/6.40  tff(c_10566, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_9466, c_10559])).
% 14.42/6.40  tff(c_10577, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_10566])).
% 14.42/6.40  tff(c_10049, plain, (![A_670, B_671, C_672]: (k1_relset_1(A_670, B_671, C_672)=k1_relat_1(C_672) | ~m1_subset_1(C_672, k1_zfmisc_1(k2_zfmisc_1(A_670, B_671))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.42/6.40  tff(c_10186, plain, (![C_680]: (k1_relset_1('#skF_3', '#skF_4', C_680)=k1_relat_1(C_680) | ~m1_subset_1(C_680, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_9462, c_10049])).
% 14.42/6.40  tff(c_10203, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_9466, c_10186])).
% 14.42/6.40  tff(c_12417, plain, (![B_828, C_829, A_830]: (k1_xboole_0=B_828 | v1_funct_2(C_829, A_830, B_828) | k1_relset_1(A_830, B_828, C_829)!=A_830 | ~m1_subset_1(C_829, k1_zfmisc_1(k2_zfmisc_1(A_830, B_828))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.42/6.40  tff(c_12436, plain, (![C_829]: (k1_xboole_0='#skF_4' | v1_funct_2(C_829, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', C_829)!='#skF_3' | ~m1_subset_1(C_829, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_9462, c_12417])).
% 14.42/6.40  tff(c_12511, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_12436])).
% 14.42/6.40  tff(c_9473, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_9462, c_20])).
% 14.42/6.40  tff(c_9524, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_9473])).
% 14.42/6.40  tff(c_12543, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12511, c_9524])).
% 14.42/6.40  tff(c_12552, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12511, c_12511, c_22])).
% 14.42/6.40  tff(c_11276, plain, (![B_776, C_777, A_778]: (k1_xboole_0=B_776 | v1_funct_2(C_777, A_778, B_776) | k1_relset_1(A_778, B_776, C_777)!=A_778 | ~m1_subset_1(C_777, k1_zfmisc_1(k2_zfmisc_1(A_778, B_776))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.42/6.40  tff(c_11295, plain, (![C_777]: (k1_xboole_0='#skF_4' | v1_funct_2(C_777, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', C_777)!='#skF_3' | ~m1_subset_1(C_777, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_9462, c_11276])).
% 14.42/6.40  tff(c_11405, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_11295])).
% 14.42/6.40  tff(c_11445, plain, (![A_14]: (r1_tarski('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_11405, c_140])).
% 14.42/6.40  tff(c_11448, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11405, c_11405, c_22])).
% 14.42/6.40  tff(c_10259, plain, (![A_687]: (m1_subset_1(A_687, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_687), k2_relat_1(A_687)))) | ~v1_funct_1(A_687) | ~v1_relat_1(A_687))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.42/6.40  tff(c_10284, plain, (![A_687]: (r1_tarski(A_687, k2_zfmisc_1(k1_relat_1(A_687), k2_relat_1(A_687))) | ~v1_funct_1(A_687) | ~v1_relat_1(A_687))), inference(resolution, [status(thm)], [c_10259, c_28])).
% 14.42/6.40  tff(c_10584, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10577, c_10284])).
% 14.42/6.40  tff(c_10594, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_84, c_10584])).
% 14.42/6.40  tff(c_10627, plain, (k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_10594, c_14])).
% 14.42/6.40  tff(c_11203, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_10627])).
% 14.42/6.40  tff(c_11601, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11448, c_11203])).
% 14.42/6.40  tff(c_11609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11445, c_11601])).
% 14.42/6.40  tff(c_11611, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_11295])).
% 14.42/6.40  tff(c_11724, plain, (![B_798, A_799, C_800]: (k1_xboole_0=B_798 | k1_relset_1(A_799, B_798, C_800)=A_799 | ~v1_funct_2(C_800, A_799, B_798) | ~m1_subset_1(C_800, k1_zfmisc_1(k2_zfmisc_1(A_799, B_798))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.42/6.40  tff(c_11747, plain, (![C_800]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_800)='#skF_3' | ~v1_funct_2(C_800, '#skF_3', '#skF_4') | ~m1_subset_1(C_800, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_9462, c_11724])).
% 14.42/6.40  tff(c_12261, plain, (![C_823]: (k1_relset_1('#skF_3', '#skF_4', C_823)='#skF_3' | ~v1_funct_2(C_823, '#skF_3', '#skF_4') | ~m1_subset_1(C_823, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_11611, c_11747])).
% 14.42/6.40  tff(c_12276, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_9466, c_12261])).
% 14.42/6.40  tff(c_12290, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_10203, c_12276])).
% 14.42/6.40  tff(c_12295, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12290, c_11203])).
% 14.42/6.40  tff(c_12308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_9462, c_12295])).
% 14.42/6.40  tff(c_12309, plain, (k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_10627])).
% 14.42/6.40  tff(c_12702, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12552, c_12309])).
% 14.42/6.40  tff(c_12705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12543, c_12702])).
% 14.42/6.40  tff(c_12707, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_12436])).
% 14.42/6.40  tff(c_12851, plain, (![B_848, A_849, C_850]: (k1_xboole_0=B_848 | k1_relset_1(A_849, B_848, C_850)=A_849 | ~v1_funct_2(C_850, A_849, B_848) | ~m1_subset_1(C_850, k1_zfmisc_1(k2_zfmisc_1(A_849, B_848))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.42/6.40  tff(c_12870, plain, (![C_850]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_850)='#skF_3' | ~v1_funct_2(C_850, '#skF_3', '#skF_4') | ~m1_subset_1(C_850, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_9462, c_12851])).
% 14.42/6.40  tff(c_13656, plain, (![C_886]: (k1_relset_1('#skF_3', '#skF_4', C_886)='#skF_3' | ~v1_funct_2(C_886, '#skF_3', '#skF_4') | ~m1_subset_1(C_886, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_12707, c_12870])).
% 14.42/6.40  tff(c_13671, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_9466, c_13656])).
% 14.42/6.40  tff(c_13685, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_10203, c_13671])).
% 14.42/6.40  tff(c_9868, plain, (![A_661]: (k2_relat_1(k2_funct_1(A_661))=k1_relat_1(A_661) | ~v2_funct_1(A_661) | ~v1_funct_1(A_661) | ~v1_relat_1(A_661))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.42/6.40  tff(c_15626, plain, (![A_978]: (v1_funct_2(k2_funct_1(A_978), k1_relat_1(k2_funct_1(A_978)), k1_relat_1(A_978)) | ~v1_funct_1(k2_funct_1(A_978)) | ~v1_relat_1(k2_funct_1(A_978)) | ~v2_funct_1(A_978) | ~v1_funct_1(A_978) | ~v1_relat_1(A_978))), inference(superposition, [status(thm), theory('equality')], [c_9868, c_64])).
% 14.42/6.40  tff(c_15629, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13685, c_15626])).
% 14.42/6.40  tff(c_15640, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_84, c_78, c_210, c_15629])).
% 14.42/6.40  tff(c_15643, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_15640])).
% 14.42/6.40  tff(c_15646, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_15643])).
% 14.42/6.40  tff(c_15650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_324, c_84, c_15646])).
% 14.42/6.40  tff(c_15652, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_15640])).
% 14.42/6.40  tff(c_16197, plain, (![A_1005]: (m1_subset_1(k2_funct_1(A_1005), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1005)), k1_relat_1(A_1005)))) | ~v1_funct_1(k2_funct_1(A_1005)) | ~v1_relat_1(k2_funct_1(A_1005)) | ~v2_funct_1(A_1005) | ~v1_funct_1(A_1005) | ~v1_relat_1(A_1005))), inference(superposition, [status(thm), theory('equality')], [c_38, c_10259])).
% 14.42/6.40  tff(c_16223, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13685, c_16197])).
% 14.42/6.40  tff(c_16242, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_84, c_78, c_15652, c_210, c_16223])).
% 14.42/6.40  tff(c_16270, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_16242])).
% 14.42/6.40  tff(c_16286, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_84, c_78, c_10577, c_16270])).
% 14.42/6.40  tff(c_16288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_16286])).
% 14.42/6.40  tff(c_16290, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_9473])).
% 14.42/6.40  tff(c_16303, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16290, c_12])).
% 14.42/6.40  tff(c_16306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9464, c_16303])).
% 14.42/6.40  tff(c_16307, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_291])).
% 14.42/6.40  tff(c_16308, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_291])).
% 14.42/6.40  tff(c_16324, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16307, c_16308])).
% 14.42/6.40  tff(c_16328, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_16324, c_258])).
% 14.42/6.40  tff(c_16315, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_16307, c_20])).
% 14.42/6.40  tff(c_16472, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16328, c_16328, c_16328, c_16315])).
% 14.42/6.40  tff(c_16473, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_16472])).
% 14.42/6.40  tff(c_16335, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16328, c_16328, c_22])).
% 14.42/6.40  tff(c_16480, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16473, c_16473, c_16335])).
% 14.42/6.40  tff(c_16489, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16473, c_224])).
% 14.42/6.40  tff(c_16644, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16480, c_16489])).
% 14.42/6.40  tff(c_16392, plain, (![A_1013]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_1013)))), inference(demodulation, [status(thm), theory('equality')], [c_16328, c_26])).
% 14.42/6.40  tff(c_42, plain, (![C_24, A_22, B_23]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.42/6.40  tff(c_16400, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16392, c_42])).
% 14.42/6.40  tff(c_16478, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16473, c_16400])).
% 14.42/6.40  tff(c_16494, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16473, c_84])).
% 14.42/6.40  tff(c_16493, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16473, c_78])).
% 14.42/6.40  tff(c_16336, plain, (![A_14]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_16328, c_26])).
% 14.42/6.40  tff(c_16479, plain, (![A_14]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_16473, c_16336])).
% 14.42/6.40  tff(c_16986, plain, (![A_1084, B_1085, C_1086]: (k1_relset_1(A_1084, B_1085, C_1086)=k1_relat_1(C_1086) | ~m1_subset_1(C_1086, k1_zfmisc_1(k2_zfmisc_1(A_1084, B_1085))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.42/6.40  tff(c_17004, plain, (![A_1084, B_1085]: (k1_relset_1(A_1084, B_1085, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_16479, c_16986])).
% 14.42/6.40  tff(c_16492, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16473, c_82])).
% 14.42/6.40  tff(c_16484, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16473, c_16328])).
% 14.42/6.40  tff(c_58, plain, (![B_36, C_37]: (k1_relset_1(k1_xboole_0, B_36, C_37)=k1_xboole_0 | ~v1_funct_2(C_37, k1_xboole_0, B_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.42/6.40  tff(c_87, plain, (![B_36, C_37]: (k1_relset_1(k1_xboole_0, B_36, C_37)=k1_xboole_0 | ~v1_funct_2(C_37, k1_xboole_0, B_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_58])).
% 14.42/6.40  tff(c_21478, plain, (![B_1349, C_1350]: (k1_relset_1('#skF_3', B_1349, C_1350)='#skF_3' | ~v1_funct_2(C_1350, '#skF_3', B_1349) | ~m1_subset_1(C_1350, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16484, c_16484, c_16484, c_16484, c_87])).
% 14.42/6.40  tff(c_21483, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_16492, c_21478])).
% 14.42/6.40  tff(c_21490, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16479, c_17004, c_21483])).
% 14.42/6.40  tff(c_16490, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16473, c_210])).
% 14.42/6.40  tff(c_16732, plain, (![A_1049]: (k2_relat_1(k2_funct_1(A_1049))=k1_relat_1(A_1049) | ~v2_funct_1(A_1049) | ~v1_funct_1(A_1049) | ~v1_relat_1(A_1049))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.42/6.40  tff(c_26368, plain, (![A_1562]: (v1_funct_2(k2_funct_1(A_1562), k1_relat_1(k2_funct_1(A_1562)), k1_relat_1(A_1562)) | ~v1_funct_1(k2_funct_1(A_1562)) | ~v1_relat_1(k2_funct_1(A_1562)) | ~v2_funct_1(A_1562) | ~v1_funct_1(A_1562) | ~v1_relat_1(A_1562))), inference(superposition, [status(thm), theory('equality')], [c_16732, c_64])).
% 14.42/6.40  tff(c_26377, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21490, c_26368])).
% 14.42/6.40  tff(c_26389, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16478, c_16494, c_16493, c_16490, c_26377])).
% 14.42/6.40  tff(c_26390, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_26389])).
% 14.42/6.40  tff(c_26393, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_26390])).
% 14.42/6.40  tff(c_26397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16478, c_16494, c_26393])).
% 14.42/6.40  tff(c_26399, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_26389])).
% 14.42/6.40  tff(c_16858, plain, (![A_1067, B_1068, C_1069]: (k2_relset_1(A_1067, B_1068, C_1069)=k2_relat_1(C_1069) | ~m1_subset_1(C_1069, k1_zfmisc_1(k2_zfmisc_1(A_1067, B_1068))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.42/6.40  tff(c_16883, plain, (![A_1072, B_1073]: (k2_relset_1(A_1072, B_1073, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_16479, c_16858])).
% 14.42/6.40  tff(c_16491, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16473, c_76])).
% 14.42/6.40  tff(c_16887, plain, (k2_relat_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_16883, c_16491])).
% 14.42/6.40  tff(c_21371, plain, (![A_1346]: (m1_subset_1(A_1346, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1346), k2_relat_1(A_1346)))) | ~v1_funct_1(A_1346) | ~v1_relat_1(A_1346))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.42/6.40  tff(c_26967, plain, (![A_1588]: (m1_subset_1(k2_funct_1(A_1588), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1588), k2_relat_1(k2_funct_1(A_1588))))) | ~v1_funct_1(k2_funct_1(A_1588)) | ~v1_relat_1(k2_funct_1(A_1588)) | ~v2_funct_1(A_1588) | ~v1_funct_1(A_1588) | ~v1_relat_1(A_1588))), inference(superposition, [status(thm), theory('equality')], [c_40, c_21371])).
% 14.42/6.40  tff(c_26999, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16887, c_26967])).
% 14.42/6.40  tff(c_27019, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_16478, c_16494, c_16493, c_26399, c_16490, c_26999])).
% 14.42/6.40  tff(c_27045, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_27019])).
% 14.42/6.40  tff(c_27061, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16478, c_16494, c_16493, c_16480, c_21490, c_27045])).
% 14.42/6.40  tff(c_27063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16644, c_27061])).
% 14.42/6.40  tff(c_27064, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_16472])).
% 14.42/6.40  tff(c_16334, plain, (![B_13]: (k2_zfmisc_1('#skF_5', B_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16328, c_16328, c_24])).
% 14.42/6.40  tff(c_27073, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27064, c_27064, c_16334])).
% 14.42/6.40  tff(c_27081, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_27064, c_224])).
% 14.42/6.40  tff(c_27232, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_27073, c_27081])).
% 14.42/6.40  tff(c_27070, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27064, c_16400])).
% 14.42/6.40  tff(c_27086, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27064, c_84])).
% 14.42/6.40  tff(c_27085, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27064, c_78])).
% 14.42/6.40  tff(c_27082, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_27064, c_210])).
% 14.42/6.40  tff(c_27071, plain, (![A_14]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_27064, c_16336])).
% 14.42/6.40  tff(c_32957, plain, (![A_1972, B_1973, C_1974]: (k2_relset_1(A_1972, B_1973, C_1974)=k2_relat_1(C_1974) | ~m1_subset_1(C_1974, k1_zfmisc_1(k2_zfmisc_1(A_1972, B_1973))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.42/6.40  tff(c_32986, plain, (![A_1975, B_1976]: (k2_relset_1(A_1975, B_1976, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_27071, c_32957])).
% 14.42/6.40  tff(c_27083, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27064, c_76])).
% 14.42/6.40  tff(c_32990, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_32986, c_27083])).
% 14.42/6.40  tff(c_27338, plain, (![A_1619]: (k1_relat_1(k2_funct_1(A_1619))=k2_relat_1(A_1619) | ~v2_funct_1(A_1619) | ~v1_funct_1(A_1619) | ~v1_relat_1(A_1619))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.42/6.40  tff(c_37599, plain, (![A_2168]: (v1_funct_2(k2_funct_1(A_2168), k2_relat_1(A_2168), k2_relat_1(k2_funct_1(A_2168))) | ~v1_funct_1(k2_funct_1(A_2168)) | ~v1_relat_1(k2_funct_1(A_2168)) | ~v2_funct_1(A_2168) | ~v1_funct_1(A_2168) | ~v1_relat_1(A_2168))), inference(superposition, [status(thm), theory('equality')], [c_27338, c_64])).
% 14.42/6.40  tff(c_37608, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32990, c_37599])).
% 14.42/6.40  tff(c_37620, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_27070, c_27086, c_27085, c_27082, c_37608])).
% 14.42/6.40  tff(c_37621, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_37620])).
% 14.42/6.40  tff(c_37624, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_37621])).
% 14.42/6.40  tff(c_37628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27070, c_27086, c_37624])).
% 14.42/6.40  tff(c_37630, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_37620])).
% 14.42/6.40  tff(c_27515, plain, (![A_1641]: (m1_subset_1(A_1641, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1641), k2_relat_1(A_1641)))) | ~v1_funct_1(A_1641) | ~v1_relat_1(A_1641))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.42/6.40  tff(c_38396, plain, (![A_2196]: (m1_subset_1(k2_funct_1(A_2196), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_2196), k2_relat_1(k2_funct_1(A_2196))))) | ~v1_funct_1(k2_funct_1(A_2196)) | ~v1_relat_1(k2_funct_1(A_2196)) | ~v2_funct_1(A_2196) | ~v1_funct_1(A_2196) | ~v1_relat_1(A_2196))), inference(superposition, [status(thm), theory('equality')], [c_40, c_27515])).
% 14.42/6.40  tff(c_38428, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32990, c_38396])).
% 14.42/6.40  tff(c_38448, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_27070, c_27086, c_27085, c_37630, c_27082, c_27073, c_38428])).
% 14.42/6.40  tff(c_38450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27232, c_38448])).
% 14.42/6.40  tff(c_38451, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_209])).
% 14.42/6.40  tff(c_38452, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_209])).
% 14.42/6.40  tff(c_40706, plain, (![A_2384, B_2385, C_2386]: (k1_relset_1(A_2384, B_2385, C_2386)=k1_relat_1(C_2386) | ~m1_subset_1(C_2386, k1_zfmisc_1(k2_zfmisc_1(A_2384, B_2385))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.42/6.40  tff(c_40736, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_38452, c_40706])).
% 14.42/6.40  tff(c_41577, plain, (![B_2461, C_2462, A_2463]: (k1_xboole_0=B_2461 | v1_funct_2(C_2462, A_2463, B_2461) | k1_relset_1(A_2463, B_2461, C_2462)!=A_2463 | ~m1_subset_1(C_2462, k1_zfmisc_1(k2_zfmisc_1(A_2463, B_2461))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.42/6.40  tff(c_41596, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_38452, c_41577])).
% 14.42/6.40  tff(c_41620, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40736, c_41596])).
% 14.42/6.40  tff(c_41621, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_38451, c_41620])).
% 14.42/6.40  tff(c_41635, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_41621])).
% 14.42/6.40  tff(c_41638, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_41635])).
% 14.42/6.40  tff(c_41641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38557, c_84, c_78, c_40603, c_41638])).
% 14.42/6.40  tff(c_41642, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_41621])).
% 14.42/6.40  tff(c_41686, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41642, c_12])).
% 14.42/6.40  tff(c_41688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40219, c_41686])).
% 14.42/6.40  tff(c_41690, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_40214])).
% 14.42/6.40  tff(c_38474, plain, (![A_2198, B_2199]: (r2_hidden('#skF_2'(A_2198, B_2199), A_2198) | r1_tarski(A_2198, B_2199))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.42/6.40  tff(c_38479, plain, (![A_2200, B_2201]: (~v1_xboole_0(A_2200) | r1_tarski(A_2200, B_2201))), inference(resolution, [status(thm)], [c_38474, c_2])).
% 14.42/6.40  tff(c_38490, plain, (![A_2200]: (k1_xboole_0=A_2200 | ~v1_xboole_0(A_2200))), inference(resolution, [status(thm)], [c_38479, c_219])).
% 14.42/6.40  tff(c_41713, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_41690, c_38490])).
% 14.42/6.40  tff(c_41689, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_40214])).
% 14.42/6.40  tff(c_41702, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_41689, c_38490])).
% 14.42/6.40  tff(c_41733, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_41713, c_41702])).
% 14.42/6.40  tff(c_41724, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_41702, c_41702, c_22])).
% 14.42/6.40  tff(c_41779, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41733, c_41733, c_41724])).
% 14.42/6.40  tff(c_38469, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_38452, c_28])).
% 14.42/6.40  tff(c_38509, plain, (![B_2205, A_2206]: (B_2205=A_2206 | ~r1_tarski(B_2205, A_2206) | ~v1_xboole_0(A_2206))), inference(resolution, [status(thm)], [c_38479, c_14])).
% 14.42/6.40  tff(c_38526, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k2_funct_1('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_38469, c_38509])).
% 14.42/6.40  tff(c_38535, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_38526])).
% 14.42/6.40  tff(c_41780, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41779, c_38535])).
% 14.42/6.40  tff(c_41783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41690, c_41780])).
% 14.42/6.40  tff(c_41785, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_38526])).
% 14.42/6.40  tff(c_41816, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_41785, c_38490])).
% 14.42/6.40  tff(c_41829, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_41816, c_20])).
% 14.42/6.40  tff(c_41876, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_41829])).
% 14.42/6.40  tff(c_41890, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41876, c_12])).
% 14.42/6.40  tff(c_41888, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41876, c_41876, c_22])).
% 14.42/6.40  tff(c_38470, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_218])).
% 14.42/6.40  tff(c_38489, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_38479, c_38470])).
% 14.42/6.40  tff(c_41927, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41888, c_38489])).
% 14.42/6.40  tff(c_41933, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41890, c_41927])).
% 14.42/6.40  tff(c_41934, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_41829])).
% 14.42/6.40  tff(c_41950, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41934, c_12])).
% 14.42/6.40  tff(c_41947, plain, (![B_13]: (k2_zfmisc_1('#skF_3', B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41934, c_41934, c_24])).
% 14.42/6.40  tff(c_42010, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41947, c_38489])).
% 14.42/6.40  tff(c_42016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41950, c_42010])).
% 14.42/6.40  tff(c_42017, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_218])).
% 14.42/6.40  tff(c_42276, plain, (![C_2518, A_2519, B_2520]: (v1_xboole_0(C_2518) | ~m1_subset_1(C_2518, k1_zfmisc_1(k2_zfmisc_1(A_2519, B_2520))) | ~v1_xboole_0(A_2519))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.42/6.40  tff(c_42279, plain, (![C_2518]: (v1_xboole_0(C_2518) | ~m1_subset_1(C_2518, k1_zfmisc_1('#skF_5')) | ~v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42017, c_42276])).
% 14.42/6.40  tff(c_42395, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_42279])).
% 14.42/6.40  tff(c_42020, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42017, c_80])).
% 14.42/6.40  tff(c_42092, plain, (![C_2492, A_2493, B_2494]: (v1_relat_1(C_2492) | ~m1_subset_1(C_2492, k1_zfmisc_1(k2_zfmisc_1(A_2493, B_2494))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.42/6.40  tff(c_42125, plain, (![C_2496]: (v1_relat_1(C_2496) | ~m1_subset_1(C_2496, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_42017, c_42092])).
% 14.42/6.40  tff(c_42137, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42020, c_42125])).
% 14.42/6.40  tff(c_43606, plain, (![A_2612, B_2613, C_2614]: (k2_relset_1(A_2612, B_2613, C_2614)=k2_relat_1(C_2614) | ~m1_subset_1(C_2614, k1_zfmisc_1(k2_zfmisc_1(A_2612, B_2613))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.42/6.40  tff(c_43886, plain, (![C_2628]: (k2_relset_1('#skF_3', '#skF_4', C_2628)=k2_relat_1(C_2628) | ~m1_subset_1(C_2628, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_42017, c_43606])).
% 14.42/6.40  tff(c_43893, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42020, c_43886])).
% 14.42/6.40  tff(c_43904, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_43893])).
% 14.42/6.40  tff(c_43711, plain, (![A_2620, B_2621, C_2622]: (k1_relset_1(A_2620, B_2621, C_2622)=k1_relat_1(C_2622) | ~m1_subset_1(C_2622, k1_zfmisc_1(k2_zfmisc_1(A_2620, B_2621))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.42/6.40  tff(c_43741, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_38452, c_43711])).
% 14.42/6.40  tff(c_44737, plain, (![B_2712, C_2713, A_2714]: (k1_xboole_0=B_2712 | v1_funct_2(C_2713, A_2714, B_2712) | k1_relset_1(A_2714, B_2712, C_2713)!=A_2714 | ~m1_subset_1(C_2713, k1_zfmisc_1(k2_zfmisc_1(A_2714, B_2712))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.42/6.40  tff(c_44759, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_38452, c_44737])).
% 14.42/6.40  tff(c_44782, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_43741, c_44759])).
% 14.42/6.40  tff(c_44783, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_38451, c_44782])).
% 14.42/6.40  tff(c_44790, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_44783])).
% 14.42/6.40  tff(c_44793, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_44790])).
% 14.42/6.40  tff(c_44796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42137, c_84, c_78, c_43904, c_44793])).
% 14.42/6.40  tff(c_44797, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_44783])).
% 14.42/6.40  tff(c_44842, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44797, c_12])).
% 14.42/6.40  tff(c_44844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42395, c_44842])).
% 14.42/6.40  tff(c_44846, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_42279])).
% 14.42/6.40  tff(c_42031, plain, (![A_2481, B_2482]: (r2_hidden('#skF_2'(A_2481, B_2482), A_2481) | r1_tarski(A_2481, B_2482))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.42/6.40  tff(c_42036, plain, (![A_2483, B_2484]: (~v1_xboole_0(A_2483) | r1_tarski(A_2483, B_2484))), inference(resolution, [status(thm)], [c_42031, c_2])).
% 14.42/6.40  tff(c_42043, plain, (![A_2483]: (k1_xboole_0=A_2483 | ~v1_xboole_0(A_2483))), inference(resolution, [status(thm)], [c_42036, c_219])).
% 14.42/6.40  tff(c_44858, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_44846, c_42043])).
% 14.42/6.40  tff(c_42077, plain, (![B_2490, A_2491]: (k1_xboole_0=B_2490 | k1_xboole_0=A_2491 | k2_zfmisc_1(A_2491, B_2490)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.42/6.40  tff(c_42080, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_42017, c_42077])).
% 14.42/6.40  tff(c_42091, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_42080])).
% 14.42/6.40  tff(c_44865, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44858, c_42091])).
% 14.42/6.40  tff(c_44871, plain, (![B_13]: (k2_zfmisc_1('#skF_3', B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44858, c_44858, c_24])).
% 14.42/6.40  tff(c_44918, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44871, c_42017])).
% 14.42/6.40  tff(c_44920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44865, c_44918])).
% 14.42/6.40  tff(c_44922, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_42080])).
% 14.42/6.40  tff(c_44921, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_42080])).
% 14.42/6.40  tff(c_45156, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44922, c_44922, c_44921])).
% 14.42/6.40  tff(c_45157, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_45156])).
% 14.42/6.40  tff(c_44930, plain, (![A_14]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_44922, c_26])).
% 14.42/6.40  tff(c_45209, plain, (![A_2745]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_2745)))), inference(demodulation, [status(thm), theory('equality')], [c_45157, c_44930])).
% 14.42/6.40  tff(c_45217, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_45209, c_42])).
% 14.42/6.40  tff(c_45171, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45157, c_84])).
% 14.42/6.40  tff(c_45170, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45157, c_78])).
% 14.42/6.40  tff(c_44928, plain, (![B_13]: (k2_zfmisc_1('#skF_5', B_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44922, c_44922, c_24])).
% 14.42/6.40  tff(c_45198, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45157, c_45157, c_44928])).
% 14.42/6.40  tff(c_44948, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44922, c_44922, c_44921])).
% 14.42/6.40  tff(c_44949, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_44948])).
% 14.42/6.40  tff(c_44931, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44922, c_12])).
% 14.42/6.40  tff(c_44951, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44949, c_44931])).
% 14.42/6.40  tff(c_44996, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44949, c_44949, c_44928])).
% 14.42/6.40  tff(c_42055, plain, (![B_2486, A_2487]: (B_2486=A_2487 | ~r1_tarski(B_2486, A_2487) | ~v1_xboole_0(A_2487))), inference(resolution, [status(thm)], [c_42036, c_14])).
% 14.42/6.40  tff(c_42068, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k2_funct_1('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_38469, c_42055])).
% 14.42/6.40  tff(c_44939, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_42068])).
% 14.42/6.40  tff(c_45043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44951, c_44996, c_44939])).
% 14.42/6.40  tff(c_45044, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_44948])).
% 14.42/6.40  tff(c_45047, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45044, c_44931])).
% 14.42/6.40  tff(c_44929, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44922, c_44922, c_22])).
% 14.42/6.40  tff(c_45107, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45044, c_45044, c_44929])).
% 14.42/6.40  tff(c_45133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45047, c_45107, c_44939])).
% 14.42/6.40  tff(c_45134, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_42068])).
% 14.42/6.40  tff(c_45261, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_45198, c_45157, c_45134])).
% 14.42/6.40  tff(c_45508, plain, (![A_2781]: (k1_relat_1(k2_funct_1(A_2781))=k2_relat_1(A_2781) | ~v2_funct_1(A_2781) | ~v1_funct_1(A_2781) | ~v1_relat_1(A_2781))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.42/6.40  tff(c_45520, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_45261, c_45508])).
% 14.42/6.40  tff(c_45524, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45217, c_45171, c_45170, c_45520])).
% 14.42/6.40  tff(c_45208, plain, (![A_14]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_45157, c_44930])).
% 14.42/6.40  tff(c_46516, plain, (![A_2868, B_2869, C_2870]: (k2_relset_1(A_2868, B_2869, C_2870)=k2_relat_1(C_2870) | ~m1_subset_1(C_2870, k1_zfmisc_1(k2_zfmisc_1(A_2868, B_2869))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.42/6.40  tff(c_46530, plain, (![A_2868, B_2869]: (k2_relset_1(A_2868, B_2869, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_45208, c_46516])).
% 14.42/6.40  tff(c_46542, plain, (![A_2871, B_2872]: (k2_relset_1(A_2871, B_2872, '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_45524, c_46530])).
% 14.42/6.40  tff(c_45168, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_45157, c_76])).
% 14.42/6.40  tff(c_46546, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_46542, c_45168])).
% 14.42/6.40  tff(c_46790, plain, (![A_2891, B_2892, C_2893]: (k1_relset_1(A_2891, B_2892, C_2893)=k1_relat_1(C_2893) | ~m1_subset_1(C_2893, k1_zfmisc_1(k2_zfmisc_1(A_2891, B_2892))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.42/6.40  tff(c_46807, plain, (![A_2891, B_2892]: (k1_relset_1(A_2891, B_2892, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_45208, c_46790])).
% 14.42/6.40  tff(c_46818, plain, (![A_2891, B_2892]: (k1_relset_1(A_2891, B_2892, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46546, c_46807])).
% 14.42/6.40  tff(c_45161, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_45157, c_44922])).
% 14.42/6.40  tff(c_54, plain, (![C_37, B_36]: (v1_funct_2(C_37, k1_xboole_0, B_36) | k1_relset_1(k1_xboole_0, B_36, C_37)!=k1_xboole_0 | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.42/6.40  tff(c_88, plain, (![C_37, B_36]: (v1_funct_2(C_37, k1_xboole_0, B_36) | k1_relset_1(k1_xboole_0, B_36, C_37)!=k1_xboole_0 | ~m1_subset_1(C_37, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_54])).
% 14.42/6.40  tff(c_47026, plain, (![C_2909, B_2910]: (v1_funct_2(C_2909, '#skF_4', B_2910) | k1_relset_1('#skF_4', B_2910, C_2909)!='#skF_4' | ~m1_subset_1(C_2909, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_45161, c_45161, c_45161, c_45161, c_88])).
% 14.42/6.40  tff(c_47032, plain, (![B_2910]: (v1_funct_2('#skF_4', '#skF_4', B_2910) | k1_relset_1('#skF_4', B_2910, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_45208, c_47026])).
% 14.42/6.40  tff(c_47039, plain, (![B_2910]: (v1_funct_2('#skF_4', '#skF_4', B_2910))), inference(demodulation, [status(thm), theory('equality')], [c_46818, c_47032])).
% 14.42/6.40  tff(c_45166, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45157, c_38451])).
% 14.42/6.40  tff(c_45299, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45261, c_45166])).
% 14.42/6.40  tff(c_47044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47039, c_45299])).
% 14.42/6.40  tff(c_47045, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_45156])).
% 14.42/6.40  tff(c_47046, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_45156])).
% 14.42/6.40  tff(c_47065, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47045, c_47046])).
% 14.42/6.40  tff(c_50, plain, (![A_35]: (v1_funct_2(k1_xboole_0, A_35, k1_xboole_0) | k1_xboole_0=A_35 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_35, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.42/6.40  tff(c_86, plain, (![A_35]: (v1_funct_2(k1_xboole_0, A_35, k1_xboole_0) | k1_xboole_0=A_35)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_50])).
% 14.42/6.40  tff(c_44927, plain, (![A_35]: (v1_funct_2('#skF_5', A_35, '#skF_5') | A_35='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44922, c_44922, c_44922, c_86])).
% 14.42/6.40  tff(c_47238, plain, (![A_2928]: (v1_funct_2('#skF_3', A_2928, '#skF_3') | A_2928='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47045, c_47045, c_47045, c_44927])).
% 14.42/6.40  tff(c_47110, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47045, c_47045, c_44929])).
% 14.42/6.40  tff(c_47170, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_47110, c_47045, c_45134])).
% 14.42/6.40  tff(c_47055, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47045, c_38451])).
% 14.42/6.40  tff(c_47171, plain, (~v1_funct_2('#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47170, c_47055])).
% 14.42/6.40  tff(c_47241, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_47238, c_47171])).
% 14.42/6.40  tff(c_47245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47065, c_47241])).
% 14.42/6.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.42/6.40  
% 14.42/6.40  Inference rules
% 14.42/6.40  ----------------------
% 14.42/6.41  #Ref     : 0
% 14.42/6.41  #Sup     : 10794
% 14.42/6.41  #Fact    : 0
% 14.42/6.41  #Define  : 0
% 14.42/6.41  #Split   : 90
% 14.42/6.41  #Chain   : 0
% 14.42/6.41  #Close   : 0
% 14.42/6.41  
% 14.42/6.41  Ordering : KBO
% 14.42/6.41  
% 14.42/6.41  Simplification rules
% 14.42/6.41  ----------------------
% 14.42/6.41  #Subsume      : 2845
% 14.42/6.41  #Demod        : 7343
% 14.42/6.41  #Tautology    : 3496
% 14.42/6.41  #SimpNegUnit  : 222
% 14.42/6.41  #BackRed      : 1094
% 14.42/6.41  
% 14.42/6.41  #Partial instantiations: 0
% 14.42/6.41  #Strategies tried      : 1
% 14.42/6.41  
% 14.42/6.41  Timing (in seconds)
% 14.42/6.41  ----------------------
% 14.42/6.41  Preprocessing        : 0.36
% 14.42/6.41  Parsing              : 0.19
% 14.42/6.41  CNF conversion       : 0.03
% 14.42/6.41  Main loop            : 5.19
% 14.42/6.41  Inferencing          : 1.46
% 14.42/6.41  Reduction            : 1.63
% 14.42/6.41  Demodulation         : 1.12
% 14.42/6.41  BG Simplification    : 0.14
% 14.42/6.41  Subsumption          : 1.54
% 14.42/6.41  Abstraction          : 0.21
% 14.42/6.41  MUC search           : 0.00
% 14.42/6.41  Cooper               : 0.00
% 14.42/6.41  Total                : 5.69
% 14.42/6.41  Index Insertion      : 0.00
% 14.42/6.41  Index Deletion       : 0.00
% 14.42/6.41  Index Matching       : 0.00
% 14.42/6.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
