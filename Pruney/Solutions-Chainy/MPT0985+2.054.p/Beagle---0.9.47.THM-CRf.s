%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:34 EST 2020

% Result     : Theorem 18.58s
% Output     : CNFRefutation 18.79s
% Verified   : 
% Statistics : Number of formulae       :  235 ( 967 expanded)
%              Number of leaves         :   59 ( 339 expanded)
%              Depth                    :   13
%              Number of atoms          :  391 (2539 expanded)
%              Number of equality atoms :  129 ( 668 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_270,negated_conjecture,(
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

tff(f_204,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_198,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_131,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_208,axiom,(
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

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_123,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_234,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_253,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(B,C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_224,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_111,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_135,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_222,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_218,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_118,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_122,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_25311,plain,(
    ! [C_1113,A_1114,B_1115] :
      ( v4_relat_1(C_1113,A_1114)
      | ~ m1_subset_1(C_1113,k1_zfmisc_1(k2_zfmisc_1(A_1114,B_1115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_25337,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_122,c_25311])).

tff(c_24761,plain,(
    ! [C_1047,A_1048,B_1049] :
      ( v1_relat_1(C_1047)
      | ~ m1_subset_1(C_1047,k1_zfmisc_1(k2_zfmisc_1(A_1048,B_1049))) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_24788,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_24761])).

tff(c_42,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24797,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24788,c_42])).

tff(c_24817,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24797])).

tff(c_126,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_370,plain,(
    ! [A_85] :
      ( v1_funct_1(k2_funct_1(A_85))
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_116,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_277,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_373,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_370,c_277])).

tff(c_376,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_373])).

tff(c_756,plain,(
    ! [C_110,A_111,B_112] :
      ( v1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_769,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_756])).

tff(c_782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_769])).

tff(c_784,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_25781,plain,(
    ! [A_1150,B_1151,C_1152] :
      ( k2_relset_1(A_1150,B_1151,C_1152) = k2_relat_1(C_1152)
      | ~ m1_subset_1(C_1152,k1_zfmisc_1(k2_zfmisc_1(A_1150,B_1151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_25797,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_25781])).

tff(c_25810,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_25797])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_134,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_24270,plain,(
    ! [C_1014,B_1015,A_1016] :
      ( ~ v1_xboole_0(C_1014)
      | ~ m1_subset_1(B_1015,k1_zfmisc_1(C_1014))
      | ~ r2_hidden(A_1016,B_1015) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24286,plain,(
    ! [A_1017,A_1018] :
      ( ~ v1_xboole_0(A_1017)
      | ~ r2_hidden(A_1018,A_1017) ) ),
    inference(resolution,[status(thm)],[c_134,c_24270])).

tff(c_24291,plain,(
    ! [A_1019,B_1020] :
      ( ~ v1_xboole_0(A_1019)
      | r1_tarski(A_1019,B_1020) ) ),
    inference(resolution,[status(thm)],[c_6,c_24286])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_783,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_865,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_783])).

tff(c_991,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_865])).

tff(c_24300,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24291,c_991])).

tff(c_1064,plain,(
    ! [C_138,A_139,B_140] :
      ( v1_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1087,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_1064])).

tff(c_120,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_24362,plain,(
    ! [A_1026] :
      ( k4_relat_1(A_1026) = k2_funct_1(A_1026)
      | ~ v2_funct_1(A_1026)
      | ~ v1_funct_1(A_1026)
      | ~ v1_relat_1(A_1026) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_24365,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_24362])).

tff(c_24368,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_126,c_24365])).

tff(c_26,plain,(
    ! [A_16] :
      ( v1_relat_1(k4_relat_1(A_16))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24378,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_24368,c_26])).

tff(c_24386,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_24378])).

tff(c_1569,plain,(
    ! [C_176,A_177,B_178] :
      ( v4_relat_1(C_176,A_177)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1591,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_122,c_1569])).

tff(c_1100,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1087,c_42])).

tff(c_1115,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1100])).

tff(c_1731,plain,(
    ! [A_200] :
      ( k4_relat_1(A_200) = k2_funct_1(A_200)
      | ~ v2_funct_1(A_200)
      | ~ v1_funct_1(A_200)
      | ~ v1_relat_1(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1734,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_1731])).

tff(c_1737,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_126,c_1734])).

tff(c_1747,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1737,c_26])).

tff(c_1755,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_1747])).

tff(c_36,plain,(
    ! [A_22] :
      ( k2_relat_1(k4_relat_1(A_22)) = k1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1741,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1737,c_36])).

tff(c_1751,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_1741])).

tff(c_2358,plain,(
    ! [A_248,B_249,C_250] :
      ( k2_relset_1(A_248,B_249,C_250) = k2_relat_1(C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_2374,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_2358])).

tff(c_2386,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2374])).

tff(c_38,plain,(
    ! [A_22] :
      ( k1_relat_1(k4_relat_1(A_22)) = k2_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1744,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1737,c_38])).

tff(c_1753,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_1744])).

tff(c_2392,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2386,c_1753])).

tff(c_100,plain,(
    ! [A_57] :
      ( v1_funct_2(A_57,k1_relat_1(A_57),k2_relat_1(A_57))
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_2432,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2392,c_100])).

tff(c_2458,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1755,c_784,c_1751,c_2432])).

tff(c_98,plain,(
    ! [A_57] :
      ( m1_subset_1(A_57,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_57),k2_relat_1(A_57))))
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_2426,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2392,c_98])).

tff(c_2454,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1755,c_784,c_1751,c_2426])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4074,plain,(
    ! [B_306,D_307,A_308,C_309] :
      ( k1_xboole_0 = B_306
      | m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(A_308,C_309)))
      | ~ r1_tarski(B_306,C_309)
      | ~ m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(A_308,B_306)))
      | ~ v1_funct_2(D_307,A_308,B_306)
      | ~ v1_funct_1(D_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_23364,plain,(
    ! [B_965,D_966,A_967,A_968] :
      ( k1_relat_1(B_965) = k1_xboole_0
      | m1_subset_1(D_966,k1_zfmisc_1(k2_zfmisc_1(A_967,A_968)))
      | ~ m1_subset_1(D_966,k1_zfmisc_1(k2_zfmisc_1(A_967,k1_relat_1(B_965))))
      | ~ v1_funct_2(D_966,A_967,k1_relat_1(B_965))
      | ~ v1_funct_1(D_966)
      | ~ v4_relat_1(B_965,A_968)
      | ~ v1_relat_1(B_965) ) ),
    inference(resolution,[status(thm)],[c_24,c_4074])).

tff(c_23382,plain,(
    ! [A_968] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_968)))
      | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_968)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2454,c_23364])).

tff(c_23413,plain,(
    ! [A_968] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_968)))
      | ~ v4_relat_1('#skF_4',A_968) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_784,c_2458,c_23382])).

tff(c_23430,plain,(
    ! [A_969] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_969)))
      | ~ v4_relat_1('#skF_4',A_969) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1115,c_23413])).

tff(c_23498,plain,(
    ~ v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_23430,c_865])).

tff(c_23561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_23498])).

tff(c_23562,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1100])).

tff(c_158,plain,(
    ! [A_68] : k6_relat_1(A_68) = k6_partfun1(A_68) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_54,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_164,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_54])).

tff(c_96,plain,(
    ! [A_56] : k6_relat_1(A_56) = k6_partfun1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_50,plain,(
    ! [A_25] : k2_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_205,plain,(
    ! [A_70] : k2_relat_1(k6_partfun1(A_70)) = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_50])).

tff(c_214,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_205])).

tff(c_23577,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23562,c_23562,c_214])).

tff(c_44,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) = k1_xboole_0
      | k2_relat_1(A_24) != k1_xboole_0
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1098,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1087,c_44])).

tff(c_23590,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23562,c_23562,c_1098])).

tff(c_23591,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_23590])).

tff(c_23623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23577,c_23591])).

tff(c_23625,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_23590])).

tff(c_40,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1099,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1087,c_40])).

tff(c_1101,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1099])).

tff(c_23564,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23562,c_1101])).

tff(c_23669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23625,c_23564])).

tff(c_23670,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1099])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_23690,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23670,c_8])).

tff(c_48,plain,(
    ! [A_25] : k1_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_184,plain,(
    ! [A_69] : k1_relat_1(k6_partfun1(A_69)) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_48])).

tff(c_193,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_184])).

tff(c_23685,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23670,c_23670,c_193])).

tff(c_24372,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_24368,c_36])).

tff(c_24382,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_23685,c_24372])).

tff(c_28,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(k2_relat_1(A_17))
      | ~ v1_relat_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24401,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24382,c_28])).

tff(c_24409,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24386,c_23690,c_24401])).

tff(c_24411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24300,c_24409])).

tff(c_24413,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_783])).

tff(c_24783,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24413,c_24761])).

tff(c_25382,plain,(
    ! [A_1121] :
      ( k4_relat_1(A_1121) = k2_funct_1(A_1121)
      | ~ v2_funct_1(A_1121)
      | ~ v1_funct_1(A_1121)
      | ~ v1_relat_1(A_1121) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_25385,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_25382])).

tff(c_25388,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24788,c_126,c_25385])).

tff(c_25392,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25388,c_36])).

tff(c_25402,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24788,c_25392])).

tff(c_25395,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25388,c_38])).

tff(c_25404,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24788,c_25395])).

tff(c_25437,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25404,c_100])).

tff(c_25456,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24783,c_784,c_25402,c_25437])).

tff(c_25813,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25810,c_25456])).

tff(c_25817,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25810,c_25404])).

tff(c_25917,plain,(
    ! [A_1154] :
      ( m1_subset_1(A_1154,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1154),k2_relat_1(A_1154))))
      | ~ v1_funct_1(A_1154)
      | ~ v1_relat_1(A_1154) ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_25949,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25402,c_25917])).

tff(c_25982,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24783,c_784,c_25817,c_25949])).

tff(c_27089,plain,(
    ! [B_1195,D_1196,A_1197,C_1198] :
      ( k1_xboole_0 = B_1195
      | v1_funct_2(D_1196,A_1197,C_1198)
      | ~ r1_tarski(B_1195,C_1198)
      | ~ m1_subset_1(D_1196,k1_zfmisc_1(k2_zfmisc_1(A_1197,B_1195)))
      | ~ v1_funct_2(D_1196,A_1197,B_1195)
      | ~ v1_funct_1(D_1196) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_46369,plain,(
    ! [B_1840,D_1841,A_1842,A_1843] :
      ( k1_relat_1(B_1840) = k1_xboole_0
      | v1_funct_2(D_1841,A_1842,A_1843)
      | ~ m1_subset_1(D_1841,k1_zfmisc_1(k2_zfmisc_1(A_1842,k1_relat_1(B_1840))))
      | ~ v1_funct_2(D_1841,A_1842,k1_relat_1(B_1840))
      | ~ v1_funct_1(D_1841)
      | ~ v4_relat_1(B_1840,A_1843)
      | ~ v1_relat_1(B_1840) ) ),
    inference(resolution,[status(thm)],[c_24,c_27089])).

tff(c_46387,plain,(
    ! [A_1843] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_1843)
      | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_1843)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_25982,c_46369])).

tff(c_46418,plain,(
    ! [A_1843] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_1843)
      | ~ v4_relat_1('#skF_4',A_1843) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24788,c_784,c_25813,c_46387])).

tff(c_46435,plain,(
    ! [A_1844] :
      ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_1844)
      | ~ v4_relat_1('#skF_4',A_1844) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24817,c_46418])).

tff(c_24412,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_783])).

tff(c_46438,plain,(
    ~ v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46435,c_24412])).

tff(c_46442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25337,c_46438])).

tff(c_46443,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24797])).

tff(c_46460,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46443,c_46443,c_214])).

tff(c_24796,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24788,c_40])).

tff(c_24815,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24796])).

tff(c_46445,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46443,c_24815])).

tff(c_46519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46460,c_46445])).

tff(c_46520,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24796])).

tff(c_46521,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24796])).

tff(c_46576,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46520,c_46521])).

tff(c_48347,plain,(
    ! [A_1987,B_1988,C_1989] :
      ( k2_relset_1(A_1987,B_1988,C_1989) = k2_relat_1(C_1989)
      | ~ m1_subset_1(C_1989,k1_zfmisc_1(k2_zfmisc_1(A_1987,B_1988))) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_48366,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_48347])).

tff(c_48380,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_46576,c_48366])).

tff(c_24805,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != k1_xboole_0
    | k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24783,c_42])).

tff(c_46673,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46520,c_46520,c_24805])).

tff(c_46674,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46673])).

tff(c_46686,plain,(
    ! [A_1850] :
      ( k1_relat_1(A_1850) = '#skF_4'
      | k2_relat_1(A_1850) != '#skF_4'
      | ~ v1_relat_1(A_1850) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46520,c_46520,c_44])).

tff(c_46692,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_24783,c_46686])).

tff(c_46708,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46674,c_46692])).

tff(c_46537,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46520,c_46520,c_193])).

tff(c_47267,plain,(
    ! [A_1902] :
      ( k4_relat_1(A_1902) = k2_funct_1(A_1902)
      | ~ v2_funct_1(A_1902)
      | ~ v1_funct_1(A_1902)
      | ~ v1_relat_1(A_1902) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_47270,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_47267])).

tff(c_47273,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24788,c_126,c_47270])).

tff(c_47277,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_47273,c_36])).

tff(c_47287,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24788,c_46537,c_47277])).

tff(c_47289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46708,c_47287])).

tff(c_47290,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46673])).

tff(c_47295,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47290,c_24412])).

tff(c_48386,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48380,c_47295])).

tff(c_133,plain,(
    ! [A_25] : k1_relat_1(k6_partfun1(A_25)) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_48])).

tff(c_64,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_130,plain,(
    ! [A_30] : v1_relat_1(k6_partfun1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64])).

tff(c_222,plain,(
    ! [A_72] :
      ( k1_relat_1(A_72) != k1_xboole_0
      | k1_xboole_0 = A_72
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_231,plain,(
    ! [A_30] :
      ( k1_relat_1(k6_partfun1(A_30)) != k1_xboole_0
      | k6_partfun1(A_30) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_130,c_222])).

tff(c_245,plain,(
    ! [A_74] :
      ( k1_xboole_0 != A_74
      | k6_partfun1(A_74) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_231])).

tff(c_92,plain,(
    ! [A_55] : v1_partfun1(k6_partfun1(A_55),A_55) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_260,plain,(
    ! [A_74] :
      ( v1_partfun1(k1_xboole_0,A_74)
      | k1_xboole_0 != A_74 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_92])).

tff(c_46730,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46520,c_46520,c_260])).

tff(c_47294,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47290,c_24413])).

tff(c_48385,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48380,c_47294])).

tff(c_48585,plain,(
    ! [C_2003,A_2004,B_2005] :
      ( v1_funct_2(C_2003,A_2004,B_2005)
      | ~ v1_partfun1(C_2003,A_2004)
      | ~ v1_funct_1(C_2003)
      | ~ m1_subset_1(C_2003,k1_zfmisc_1(k2_zfmisc_1(A_2004,B_2005))) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_48591,plain,
    ( v1_funct_2('#skF_4','#skF_4','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48385,c_48585])).

tff(c_48614,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_46730,c_48591])).

tff(c_48616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48386,c_48614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.58/9.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.58/9.97  
% 18.58/9.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.58/9.97  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 18.58/9.97  
% 18.58/9.97  %Foreground sorts:
% 18.58/9.97  
% 18.58/9.97  
% 18.58/9.97  %Background operators:
% 18.58/9.97  
% 18.58/9.97  
% 18.58/9.97  %Foreground operators:
% 18.58/9.97  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 18.58/9.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.58/9.97  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 18.58/9.97  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 18.58/9.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.58/9.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.58/9.97  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 18.58/9.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.58/9.97  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 18.58/9.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.58/9.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.58/9.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 18.58/9.97  tff('#skF_2', type, '#skF_2': $i).
% 18.58/9.97  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.58/9.97  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 18.58/9.97  tff('#skF_3', type, '#skF_3': $i).
% 18.58/9.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 18.58/9.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.58/9.97  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 18.58/9.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.58/9.97  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 18.58/9.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.58/9.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 18.58/9.97  tff('#skF_4', type, '#skF_4': $i).
% 18.58/9.97  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 18.58/9.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.58/9.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 18.58/9.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.58/9.97  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 18.58/9.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 18.58/9.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.58/9.97  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 18.58/9.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.58/9.97  
% 18.79/10.00  tff(f_270, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 18.79/10.00  tff(f_204, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 18.79/10.00  tff(f_198, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 18.79/10.00  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 18.79/10.00  tff(f_131, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 18.79/10.00  tff(f_208, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 18.79/10.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 18.79/10.00  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 18.79/10.00  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 18.79/10.00  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 18.79/10.00  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 18.79/10.00  tff(f_123, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 18.79/10.00  tff(f_62, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 18.79/10.00  tff(f_88, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 18.79/10.00  tff(f_234, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 18.79/10.00  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 18.79/10.00  tff(f_253, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 18.79/10.00  tff(f_224, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 18.79/10.00  tff(f_111, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 18.79/10.00  tff(f_106, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 18.79/10.00  tff(f_102, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 18.79/10.00  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 18.79/10.00  tff(f_70, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 18.79/10.00  tff(f_135, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 18.79/10.00  tff(f_222, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 18.79/10.00  tff(f_218, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 18.79/10.00  tff(c_118, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_270])).
% 18.79/10.00  tff(c_122, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_270])).
% 18.79/10.00  tff(c_25311, plain, (![C_1113, A_1114, B_1115]: (v4_relat_1(C_1113, A_1114) | ~m1_subset_1(C_1113, k1_zfmisc_1(k2_zfmisc_1(A_1114, B_1115))))), inference(cnfTransformation, [status(thm)], [f_204])).
% 18.79/10.00  tff(c_25337, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_122, c_25311])).
% 18.79/10.00  tff(c_24761, plain, (![C_1047, A_1048, B_1049]: (v1_relat_1(C_1047) | ~m1_subset_1(C_1047, k1_zfmisc_1(k2_zfmisc_1(A_1048, B_1049))))), inference(cnfTransformation, [status(thm)], [f_198])).
% 18.79/10.00  tff(c_24788, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_24761])).
% 18.79/10.00  tff(c_42, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 18.79/10.00  tff(c_24797, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_24788, c_42])).
% 18.79/10.00  tff(c_24817, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24797])).
% 18.79/10.00  tff(c_126, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_270])).
% 18.79/10.00  tff(c_370, plain, (![A_85]: (v1_funct_1(k2_funct_1(A_85)) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_131])).
% 18.79/10.00  tff(c_116, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_270])).
% 18.79/10.00  tff(c_277, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_116])).
% 18.79/10.00  tff(c_373, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_370, c_277])).
% 18.79/10.00  tff(c_376, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_373])).
% 18.79/10.00  tff(c_756, plain, (![C_110, A_111, B_112]: (v1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_198])).
% 18.79/10.00  tff(c_769, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_756])).
% 18.79/10.00  tff(c_782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_769])).
% 18.79/10.00  tff(c_784, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_116])).
% 18.79/10.00  tff(c_25781, plain, (![A_1150, B_1151, C_1152]: (k2_relset_1(A_1150, B_1151, C_1152)=k2_relat_1(C_1152) | ~m1_subset_1(C_1152, k1_zfmisc_1(k2_zfmisc_1(A_1150, B_1151))))), inference(cnfTransformation, [status(thm)], [f_208])).
% 18.79/10.00  tff(c_25797, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_25781])).
% 18.79/10.00  tff(c_25810, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_25797])).
% 18.79/10.00  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 18.79/10.00  tff(c_12, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.79/10.00  tff(c_14, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.79/10.00  tff(c_134, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 18.79/10.00  tff(c_24270, plain, (![C_1014, B_1015, A_1016]: (~v1_xboole_0(C_1014) | ~m1_subset_1(B_1015, k1_zfmisc_1(C_1014)) | ~r2_hidden(A_1016, B_1015))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.79/10.00  tff(c_24286, plain, (![A_1017, A_1018]: (~v1_xboole_0(A_1017) | ~r2_hidden(A_1018, A_1017))), inference(resolution, [status(thm)], [c_134, c_24270])).
% 18.79/10.00  tff(c_24291, plain, (![A_1019, B_1020]: (~v1_xboole_0(A_1019) | r1_tarski(A_1019, B_1020))), inference(resolution, [status(thm)], [c_6, c_24286])).
% 18.79/10.00  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.79/10.00  tff(c_783, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_116])).
% 18.79/10.00  tff(c_865, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_783])).
% 18.79/10.00  tff(c_991, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_865])).
% 18.79/10.00  tff(c_24300, plain, (~v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_24291, c_991])).
% 18.79/10.00  tff(c_1064, plain, (![C_138, A_139, B_140]: (v1_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_198])).
% 18.79/10.00  tff(c_1087, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_1064])).
% 18.79/10.00  tff(c_120, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_270])).
% 18.79/10.00  tff(c_24362, plain, (![A_1026]: (k4_relat_1(A_1026)=k2_funct_1(A_1026) | ~v2_funct_1(A_1026) | ~v1_funct_1(A_1026) | ~v1_relat_1(A_1026))), inference(cnfTransformation, [status(thm)], [f_123])).
% 18.79/10.00  tff(c_24365, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_24362])).
% 18.79/10.00  tff(c_24368, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_126, c_24365])).
% 18.79/10.00  tff(c_26, plain, (![A_16]: (v1_relat_1(k4_relat_1(A_16)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.79/10.00  tff(c_24378, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_24368, c_26])).
% 18.79/10.00  tff(c_24386, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_24378])).
% 18.79/10.00  tff(c_1569, plain, (![C_176, A_177, B_178]: (v4_relat_1(C_176, A_177) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_204])).
% 18.79/10.00  tff(c_1591, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_122, c_1569])).
% 18.79/10.00  tff(c_1100, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1087, c_42])).
% 18.79/10.00  tff(c_1115, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1100])).
% 18.79/10.00  tff(c_1731, plain, (![A_200]: (k4_relat_1(A_200)=k2_funct_1(A_200) | ~v2_funct_1(A_200) | ~v1_funct_1(A_200) | ~v1_relat_1(A_200))), inference(cnfTransformation, [status(thm)], [f_123])).
% 18.79/10.00  tff(c_1734, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_1731])).
% 18.79/10.00  tff(c_1737, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_126, c_1734])).
% 18.79/10.00  tff(c_1747, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1737, c_26])).
% 18.79/10.00  tff(c_1755, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_1747])).
% 18.79/10.00  tff(c_36, plain, (![A_22]: (k2_relat_1(k4_relat_1(A_22))=k1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.79/10.00  tff(c_1741, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1737, c_36])).
% 18.79/10.00  tff(c_1751, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_1741])).
% 18.79/10.00  tff(c_2358, plain, (![A_248, B_249, C_250]: (k2_relset_1(A_248, B_249, C_250)=k2_relat_1(C_250) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_208])).
% 18.79/10.00  tff(c_2374, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_2358])).
% 18.79/10.00  tff(c_2386, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_2374])).
% 18.79/10.00  tff(c_38, plain, (![A_22]: (k1_relat_1(k4_relat_1(A_22))=k2_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.79/10.00  tff(c_1744, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1737, c_38])).
% 18.79/10.00  tff(c_1753, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_1744])).
% 18.79/10.00  tff(c_2392, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2386, c_1753])).
% 18.79/10.00  tff(c_100, plain, (![A_57]: (v1_funct_2(A_57, k1_relat_1(A_57), k2_relat_1(A_57)) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_234])).
% 18.79/10.00  tff(c_2432, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2392, c_100])).
% 18.79/10.00  tff(c_2458, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1755, c_784, c_1751, c_2432])).
% 18.79/10.00  tff(c_98, plain, (![A_57]: (m1_subset_1(A_57, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_57), k2_relat_1(A_57)))) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_234])).
% 18.79/10.00  tff(c_2426, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2392, c_98])).
% 18.79/10.00  tff(c_2454, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1755, c_784, c_1751, c_2426])).
% 18.79/10.00  tff(c_24, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 18.79/10.00  tff(c_4074, plain, (![B_306, D_307, A_308, C_309]: (k1_xboole_0=B_306 | m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(A_308, C_309))) | ~r1_tarski(B_306, C_309) | ~m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(A_308, B_306))) | ~v1_funct_2(D_307, A_308, B_306) | ~v1_funct_1(D_307))), inference(cnfTransformation, [status(thm)], [f_253])).
% 18.79/10.00  tff(c_23364, plain, (![B_965, D_966, A_967, A_968]: (k1_relat_1(B_965)=k1_xboole_0 | m1_subset_1(D_966, k1_zfmisc_1(k2_zfmisc_1(A_967, A_968))) | ~m1_subset_1(D_966, k1_zfmisc_1(k2_zfmisc_1(A_967, k1_relat_1(B_965)))) | ~v1_funct_2(D_966, A_967, k1_relat_1(B_965)) | ~v1_funct_1(D_966) | ~v4_relat_1(B_965, A_968) | ~v1_relat_1(B_965))), inference(resolution, [status(thm)], [c_24, c_4074])).
% 18.79/10.00  tff(c_23382, plain, (![A_968]: (k1_relat_1('#skF_4')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_968))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_4', A_968) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2454, c_23364])).
% 18.79/10.00  tff(c_23413, plain, (![A_968]: (k1_relat_1('#skF_4')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_968))) | ~v4_relat_1('#skF_4', A_968))), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_784, c_2458, c_23382])).
% 18.79/10.00  tff(c_23430, plain, (![A_969]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_969))) | ~v4_relat_1('#skF_4', A_969))), inference(negUnitSimplification, [status(thm)], [c_1115, c_23413])).
% 18.79/10.00  tff(c_23498, plain, (~v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_23430, c_865])).
% 18.79/10.00  tff(c_23561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1591, c_23498])).
% 18.79/10.00  tff(c_23562, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1100])).
% 18.79/10.00  tff(c_158, plain, (![A_68]: (k6_relat_1(A_68)=k6_partfun1(A_68))), inference(cnfTransformation, [status(thm)], [f_224])).
% 18.79/10.00  tff(c_54, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 18.79/10.00  tff(c_164, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_158, c_54])).
% 18.79/10.00  tff(c_96, plain, (![A_56]: (k6_relat_1(A_56)=k6_partfun1(A_56))), inference(cnfTransformation, [status(thm)], [f_224])).
% 18.79/10.00  tff(c_50, plain, (![A_25]: (k2_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.79/10.00  tff(c_205, plain, (![A_70]: (k2_relat_1(k6_partfun1(A_70))=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_50])).
% 18.79/10.00  tff(c_214, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_164, c_205])).
% 18.79/10.00  tff(c_23577, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23562, c_23562, c_214])).
% 18.79/10.00  tff(c_44, plain, (![A_24]: (k1_relat_1(A_24)=k1_xboole_0 | k2_relat_1(A_24)!=k1_xboole_0 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_102])).
% 18.79/10.00  tff(c_1098, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1087, c_44])).
% 18.79/10.00  tff(c_23590, plain, (k1_relat_1('#skF_4')='#skF_4' | k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23562, c_23562, c_1098])).
% 18.79/10.00  tff(c_23591, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_23590])).
% 18.79/10.00  tff(c_23623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23577, c_23591])).
% 18.79/10.00  tff(c_23625, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_23590])).
% 18.79/10.00  tff(c_40, plain, (![A_23]: (k2_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 18.79/10.00  tff(c_1099, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1087, c_40])).
% 18.79/10.00  tff(c_1101, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1099])).
% 18.79/10.00  tff(c_23564, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23562, c_1101])).
% 18.79/10.00  tff(c_23669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23625, c_23564])).
% 18.79/10.00  tff(c_23670, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1099])).
% 18.79/10.00  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.79/10.00  tff(c_23690, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23670, c_8])).
% 18.79/10.00  tff(c_48, plain, (![A_25]: (k1_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.79/10.00  tff(c_184, plain, (![A_69]: (k1_relat_1(k6_partfun1(A_69))=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_48])).
% 18.79/10.00  tff(c_193, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_164, c_184])).
% 18.79/10.00  tff(c_23685, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23670, c_23670, c_193])).
% 18.79/10.00  tff(c_24372, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_24368, c_36])).
% 18.79/10.00  tff(c_24382, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_23685, c_24372])).
% 18.79/10.00  tff(c_28, plain, (![A_17]: (~v1_xboole_0(k2_relat_1(A_17)) | ~v1_relat_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 18.79/10.00  tff(c_24401, plain, (~v1_xboole_0('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | v1_xboole_0(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_24382, c_28])).
% 18.79/10.00  tff(c_24409, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24386, c_23690, c_24401])).
% 18.79/10.00  tff(c_24411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24300, c_24409])).
% 18.79/10.00  tff(c_24413, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_783])).
% 18.79/10.00  tff(c_24783, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_24413, c_24761])).
% 18.79/10.00  tff(c_25382, plain, (![A_1121]: (k4_relat_1(A_1121)=k2_funct_1(A_1121) | ~v2_funct_1(A_1121) | ~v1_funct_1(A_1121) | ~v1_relat_1(A_1121))), inference(cnfTransformation, [status(thm)], [f_123])).
% 18.79/10.00  tff(c_25385, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_25382])).
% 18.79/10.00  tff(c_25388, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24788, c_126, c_25385])).
% 18.79/10.00  tff(c_25392, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25388, c_36])).
% 18.79/10.00  tff(c_25402, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24788, c_25392])).
% 18.79/10.00  tff(c_25395, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25388, c_38])).
% 18.79/10.00  tff(c_25404, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24788, c_25395])).
% 18.79/10.00  tff(c_25437, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_25404, c_100])).
% 18.79/10.00  tff(c_25456, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24783, c_784, c_25402, c_25437])).
% 18.79/10.00  tff(c_25813, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_25810, c_25456])).
% 18.79/10.00  tff(c_25817, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25810, c_25404])).
% 18.79/10.00  tff(c_25917, plain, (![A_1154]: (m1_subset_1(A_1154, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1154), k2_relat_1(A_1154)))) | ~v1_funct_1(A_1154) | ~v1_relat_1(A_1154))), inference(cnfTransformation, [status(thm)], [f_234])).
% 18.79/10.00  tff(c_25949, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4')))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_25402, c_25917])).
% 18.79/10.00  tff(c_25982, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_24783, c_784, c_25817, c_25949])).
% 18.79/10.00  tff(c_27089, plain, (![B_1195, D_1196, A_1197, C_1198]: (k1_xboole_0=B_1195 | v1_funct_2(D_1196, A_1197, C_1198) | ~r1_tarski(B_1195, C_1198) | ~m1_subset_1(D_1196, k1_zfmisc_1(k2_zfmisc_1(A_1197, B_1195))) | ~v1_funct_2(D_1196, A_1197, B_1195) | ~v1_funct_1(D_1196))), inference(cnfTransformation, [status(thm)], [f_253])).
% 18.79/10.00  tff(c_46369, plain, (![B_1840, D_1841, A_1842, A_1843]: (k1_relat_1(B_1840)=k1_xboole_0 | v1_funct_2(D_1841, A_1842, A_1843) | ~m1_subset_1(D_1841, k1_zfmisc_1(k2_zfmisc_1(A_1842, k1_relat_1(B_1840)))) | ~v1_funct_2(D_1841, A_1842, k1_relat_1(B_1840)) | ~v1_funct_1(D_1841) | ~v4_relat_1(B_1840, A_1843) | ~v1_relat_1(B_1840))), inference(resolution, [status(thm)], [c_24, c_27089])).
% 18.79/10.00  tff(c_46387, plain, (![A_1843]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_1843) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_4', A_1843) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_25982, c_46369])).
% 18.79/10.00  tff(c_46418, plain, (![A_1843]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_1843) | ~v4_relat_1('#skF_4', A_1843))), inference(demodulation, [status(thm), theory('equality')], [c_24788, c_784, c_25813, c_46387])).
% 18.79/10.00  tff(c_46435, plain, (![A_1844]: (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_1844) | ~v4_relat_1('#skF_4', A_1844))), inference(negUnitSimplification, [status(thm)], [c_24817, c_46418])).
% 18.79/10.00  tff(c_24412, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_783])).
% 18.79/10.00  tff(c_46438, plain, (~v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_46435, c_24412])).
% 18.79/10.00  tff(c_46442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25337, c_46438])).
% 18.79/10.00  tff(c_46443, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_24797])).
% 18.79/10.00  tff(c_46460, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46443, c_46443, c_214])).
% 18.79/10.00  tff(c_24796, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_24788, c_40])).
% 18.79/10.00  tff(c_24815, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24796])).
% 18.79/10.00  tff(c_46445, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46443, c_24815])).
% 18.79/10.00  tff(c_46519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46460, c_46445])).
% 18.79/10.00  tff(c_46520, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_24796])).
% 18.79/10.00  tff(c_46521, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_24796])).
% 18.79/10.00  tff(c_46576, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46520, c_46521])).
% 18.79/10.00  tff(c_48347, plain, (![A_1987, B_1988, C_1989]: (k2_relset_1(A_1987, B_1988, C_1989)=k2_relat_1(C_1989) | ~m1_subset_1(C_1989, k1_zfmisc_1(k2_zfmisc_1(A_1987, B_1988))))), inference(cnfTransformation, [status(thm)], [f_208])).
% 18.79/10.00  tff(c_48366, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_48347])).
% 18.79/10.00  tff(c_48380, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_46576, c_48366])).
% 18.79/10.00  tff(c_24805, plain, (k1_relat_1(k2_funct_1('#skF_4'))!=k1_xboole_0 | k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_24783, c_42])).
% 18.79/10.00  tff(c_46673, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46520, c_46520, c_24805])).
% 18.79/10.00  tff(c_46674, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_46673])).
% 18.79/10.00  tff(c_46686, plain, (![A_1850]: (k1_relat_1(A_1850)='#skF_4' | k2_relat_1(A_1850)!='#skF_4' | ~v1_relat_1(A_1850))), inference(demodulation, [status(thm), theory('equality')], [c_46520, c_46520, c_44])).
% 18.79/10.00  tff(c_46692, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_4' | k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_24783, c_46686])).
% 18.79/10.00  tff(c_46708, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46674, c_46692])).
% 18.79/10.00  tff(c_46537, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46520, c_46520, c_193])).
% 18.79/10.00  tff(c_47267, plain, (![A_1902]: (k4_relat_1(A_1902)=k2_funct_1(A_1902) | ~v2_funct_1(A_1902) | ~v1_funct_1(A_1902) | ~v1_relat_1(A_1902))), inference(cnfTransformation, [status(thm)], [f_123])).
% 18.79/10.00  tff(c_47270, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_47267])).
% 18.79/10.00  tff(c_47273, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24788, c_126, c_47270])).
% 18.79/10.00  tff(c_47277, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_47273, c_36])).
% 18.79/10.00  tff(c_47287, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24788, c_46537, c_47277])).
% 18.79/10.00  tff(c_47289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46708, c_47287])).
% 18.79/10.00  tff(c_47290, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_46673])).
% 18.79/10.00  tff(c_47295, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_47290, c_24412])).
% 18.79/10.00  tff(c_48386, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48380, c_47295])).
% 18.79/10.00  tff(c_133, plain, (![A_25]: (k1_relat_1(k6_partfun1(A_25))=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_48])).
% 18.79/10.00  tff(c_64, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_135])).
% 18.79/10.00  tff(c_130, plain, (![A_30]: (v1_relat_1(k6_partfun1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64])).
% 18.79/10.00  tff(c_222, plain, (![A_72]: (k1_relat_1(A_72)!=k1_xboole_0 | k1_xboole_0=A_72 | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_96])).
% 18.79/10.00  tff(c_231, plain, (![A_30]: (k1_relat_1(k6_partfun1(A_30))!=k1_xboole_0 | k6_partfun1(A_30)=k1_xboole_0)), inference(resolution, [status(thm)], [c_130, c_222])).
% 18.79/10.00  tff(c_245, plain, (![A_74]: (k1_xboole_0!=A_74 | k6_partfun1(A_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_231])).
% 18.79/10.00  tff(c_92, plain, (![A_55]: (v1_partfun1(k6_partfun1(A_55), A_55))), inference(cnfTransformation, [status(thm)], [f_222])).
% 18.79/10.00  tff(c_260, plain, (![A_74]: (v1_partfun1(k1_xboole_0, A_74) | k1_xboole_0!=A_74)), inference(superposition, [status(thm), theory('equality')], [c_245, c_92])).
% 18.79/10.00  tff(c_46730, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46520, c_46520, c_260])).
% 18.79/10.00  tff(c_47294, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_47290, c_24413])).
% 18.79/10.00  tff(c_48385, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48380, c_47294])).
% 18.79/10.00  tff(c_48585, plain, (![C_2003, A_2004, B_2005]: (v1_funct_2(C_2003, A_2004, B_2005) | ~v1_partfun1(C_2003, A_2004) | ~v1_funct_1(C_2003) | ~m1_subset_1(C_2003, k1_zfmisc_1(k2_zfmisc_1(A_2004, B_2005))))), inference(cnfTransformation, [status(thm)], [f_218])).
% 18.79/10.00  tff(c_48591, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48385, c_48585])).
% 18.79/10.00  tff(c_48614, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_46730, c_48591])).
% 18.79/10.00  tff(c_48616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48386, c_48614])).
% 18.79/10.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.79/10.00  
% 18.79/10.00  Inference rules
% 18.79/10.00  ----------------------
% 18.79/10.00  #Ref     : 0
% 18.79/10.00  #Sup     : 11039
% 18.79/10.00  #Fact    : 0
% 18.79/10.00  #Define  : 0
% 18.79/10.00  #Split   : 127
% 18.79/10.00  #Chain   : 0
% 18.79/10.00  #Close   : 0
% 18.79/10.00  
% 18.79/10.00  Ordering : KBO
% 18.79/10.00  
% 18.79/10.00  Simplification rules
% 18.79/10.00  ----------------------
% 18.79/10.00  #Subsume      : 4931
% 18.79/10.00  #Demod        : 11891
% 18.79/10.00  #Tautology    : 3637
% 18.79/10.00  #SimpNegUnit  : 541
% 18.79/10.00  #BackRed      : 393
% 18.79/10.00  
% 18.79/10.00  #Partial instantiations: 0
% 18.79/10.00  #Strategies tried      : 1
% 18.79/10.00  
% 18.79/10.00  Timing (in seconds)
% 18.79/10.00  ----------------------
% 18.79/10.00  Preprocessing        : 0.40
% 18.79/10.00  Parsing              : 0.21
% 18.79/10.00  CNF conversion       : 0.03
% 18.79/10.00  Main loop            : 8.73
% 18.79/10.00  Inferencing          : 1.88
% 18.79/10.00  Reduction            : 3.78
% 18.79/10.00  Demodulation         : 2.92
% 18.79/10.00  BG Simplification    : 0.16
% 18.79/10.00  Subsumption          : 2.38
% 18.79/10.00  Abstraction          : 0.22
% 18.79/10.00  MUC search           : 0.00
% 18.79/10.00  Cooper               : 0.00
% 18.79/10.00  Total                : 9.19
% 18.79/10.00  Index Insertion      : 0.00
% 18.79/10.00  Index Deletion       : 0.00
% 18.79/10.00  Index Matching       : 0.00
% 18.79/10.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
