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
% DateTime   : Thu Dec  3 10:12:46 EST 2020

% Result     : Theorem 12.25s
% Output     : CNFRefutation 12.40s
% Verified   : 
% Statistics : Number of formulae       :  236 (2127 expanded)
%              Number of leaves         :   53 ( 705 expanded)
%              Depth                    :   14
%              Number of atoms          :  395 (5803 expanded)
%              Number of equality atoms :  130 (1836 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_5 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
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

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_153,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_141,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_106,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_324,plain,(
    ! [C_92,A_93,B_94] :
      ( v1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_342,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_106,c_324])).

tff(c_110,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_104,plain,(
    v2_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_102,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_28964,plain,(
    ! [A_980,B_981,C_982] :
      ( k2_relset_1(A_980,B_981,C_982) = k2_relat_1(C_982)
      | ~ m1_subset_1(C_982,k1_zfmisc_1(k2_zfmisc_1(A_980,B_981))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28983,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_106,c_28964])).

tff(c_28996,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_28983])).

tff(c_56,plain,(
    ! [A_37] :
      ( k1_relat_1(k2_funct_1(A_37)) = k2_relat_1(A_37)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    ! [A_35] :
      ( v1_funct_1(k2_funct_1(A_35))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_100,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8')))
    | ~ v1_funct_2(k2_funct_1('#skF_10'),'#skF_9','#skF_8')
    | ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_213,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_216,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_46,c_213])).

tff(c_219,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_216])).

tff(c_242,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_252,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_106,c_242])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_252])).

tff(c_264,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_10'),'#skF_9','#skF_8')
    | ~ m1_subset_1(k2_funct_1('#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_356,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_1059,plain,(
    ! [A_178,B_179,C_180] :
      ( k2_relset_1(A_178,B_179,C_180) = k2_relat_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1075,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_106,c_1059])).

tff(c_1087,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1075])).

tff(c_48,plain,(
    ! [A_35] :
      ( v1_relat_1(k2_funct_1(A_35))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_265,plain,(
    v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_42,plain,(
    ! [A_34] :
      ( k2_relat_1(A_34) != k1_xboole_0
      | k1_xboole_0 = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_349,plain,
    ( k2_relat_1('#skF_10') != k1_xboole_0
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_342,c_42])).

tff(c_358,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_1088,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_358])).

tff(c_108,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1010,plain,(
    ! [A_174,B_175,C_176] :
      ( k1_relset_1(A_174,B_175,C_176) = k1_relat_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1037,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_106,c_1010])).

tff(c_3620,plain,(
    ! [B_260,A_261,C_262] :
      ( k1_xboole_0 = B_260
      | k1_relset_1(A_261,B_260,C_262) = A_261
      | ~ v1_funct_2(C_262,A_261,B_260)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_261,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3639,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_106,c_3620])).

tff(c_3659,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1037,c_3639])).

tff(c_3660,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1088,c_3659])).

tff(c_668,plain,(
    ! [A_135] :
      ( k2_relat_1(k2_funct_1(A_135)) = k1_relat_1(A_135)
      | ~ v2_funct_1(A_135)
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_96,plain,(
    ! [A_55] :
      ( v1_funct_2(A_55,k1_relat_1(A_55),k2_relat_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_15264,plain,(
    ! [A_499] :
      ( v1_funct_2(k2_funct_1(A_499),k1_relat_1(k2_funct_1(A_499)),k1_relat_1(A_499))
      | ~ v1_funct_1(k2_funct_1(A_499))
      | ~ v1_relat_1(k2_funct_1(A_499))
      | ~ v2_funct_1(A_499)
      | ~ v1_funct_1(A_499)
      | ~ v1_relat_1(A_499) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_96])).

tff(c_15273,plain,
    ( v1_funct_2(k2_funct_1('#skF_10'),k1_relat_1(k2_funct_1('#skF_10')),'#skF_8')
    | ~ v1_funct_1(k2_funct_1('#skF_10'))
    | ~ v1_relat_1(k2_funct_1('#skF_10'))
    | ~ v2_funct_1('#skF_10')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_15264])).

tff(c_15286,plain,
    ( v1_funct_2(k2_funct_1('#skF_10'),k1_relat_1(k2_funct_1('#skF_10')),'#skF_8')
    | ~ v1_relat_1(k2_funct_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_110,c_104,c_265,c_15273])).

tff(c_15465,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_15286])).

tff(c_15468,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_48,c_15465])).

tff(c_15472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_110,c_15468])).

tff(c_15474,plain,(
    v1_relat_1(k2_funct_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_15286])).

tff(c_54,plain,(
    ! [A_37] :
      ( k2_relat_1(k2_funct_1(A_37)) = k1_relat_1(A_37)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_882,plain,(
    ! [A_166] :
      ( m1_subset_1(A_166,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_166),k2_relat_1(A_166))))
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_16399,plain,(
    ! [A_520] :
      ( m1_subset_1(k2_funct_1(A_520),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_520)),k1_relat_1(A_520))))
      | ~ v1_funct_1(k2_funct_1(A_520))
      | ~ v1_relat_1(k2_funct_1(A_520))
      | ~ v2_funct_1(A_520)
      | ~ v1_funct_1(A_520)
      | ~ v1_relat_1(A_520) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_882])).

tff(c_16426,plain,
    ( m1_subset_1(k2_funct_1('#skF_10'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_10')),'#skF_8')))
    | ~ v1_funct_1(k2_funct_1('#skF_10'))
    | ~ v1_relat_1(k2_funct_1('#skF_10'))
    | ~ v2_funct_1('#skF_10')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_16399])).

tff(c_16446,plain,(
    m1_subset_1(k2_funct_1('#skF_10'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_10')),'#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_110,c_104,c_15474,c_265,c_16426])).

tff(c_16469,plain,
    ( m1_subset_1(k2_funct_1('#skF_10'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_10'),'#skF_8')))
    | ~ v2_funct_1('#skF_10')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_16446])).

tff(c_16483,plain,(
    m1_subset_1(k2_funct_1('#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_110,c_104,c_1087,c_16469])).

tff(c_16485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_356,c_16483])).

tff(c_16486,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_16487,plain,(
    k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_16509,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16486,c_16487])).

tff(c_17087,plain,(
    ! [A_585,B_586,C_587] :
      ( k2_relset_1(A_585,B_586,C_587) = k2_relat_1(C_587)
      | ~ m1_subset_1(C_587,k1_zfmisc_1(k2_zfmisc_1(A_585,B_586))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_17106,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_106,c_17087])).

tff(c_17111,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16509,c_102,c_17106])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16501,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16486,c_12])).

tff(c_17141,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17111,c_16501])).

tff(c_17140,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17111,c_17111,c_16509])).

tff(c_17563,plain,(
    ! [A_609,C_610] :
      ( r2_hidden(k4_tarski('#skF_6'(A_609,k2_relat_1(A_609),C_610),C_610),A_609)
      | ~ r2_hidden(C_610,k2_relat_1(A_609)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17594,plain,(
    ! [A_612,C_613] :
      ( ~ v1_xboole_0(A_612)
      | ~ r2_hidden(C_613,k2_relat_1(A_612)) ) ),
    inference(resolution,[status(thm)],[c_17563,c_2])).

tff(c_17601,plain,(
    ! [C_613] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ r2_hidden(C_613,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17140,c_17594])).

tff(c_17623,plain,(
    ! [C_614] : ~ r2_hidden(C_614,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17141,c_17601])).

tff(c_17643,plain,(
    ! [B_6] : r1_tarski('#skF_9',B_6) ),
    inference(resolution,[status(thm)],[c_10,c_17623])).

tff(c_17143,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17111,c_342])).

tff(c_17150,plain,(
    v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17111,c_110])).

tff(c_17149,plain,(
    v2_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17111,c_104])).

tff(c_17145,plain,(
    v1_funct_1(k2_funct_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17111,c_265])).

tff(c_16983,plain,(
    ! [A_572] :
      ( k1_relat_1(k2_funct_1(A_572)) = k2_relat_1(A_572)
      | ~ v2_funct_1(A_572)
      | ~ v1_funct_1(A_572)
      | ~ v1_relat_1(A_572) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_27456,plain,(
    ! [A_900] :
      ( v1_funct_2(k2_funct_1(A_900),k2_relat_1(A_900),k2_relat_1(k2_funct_1(A_900)))
      | ~ v1_funct_1(k2_funct_1(A_900))
      | ~ v1_relat_1(k2_funct_1(A_900))
      | ~ v2_funct_1(A_900)
      | ~ v1_funct_1(A_900)
      | ~ v1_relat_1(A_900) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16983,c_96])).

tff(c_27489,plain,
    ( v1_funct_2(k2_funct_1('#skF_9'),'#skF_9',k2_relat_1(k2_funct_1('#skF_9')))
    | ~ v1_funct_1(k2_funct_1('#skF_9'))
    | ~ v1_relat_1(k2_funct_1('#skF_9'))
    | ~ v2_funct_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_17140,c_27456])).

tff(c_27497,plain,
    ( v1_funct_2(k2_funct_1('#skF_9'),'#skF_9',k2_relat_1(k2_funct_1('#skF_9')))
    | ~ v1_relat_1(k2_funct_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17143,c_17150,c_17149,c_17145,c_27489])).

tff(c_28237,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_27497])).

tff(c_28240,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_28237])).

tff(c_28244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17143,c_17150,c_28240])).

tff(c_28246,plain,(
    v1_relat_1(k2_funct_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_27497])).

tff(c_44,plain,(
    ! [A_34] :
      ( k1_relat_1(A_34) != k1_xboole_0
      | k1_xboole_0 = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16495,plain,(
    ! [A_34] :
      ( k1_relat_1(A_34) != '#skF_10'
      | A_34 = '#skF_10'
      | ~ v1_relat_1(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16486,c_16486,c_44])).

tff(c_17116,plain,(
    ! [A_34] :
      ( k1_relat_1(A_34) != '#skF_9'
      | A_34 = '#skF_9'
      | ~ v1_relat_1(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17111,c_17111,c_16495])).

tff(c_28253,plain,
    ( k1_relat_1(k2_funct_1('#skF_9')) != '#skF_9'
    | k2_funct_1('#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_28246,c_17116])).

tff(c_28269,plain,(
    k1_relat_1(k2_funct_1('#skF_9')) != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_28253])).

tff(c_28324,plain,
    ( k2_relat_1('#skF_9') != '#skF_9'
    | ~ v2_funct_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_28269])).

tff(c_28327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17143,c_17150,c_17149,c_17140,c_28324])).

tff(c_28328,plain,(
    k2_funct_1('#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_28253])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16497,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_10',B_12) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16486,c_16486,c_20])).

tff(c_17133,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_9',B_12) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17111,c_17111,c_16497])).

tff(c_17137,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_9'),k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17111,c_356])).

tff(c_17541,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_9'),k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17133,c_17137])).

tff(c_17545,plain,(
    ~ r1_tarski(k2_funct_1('#skF_9'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_17541])).

tff(c_28333,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28328,c_17545])).

tff(c_28342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17643,c_28333])).

tff(c_28343,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_10'),'#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_28344,plain,(
    m1_subset_1(k2_funct_1('#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_29047,plain,(
    ! [A_983,B_984,C_985] :
      ( k1_relset_1(A_983,B_984,C_985) = k1_relat_1(C_985)
      | ~ m1_subset_1(C_985,k1_zfmisc_1(k2_zfmisc_1(A_983,B_984))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_29079,plain,(
    k1_relset_1('#skF_9','#skF_8',k2_funct_1('#skF_10')) = k1_relat_1(k2_funct_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_28344,c_29047])).

tff(c_30067,plain,(
    ! [B_1049,C_1050,A_1051] :
      ( k1_xboole_0 = B_1049
      | v1_funct_2(C_1050,A_1051,B_1049)
      | k1_relset_1(A_1051,B_1049,C_1050) != A_1051
      | ~ m1_subset_1(C_1050,k1_zfmisc_1(k2_zfmisc_1(A_1051,B_1049))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30079,plain,
    ( k1_xboole_0 = '#skF_8'
    | v1_funct_2(k2_funct_1('#skF_10'),'#skF_9','#skF_8')
    | k1_relset_1('#skF_9','#skF_8',k2_funct_1('#skF_10')) != '#skF_9' ),
    inference(resolution,[status(thm)],[c_28344,c_30067])).

tff(c_30104,plain,
    ( k1_xboole_0 = '#skF_8'
    | v1_funct_2(k2_funct_1('#skF_10'),'#skF_9','#skF_8')
    | k1_relat_1(k2_funct_1('#skF_10')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29079,c_30079])).

tff(c_30105,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1(k2_funct_1('#skF_10')) != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_28343,c_30104])).

tff(c_30113,plain,(
    k1_relat_1(k2_funct_1('#skF_10')) != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_30105])).

tff(c_30116,plain,
    ( k2_relat_1('#skF_10') != '#skF_9'
    | ~ v2_funct_1('#skF_10')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_30113])).

tff(c_30119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_110,c_104,c_28996,c_30116])).

tff(c_30120,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_30105])).

tff(c_350,plain,
    ( k1_relat_1('#skF_10') != k1_xboole_0
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_342,c_44])).

tff(c_28346,plain,(
    k1_relat_1('#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_30164,plain,(
    k1_relat_1('#skF_10') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30120,c_28346])).

tff(c_28347,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_28997,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28996,c_28347])).

tff(c_30144,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30120,c_28997])).

tff(c_29082,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_106,c_29047])).

tff(c_74,plain,(
    ! [B_48,A_47,C_49] :
      ( k1_xboole_0 = B_48
      | k1_relset_1(A_47,B_48,C_49) = A_47
      | ~ v1_funct_2(C_49,A_47,B_48)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30412,plain,(
    ! [B_1056,A_1057,C_1058] :
      ( B_1056 = '#skF_8'
      | k1_relset_1(A_1057,B_1056,C_1058) = A_1057
      | ~ v1_funct_2(C_1058,A_1057,B_1056)
      | ~ m1_subset_1(C_1058,k1_zfmisc_1(k2_zfmisc_1(A_1057,B_1056))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30120,c_74])).

tff(c_30434,plain,
    ( '#skF_9' = '#skF_8'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_106,c_30412])).

tff(c_30449,plain,
    ( '#skF_9' = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_29082,c_30434])).

tff(c_30451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30164,c_30144,c_30449])).

tff(c_30452,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_30454,plain,(
    k1_relat_1('#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30452,c_28346])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30467,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30452,c_30452,c_40])).

tff(c_30489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30454,c_30467])).

tff(c_30490,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_30491,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_30520,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30490,c_30491])).

tff(c_30985,plain,(
    ! [A_1108] :
      ( k2_relat_1(k2_funct_1(A_1108)) = k1_relat_1(A_1108)
      | ~ v2_funct_1(A_1108)
      | ~ v1_funct_1(A_1108)
      | ~ v1_relat_1(A_1108) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_58,plain,(
    ! [C_40,A_38,B_39] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30518,plain,(
    v1_relat_1(k2_funct_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_28344,c_58])).

tff(c_30948,plain,(
    ! [A_1105] :
      ( k2_relat_1(A_1105) != '#skF_10'
      | A_1105 = '#skF_10'
      | ~ v1_relat_1(A_1105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30490,c_30490,c_42])).

tff(c_30968,plain,
    ( k2_relat_1(k2_funct_1('#skF_10')) != '#skF_10'
    | k2_funct_1('#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_30518,c_30948])).

tff(c_30976,plain,(
    k2_relat_1(k2_funct_1('#skF_10')) != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_30968])).

tff(c_30991,plain,
    ( k1_relat_1('#skF_10') != '#skF_10'
    | ~ v2_funct_1('#skF_10')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_30985,c_30976])).

tff(c_31001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_110,c_104,c_30520,c_30991])).

tff(c_31002,plain,(
    k2_funct_1('#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_30968])).

tff(c_30919,plain,(
    ! [A_1104] :
      ( k1_relat_1(A_1104) != '#skF_10'
      | A_1104 = '#skF_10'
      | ~ v1_relat_1(A_1104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30490,c_30490,c_44])).

tff(c_30939,plain,
    ( k1_relat_1(k2_funct_1('#skF_10')) != '#skF_10'
    | k2_funct_1('#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_30518,c_30919])).

tff(c_30947,plain,(
    k1_relat_1(k2_funct_1('#skF_10')) != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_30939])).

tff(c_31004,plain,(
    k1_relat_1('#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31002,c_30947])).

tff(c_31012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30520,c_31004])).

tff(c_31013,plain,(
    k2_funct_1('#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_30939])).

tff(c_31018,plain,(
    ~ v1_funct_2('#skF_10','#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31013,c_28343])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30503,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30490,c_30490,c_38])).

tff(c_31370,plain,(
    ! [A_1142,B_1143,C_1144] :
      ( k2_relset_1(A_1142,B_1143,C_1144) = k2_relat_1(C_1144)
      | ~ m1_subset_1(C_1144,k1_zfmisc_1(k2_zfmisc_1(A_1142,B_1143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_31395,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_106,c_31370])).

tff(c_31403,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_30503,c_31395])).

tff(c_30505,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30490,c_12])).

tff(c_31439,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31403,c_30505])).

tff(c_30501,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_10',B_12) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30490,c_30490,c_20])).

tff(c_31433,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_9',B_12) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31403,c_31403,c_30501])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30519,plain,(
    r1_tarski(k2_funct_1('#skF_10'),k2_zfmisc_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_28344,c_22])).

tff(c_31015,plain,(
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31013,c_30519])).

tff(c_30722,plain,(
    ! [C_1080,B_1081,A_1082] :
      ( r2_hidden(C_1080,B_1081)
      | ~ r2_hidden(C_1080,A_1082)
      | ~ r1_tarski(A_1082,B_1081) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_31256,plain,(
    ! [A_1131,B_1132,B_1133] :
      ( r2_hidden('#skF_2'(A_1131,B_1132),B_1133)
      | ~ r1_tarski(A_1131,B_1133)
      | r1_tarski(A_1131,B_1132) ) ),
    inference(resolution,[status(thm)],[c_10,c_30722])).

tff(c_31294,plain,(
    ! [B_1135,A_1136,B_1137] :
      ( ~ v1_xboole_0(B_1135)
      | ~ r1_tarski(A_1136,B_1135)
      | r1_tarski(A_1136,B_1137) ) ),
    inference(resolution,[status(thm)],[c_31256,c_2])).

tff(c_31307,plain,(
    ! [B_1137] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_8'))
      | r1_tarski('#skF_10',B_1137) ) ),
    inference(resolution,[status(thm)],[c_31015,c_31294])).

tff(c_31314,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_31307])).

tff(c_31546,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31433,c_31314])).

tff(c_31549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31439,c_31546])).

tff(c_31551,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_31307])).

tff(c_30686,plain,(
    ! [A_1076,B_1077] : m1_subset_1('#skF_7'(A_1076,B_1077),k1_zfmisc_1(k2_zfmisc_1(A_1076,B_1077))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_30701,plain,(
    ! [A_1076,B_1077] : r1_tarski('#skF_7'(A_1076,B_1077),k2_zfmisc_1(A_1076,B_1077)) ),
    inference(resolution,[status(thm)],[c_30686,c_22])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31088,plain,(
    ! [A_1112,B_1113] :
      ( r2_hidden('#skF_1'(A_1112),B_1113)
      | ~ r1_tarski(A_1112,B_1113)
      | v1_xboole_0(A_1112) ) ),
    inference(resolution,[status(thm)],[c_4,c_30722])).

tff(c_31113,plain,(
    ! [B_1115,A_1116] :
      ( ~ v1_xboole_0(B_1115)
      | ~ r1_tarski(A_1116,B_1115)
      | v1_xboole_0(A_1116) ) ),
    inference(resolution,[status(thm)],[c_31088,c_2])).

tff(c_31134,plain,(
    ! [A_1076,B_1077] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_1076,B_1077))
      | v1_xboole_0('#skF_7'(A_1076,B_1077)) ) ),
    inference(resolution,[status(thm)],[c_30701,c_31113])).

tff(c_31591,plain,(
    v1_xboole_0('#skF_7'('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_31551,c_31134])).

tff(c_30547,plain,(
    ! [A_1059,B_1060] :
      ( r2_hidden('#skF_2'(A_1059,B_1060),A_1059)
      | r1_tarski(A_1059,B_1060) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30551,plain,(
    ! [A_1059,B_1060] :
      ( ~ v1_xboole_0(A_1059)
      | r1_tarski(A_1059,B_1060) ) ),
    inference(resolution,[status(thm)],[c_30547,c_2])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30597,plain,(
    ! [A_1065] :
      ( A_1065 = '#skF_10'
      | ~ r1_tarski(A_1065,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30490,c_30490,c_14])).

tff(c_30605,plain,(
    ! [A_1059] :
      ( A_1059 = '#skF_10'
      | ~ v1_xboole_0(A_1059) ) ),
    inference(resolution,[status(thm)],[c_30551,c_30597])).

tff(c_31603,plain,(
    '#skF_7'('#skF_9','#skF_8') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_31591,c_30605])).

tff(c_80,plain,(
    ! [A_51,B_52] : v1_funct_2('#skF_7'(A_51,B_52),A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_31661,plain,(
    v1_funct_2('#skF_10','#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_31603,c_80])).

tff(c_31681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31018,c_31661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.25/5.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.40/5.04  
% 12.40/5.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.40/5.04  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_5 > #skF_4
% 12.40/5.04  
% 12.40/5.04  %Foreground sorts:
% 12.40/5.04  
% 12.40/5.04  
% 12.40/5.04  %Background operators:
% 12.40/5.04  
% 12.40/5.04  
% 12.40/5.04  %Foreground operators:
% 12.40/5.04  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.40/5.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.40/5.04  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.40/5.04  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.40/5.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.40/5.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.40/5.04  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 12.40/5.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.40/5.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.40/5.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.40/5.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.40/5.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.40/5.04  tff('#skF_10', type, '#skF_10': $i).
% 12.40/5.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.40/5.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.40/5.04  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 12.40/5.04  tff('#skF_9', type, '#skF_9': $i).
% 12.40/5.04  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.40/5.04  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.40/5.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.40/5.04  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.40/5.04  tff('#skF_8', type, '#skF_8': $i).
% 12.40/5.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.40/5.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.40/5.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.40/5.04  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.40/5.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.40/5.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.40/5.04  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.40/5.04  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 12.40/5.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.40/5.04  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 12.40/5.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.40/5.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.40/5.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.40/5.04  
% 12.40/5.07  tff(f_170, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 12.40/5.07  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.40/5.07  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.40/5.07  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 12.40/5.07  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.40/5.07  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.40/5.07  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 12.40/5.07  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.40/5.07  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 12.40/5.07  tff(f_153, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 12.40/5.07  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 12.40/5.07  tff(f_61, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 12.40/5.07  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.40/5.07  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.40/5.07  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.40/5.07  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 12.40/5.07  tff(f_141, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 12.40/5.07  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 12.40/5.07  tff(c_106, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.40/5.07  tff(c_324, plain, (![C_92, A_93, B_94]: (v1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.40/5.07  tff(c_342, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_106, c_324])).
% 12.40/5.07  tff(c_110, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.40/5.07  tff(c_104, plain, (v2_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.40/5.07  tff(c_102, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.40/5.07  tff(c_28964, plain, (![A_980, B_981, C_982]: (k2_relset_1(A_980, B_981, C_982)=k2_relat_1(C_982) | ~m1_subset_1(C_982, k1_zfmisc_1(k2_zfmisc_1(A_980, B_981))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.40/5.07  tff(c_28983, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_106, c_28964])).
% 12.40/5.07  tff(c_28996, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_28983])).
% 12.40/5.07  tff(c_56, plain, (![A_37]: (k1_relat_1(k2_funct_1(A_37))=k2_relat_1(A_37) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.40/5.07  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.40/5.07  tff(c_46, plain, (![A_35]: (v1_funct_1(k2_funct_1(A_35)) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.40/5.07  tff(c_100, plain, (~m1_subset_1(k2_funct_1('#skF_10'), k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8'))) | ~v1_funct_2(k2_funct_1('#skF_10'), '#skF_9', '#skF_8') | ~v1_funct_1(k2_funct_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.40/5.07  tff(c_213, plain, (~v1_funct_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_100])).
% 12.40/5.07  tff(c_216, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_46, c_213])).
% 12.40/5.07  tff(c_219, plain, (~v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_216])).
% 12.40/5.07  tff(c_242, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.40/5.07  tff(c_252, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_106, c_242])).
% 12.40/5.07  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_219, c_252])).
% 12.40/5.07  tff(c_264, plain, (~v1_funct_2(k2_funct_1('#skF_10'), '#skF_9', '#skF_8') | ~m1_subset_1(k2_funct_1('#skF_10'), k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(splitRight, [status(thm)], [c_100])).
% 12.40/5.07  tff(c_356, plain, (~m1_subset_1(k2_funct_1('#skF_10'), k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(splitLeft, [status(thm)], [c_264])).
% 12.40/5.07  tff(c_1059, plain, (![A_178, B_179, C_180]: (k2_relset_1(A_178, B_179, C_180)=k2_relat_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.40/5.07  tff(c_1075, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_106, c_1059])).
% 12.40/5.07  tff(c_1087, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1075])).
% 12.40/5.07  tff(c_48, plain, (![A_35]: (v1_relat_1(k2_funct_1(A_35)) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.40/5.07  tff(c_265, plain, (v1_funct_1(k2_funct_1('#skF_10'))), inference(splitRight, [status(thm)], [c_100])).
% 12.40/5.07  tff(c_42, plain, (![A_34]: (k2_relat_1(A_34)!=k1_xboole_0 | k1_xboole_0=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.40/5.07  tff(c_349, plain, (k2_relat_1('#skF_10')!=k1_xboole_0 | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_342, c_42])).
% 12.40/5.07  tff(c_358, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_349])).
% 12.40/5.07  tff(c_1088, plain, (k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_358])).
% 12.40/5.07  tff(c_108, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.40/5.07  tff(c_1010, plain, (![A_174, B_175, C_176]: (k1_relset_1(A_174, B_175, C_176)=k1_relat_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.40/5.07  tff(c_1037, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_106, c_1010])).
% 12.40/5.07  tff(c_3620, plain, (![B_260, A_261, C_262]: (k1_xboole_0=B_260 | k1_relset_1(A_261, B_260, C_262)=A_261 | ~v1_funct_2(C_262, A_261, B_260) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_261, B_260))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.40/5.07  tff(c_3639, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_106, c_3620])).
% 12.40/5.07  tff(c_3659, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_1037, c_3639])).
% 12.40/5.07  tff(c_3660, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_1088, c_3659])).
% 12.40/5.07  tff(c_668, plain, (![A_135]: (k2_relat_1(k2_funct_1(A_135))=k1_relat_1(A_135) | ~v2_funct_1(A_135) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.40/5.07  tff(c_96, plain, (![A_55]: (v1_funct_2(A_55, k1_relat_1(A_55), k2_relat_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_153])).
% 12.40/5.07  tff(c_15264, plain, (![A_499]: (v1_funct_2(k2_funct_1(A_499), k1_relat_1(k2_funct_1(A_499)), k1_relat_1(A_499)) | ~v1_funct_1(k2_funct_1(A_499)) | ~v1_relat_1(k2_funct_1(A_499)) | ~v2_funct_1(A_499) | ~v1_funct_1(A_499) | ~v1_relat_1(A_499))), inference(superposition, [status(thm), theory('equality')], [c_668, c_96])).
% 12.40/5.07  tff(c_15273, plain, (v1_funct_2(k2_funct_1('#skF_10'), k1_relat_1(k2_funct_1('#skF_10')), '#skF_8') | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_3660, c_15264])).
% 12.40/5.07  tff(c_15286, plain, (v1_funct_2(k2_funct_1('#skF_10'), k1_relat_1(k2_funct_1('#skF_10')), '#skF_8') | ~v1_relat_1(k2_funct_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_110, c_104, c_265, c_15273])).
% 12.40/5.07  tff(c_15465, plain, (~v1_relat_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_15286])).
% 12.40/5.07  tff(c_15468, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_48, c_15465])).
% 12.40/5.07  tff(c_15472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_110, c_15468])).
% 12.40/5.07  tff(c_15474, plain, (v1_relat_1(k2_funct_1('#skF_10'))), inference(splitRight, [status(thm)], [c_15286])).
% 12.40/5.07  tff(c_54, plain, (![A_37]: (k2_relat_1(k2_funct_1(A_37))=k1_relat_1(A_37) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.40/5.07  tff(c_882, plain, (![A_166]: (m1_subset_1(A_166, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_166), k2_relat_1(A_166)))) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166))), inference(cnfTransformation, [status(thm)], [f_153])).
% 12.40/5.07  tff(c_16399, plain, (![A_520]: (m1_subset_1(k2_funct_1(A_520), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_520)), k1_relat_1(A_520)))) | ~v1_funct_1(k2_funct_1(A_520)) | ~v1_relat_1(k2_funct_1(A_520)) | ~v2_funct_1(A_520) | ~v1_funct_1(A_520) | ~v1_relat_1(A_520))), inference(superposition, [status(thm), theory('equality')], [c_54, c_882])).
% 12.40/5.07  tff(c_16426, plain, (m1_subset_1(k2_funct_1('#skF_10'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_10')), '#skF_8'))) | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_3660, c_16399])).
% 12.40/5.07  tff(c_16446, plain, (m1_subset_1(k2_funct_1('#skF_10'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_10')), '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_110, c_104, c_15474, c_265, c_16426])).
% 12.40/5.07  tff(c_16469, plain, (m1_subset_1(k2_funct_1('#skF_10'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_10'), '#skF_8'))) | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_56, c_16446])).
% 12.40/5.07  tff(c_16483, plain, (m1_subset_1(k2_funct_1('#skF_10'), k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_110, c_104, c_1087, c_16469])).
% 12.40/5.07  tff(c_16485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_356, c_16483])).
% 12.40/5.07  tff(c_16486, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_349])).
% 12.40/5.07  tff(c_16487, plain, (k2_relat_1('#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_349])).
% 12.40/5.07  tff(c_16509, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_16486, c_16487])).
% 12.40/5.07  tff(c_17087, plain, (![A_585, B_586, C_587]: (k2_relset_1(A_585, B_586, C_587)=k2_relat_1(C_587) | ~m1_subset_1(C_587, k1_zfmisc_1(k2_zfmisc_1(A_585, B_586))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.40/5.07  tff(c_17106, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_106, c_17087])).
% 12.40/5.07  tff(c_17111, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_16509, c_102, c_17106])).
% 12.40/5.07  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.40/5.07  tff(c_16501, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_16486, c_12])).
% 12.40/5.07  tff(c_17141, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_17111, c_16501])).
% 12.40/5.07  tff(c_17140, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_17111, c_17111, c_16509])).
% 12.40/5.07  tff(c_17563, plain, (![A_609, C_610]: (r2_hidden(k4_tarski('#skF_6'(A_609, k2_relat_1(A_609), C_610), C_610), A_609) | ~r2_hidden(C_610, k2_relat_1(A_609)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.40/5.07  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.40/5.07  tff(c_17594, plain, (![A_612, C_613]: (~v1_xboole_0(A_612) | ~r2_hidden(C_613, k2_relat_1(A_612)))), inference(resolution, [status(thm)], [c_17563, c_2])).
% 12.40/5.07  tff(c_17601, plain, (![C_613]: (~v1_xboole_0('#skF_9') | ~r2_hidden(C_613, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_17140, c_17594])).
% 12.40/5.07  tff(c_17623, plain, (![C_614]: (~r2_hidden(C_614, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_17141, c_17601])).
% 12.40/5.07  tff(c_17643, plain, (![B_6]: (r1_tarski('#skF_9', B_6))), inference(resolution, [status(thm)], [c_10, c_17623])).
% 12.40/5.07  tff(c_17143, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_17111, c_342])).
% 12.40/5.07  tff(c_17150, plain, (v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_17111, c_110])).
% 12.40/5.07  tff(c_17149, plain, (v2_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_17111, c_104])).
% 12.40/5.07  tff(c_17145, plain, (v1_funct_1(k2_funct_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_17111, c_265])).
% 12.40/5.07  tff(c_16983, plain, (![A_572]: (k1_relat_1(k2_funct_1(A_572))=k2_relat_1(A_572) | ~v2_funct_1(A_572) | ~v1_funct_1(A_572) | ~v1_relat_1(A_572))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.40/5.07  tff(c_27456, plain, (![A_900]: (v1_funct_2(k2_funct_1(A_900), k2_relat_1(A_900), k2_relat_1(k2_funct_1(A_900))) | ~v1_funct_1(k2_funct_1(A_900)) | ~v1_relat_1(k2_funct_1(A_900)) | ~v2_funct_1(A_900) | ~v1_funct_1(A_900) | ~v1_relat_1(A_900))), inference(superposition, [status(thm), theory('equality')], [c_16983, c_96])).
% 12.40/5.07  tff(c_27489, plain, (v1_funct_2(k2_funct_1('#skF_9'), '#skF_9', k2_relat_1(k2_funct_1('#skF_9'))) | ~v1_funct_1(k2_funct_1('#skF_9')) | ~v1_relat_1(k2_funct_1('#skF_9')) | ~v2_funct_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_17140, c_27456])).
% 12.40/5.07  tff(c_27497, plain, (v1_funct_2(k2_funct_1('#skF_9'), '#skF_9', k2_relat_1(k2_funct_1('#skF_9'))) | ~v1_relat_1(k2_funct_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_17143, c_17150, c_17149, c_17145, c_27489])).
% 12.40/5.07  tff(c_28237, plain, (~v1_relat_1(k2_funct_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_27497])).
% 12.40/5.07  tff(c_28240, plain, (~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_28237])).
% 12.40/5.07  tff(c_28244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17143, c_17150, c_28240])).
% 12.40/5.07  tff(c_28246, plain, (v1_relat_1(k2_funct_1('#skF_9'))), inference(splitRight, [status(thm)], [c_27497])).
% 12.40/5.07  tff(c_44, plain, (![A_34]: (k1_relat_1(A_34)!=k1_xboole_0 | k1_xboole_0=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.40/5.07  tff(c_16495, plain, (![A_34]: (k1_relat_1(A_34)!='#skF_10' | A_34='#skF_10' | ~v1_relat_1(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_16486, c_16486, c_44])).
% 12.40/5.07  tff(c_17116, plain, (![A_34]: (k1_relat_1(A_34)!='#skF_9' | A_34='#skF_9' | ~v1_relat_1(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_17111, c_17111, c_16495])).
% 12.40/5.07  tff(c_28253, plain, (k1_relat_1(k2_funct_1('#skF_9'))!='#skF_9' | k2_funct_1('#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_28246, c_17116])).
% 12.40/5.07  tff(c_28269, plain, (k1_relat_1(k2_funct_1('#skF_9'))!='#skF_9'), inference(splitLeft, [status(thm)], [c_28253])).
% 12.40/5.07  tff(c_28324, plain, (k2_relat_1('#skF_9')!='#skF_9' | ~v2_funct_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_56, c_28269])).
% 12.40/5.07  tff(c_28327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17143, c_17150, c_17149, c_17140, c_28324])).
% 12.40/5.07  tff(c_28328, plain, (k2_funct_1('#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_28253])).
% 12.40/5.07  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.40/5.07  tff(c_20, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.40/5.07  tff(c_16497, plain, (![B_12]: (k2_zfmisc_1('#skF_10', B_12)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_16486, c_16486, c_20])).
% 12.40/5.07  tff(c_17133, plain, (![B_12]: (k2_zfmisc_1('#skF_9', B_12)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_17111, c_17111, c_16497])).
% 12.40/5.07  tff(c_17137, plain, (~m1_subset_1(k2_funct_1('#skF_9'), k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_17111, c_356])).
% 12.40/5.07  tff(c_17541, plain, (~m1_subset_1(k2_funct_1('#skF_9'), k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_17133, c_17137])).
% 12.40/5.07  tff(c_17545, plain, (~r1_tarski(k2_funct_1('#skF_9'), '#skF_9')), inference(resolution, [status(thm)], [c_24, c_17541])).
% 12.40/5.07  tff(c_28333, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28328, c_17545])).
% 12.40/5.07  tff(c_28342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17643, c_28333])).
% 12.40/5.07  tff(c_28343, plain, (~v1_funct_2(k2_funct_1('#skF_10'), '#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_264])).
% 12.40/5.07  tff(c_28344, plain, (m1_subset_1(k2_funct_1('#skF_10'), k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(splitRight, [status(thm)], [c_264])).
% 12.40/5.07  tff(c_29047, plain, (![A_983, B_984, C_985]: (k1_relset_1(A_983, B_984, C_985)=k1_relat_1(C_985) | ~m1_subset_1(C_985, k1_zfmisc_1(k2_zfmisc_1(A_983, B_984))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.40/5.07  tff(c_29079, plain, (k1_relset_1('#skF_9', '#skF_8', k2_funct_1('#skF_10'))=k1_relat_1(k2_funct_1('#skF_10'))), inference(resolution, [status(thm)], [c_28344, c_29047])).
% 12.40/5.07  tff(c_30067, plain, (![B_1049, C_1050, A_1051]: (k1_xboole_0=B_1049 | v1_funct_2(C_1050, A_1051, B_1049) | k1_relset_1(A_1051, B_1049, C_1050)!=A_1051 | ~m1_subset_1(C_1050, k1_zfmisc_1(k2_zfmisc_1(A_1051, B_1049))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.40/5.07  tff(c_30079, plain, (k1_xboole_0='#skF_8' | v1_funct_2(k2_funct_1('#skF_10'), '#skF_9', '#skF_8') | k1_relset_1('#skF_9', '#skF_8', k2_funct_1('#skF_10'))!='#skF_9'), inference(resolution, [status(thm)], [c_28344, c_30067])).
% 12.40/5.07  tff(c_30104, plain, (k1_xboole_0='#skF_8' | v1_funct_2(k2_funct_1('#skF_10'), '#skF_9', '#skF_8') | k1_relat_1(k2_funct_1('#skF_10'))!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_29079, c_30079])).
% 12.40/5.07  tff(c_30105, plain, (k1_xboole_0='#skF_8' | k1_relat_1(k2_funct_1('#skF_10'))!='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_28343, c_30104])).
% 12.40/5.07  tff(c_30113, plain, (k1_relat_1(k2_funct_1('#skF_10'))!='#skF_9'), inference(splitLeft, [status(thm)], [c_30105])).
% 12.40/5.07  tff(c_30116, plain, (k2_relat_1('#skF_10')!='#skF_9' | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_56, c_30113])).
% 12.40/5.07  tff(c_30119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_110, c_104, c_28996, c_30116])).
% 12.40/5.07  tff(c_30120, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_30105])).
% 12.40/5.07  tff(c_350, plain, (k1_relat_1('#skF_10')!=k1_xboole_0 | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_342, c_44])).
% 12.40/5.07  tff(c_28346, plain, (k1_relat_1('#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_350])).
% 12.40/5.07  tff(c_30164, plain, (k1_relat_1('#skF_10')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_30120, c_28346])).
% 12.40/5.07  tff(c_28347, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_349])).
% 12.40/5.07  tff(c_28997, plain, (k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_28996, c_28347])).
% 12.40/5.07  tff(c_30144, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_30120, c_28997])).
% 12.40/5.07  tff(c_29082, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_106, c_29047])).
% 12.40/5.07  tff(c_74, plain, (![B_48, A_47, C_49]: (k1_xboole_0=B_48 | k1_relset_1(A_47, B_48, C_49)=A_47 | ~v1_funct_2(C_49, A_47, B_48) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.40/5.07  tff(c_30412, plain, (![B_1056, A_1057, C_1058]: (B_1056='#skF_8' | k1_relset_1(A_1057, B_1056, C_1058)=A_1057 | ~v1_funct_2(C_1058, A_1057, B_1056) | ~m1_subset_1(C_1058, k1_zfmisc_1(k2_zfmisc_1(A_1057, B_1056))))), inference(demodulation, [status(thm), theory('equality')], [c_30120, c_74])).
% 12.40/5.07  tff(c_30434, plain, ('#skF_9'='#skF_8' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_106, c_30412])).
% 12.40/5.07  tff(c_30449, plain, ('#skF_9'='#skF_8' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_29082, c_30434])).
% 12.40/5.07  tff(c_30451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30164, c_30144, c_30449])).
% 12.40/5.07  tff(c_30452, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_349])).
% 12.40/5.07  tff(c_30454, plain, (k1_relat_1('#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_30452, c_28346])).
% 12.40/5.07  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.40/5.07  tff(c_30467, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_30452, c_30452, c_40])).
% 12.40/5.07  tff(c_30489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30454, c_30467])).
% 12.40/5.07  tff(c_30490, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_350])).
% 12.40/5.07  tff(c_30491, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_350])).
% 12.40/5.07  tff(c_30520, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_30490, c_30491])).
% 12.40/5.07  tff(c_30985, plain, (![A_1108]: (k2_relat_1(k2_funct_1(A_1108))=k1_relat_1(A_1108) | ~v2_funct_1(A_1108) | ~v1_funct_1(A_1108) | ~v1_relat_1(A_1108))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.40/5.07  tff(c_58, plain, (![C_40, A_38, B_39]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.40/5.07  tff(c_30518, plain, (v1_relat_1(k2_funct_1('#skF_10'))), inference(resolution, [status(thm)], [c_28344, c_58])).
% 12.40/5.07  tff(c_30948, plain, (![A_1105]: (k2_relat_1(A_1105)!='#skF_10' | A_1105='#skF_10' | ~v1_relat_1(A_1105))), inference(demodulation, [status(thm), theory('equality')], [c_30490, c_30490, c_42])).
% 12.40/5.07  tff(c_30968, plain, (k2_relat_1(k2_funct_1('#skF_10'))!='#skF_10' | k2_funct_1('#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_30518, c_30948])).
% 12.40/5.07  tff(c_30976, plain, (k2_relat_1(k2_funct_1('#skF_10'))!='#skF_10'), inference(splitLeft, [status(thm)], [c_30968])).
% 12.40/5.07  tff(c_30991, plain, (k1_relat_1('#skF_10')!='#skF_10' | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_30985, c_30976])).
% 12.40/5.07  tff(c_31001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_110, c_104, c_30520, c_30991])).
% 12.40/5.07  tff(c_31002, plain, (k2_funct_1('#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_30968])).
% 12.40/5.07  tff(c_30919, plain, (![A_1104]: (k1_relat_1(A_1104)!='#skF_10' | A_1104='#skF_10' | ~v1_relat_1(A_1104))), inference(demodulation, [status(thm), theory('equality')], [c_30490, c_30490, c_44])).
% 12.40/5.07  tff(c_30939, plain, (k1_relat_1(k2_funct_1('#skF_10'))!='#skF_10' | k2_funct_1('#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_30518, c_30919])).
% 12.40/5.07  tff(c_30947, plain, (k1_relat_1(k2_funct_1('#skF_10'))!='#skF_10'), inference(splitLeft, [status(thm)], [c_30939])).
% 12.40/5.07  tff(c_31004, plain, (k1_relat_1('#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_31002, c_30947])).
% 12.40/5.07  tff(c_31012, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30520, c_31004])).
% 12.40/5.07  tff(c_31013, plain, (k2_funct_1('#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_30939])).
% 12.40/5.07  tff(c_31018, plain, (~v1_funct_2('#skF_10', '#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_31013, c_28343])).
% 12.40/5.07  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.40/5.07  tff(c_30503, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_30490, c_30490, c_38])).
% 12.40/5.07  tff(c_31370, plain, (![A_1142, B_1143, C_1144]: (k2_relset_1(A_1142, B_1143, C_1144)=k2_relat_1(C_1144) | ~m1_subset_1(C_1144, k1_zfmisc_1(k2_zfmisc_1(A_1142, B_1143))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.40/5.07  tff(c_31395, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_106, c_31370])).
% 12.40/5.07  tff(c_31403, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_30503, c_31395])).
% 12.40/5.07  tff(c_30505, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_30490, c_12])).
% 12.40/5.07  tff(c_31439, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_31403, c_30505])).
% 12.40/5.07  tff(c_30501, plain, (![B_12]: (k2_zfmisc_1('#skF_10', B_12)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_30490, c_30490, c_20])).
% 12.40/5.07  tff(c_31433, plain, (![B_12]: (k2_zfmisc_1('#skF_9', B_12)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_31403, c_31403, c_30501])).
% 12.40/5.07  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.40/5.07  tff(c_30519, plain, (r1_tarski(k2_funct_1('#skF_10'), k2_zfmisc_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_28344, c_22])).
% 12.40/5.07  tff(c_31015, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_31013, c_30519])).
% 12.40/5.07  tff(c_30722, plain, (![C_1080, B_1081, A_1082]: (r2_hidden(C_1080, B_1081) | ~r2_hidden(C_1080, A_1082) | ~r1_tarski(A_1082, B_1081))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.40/5.07  tff(c_31256, plain, (![A_1131, B_1132, B_1133]: (r2_hidden('#skF_2'(A_1131, B_1132), B_1133) | ~r1_tarski(A_1131, B_1133) | r1_tarski(A_1131, B_1132))), inference(resolution, [status(thm)], [c_10, c_30722])).
% 12.40/5.07  tff(c_31294, plain, (![B_1135, A_1136, B_1137]: (~v1_xboole_0(B_1135) | ~r1_tarski(A_1136, B_1135) | r1_tarski(A_1136, B_1137))), inference(resolution, [status(thm)], [c_31256, c_2])).
% 12.40/5.07  tff(c_31307, plain, (![B_1137]: (~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_8')) | r1_tarski('#skF_10', B_1137))), inference(resolution, [status(thm)], [c_31015, c_31294])).
% 12.40/5.07  tff(c_31314, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_8'))), inference(splitLeft, [status(thm)], [c_31307])).
% 12.40/5.07  tff(c_31546, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_31433, c_31314])).
% 12.40/5.07  tff(c_31549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31439, c_31546])).
% 12.40/5.07  tff(c_31551, plain, (v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_8'))), inference(splitRight, [status(thm)], [c_31307])).
% 12.40/5.07  tff(c_30686, plain, (![A_1076, B_1077]: (m1_subset_1('#skF_7'(A_1076, B_1077), k1_zfmisc_1(k2_zfmisc_1(A_1076, B_1077))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 12.40/5.07  tff(c_30701, plain, (![A_1076, B_1077]: (r1_tarski('#skF_7'(A_1076, B_1077), k2_zfmisc_1(A_1076, B_1077)))), inference(resolution, [status(thm)], [c_30686, c_22])).
% 12.40/5.07  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.40/5.07  tff(c_31088, plain, (![A_1112, B_1113]: (r2_hidden('#skF_1'(A_1112), B_1113) | ~r1_tarski(A_1112, B_1113) | v1_xboole_0(A_1112))), inference(resolution, [status(thm)], [c_4, c_30722])).
% 12.40/5.07  tff(c_31113, plain, (![B_1115, A_1116]: (~v1_xboole_0(B_1115) | ~r1_tarski(A_1116, B_1115) | v1_xboole_0(A_1116))), inference(resolution, [status(thm)], [c_31088, c_2])).
% 12.40/5.07  tff(c_31134, plain, (![A_1076, B_1077]: (~v1_xboole_0(k2_zfmisc_1(A_1076, B_1077)) | v1_xboole_0('#skF_7'(A_1076, B_1077)))), inference(resolution, [status(thm)], [c_30701, c_31113])).
% 12.40/5.07  tff(c_31591, plain, (v1_xboole_0('#skF_7'('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_31551, c_31134])).
% 12.40/5.07  tff(c_30547, plain, (![A_1059, B_1060]: (r2_hidden('#skF_2'(A_1059, B_1060), A_1059) | r1_tarski(A_1059, B_1060))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.40/5.07  tff(c_30551, plain, (![A_1059, B_1060]: (~v1_xboole_0(A_1059) | r1_tarski(A_1059, B_1060))), inference(resolution, [status(thm)], [c_30547, c_2])).
% 12.40/5.07  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.40/5.07  tff(c_30597, plain, (![A_1065]: (A_1065='#skF_10' | ~r1_tarski(A_1065, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_30490, c_30490, c_14])).
% 12.40/5.07  tff(c_30605, plain, (![A_1059]: (A_1059='#skF_10' | ~v1_xboole_0(A_1059))), inference(resolution, [status(thm)], [c_30551, c_30597])).
% 12.40/5.07  tff(c_31603, plain, ('#skF_7'('#skF_9', '#skF_8')='#skF_10'), inference(resolution, [status(thm)], [c_31591, c_30605])).
% 12.40/5.07  tff(c_80, plain, (![A_51, B_52]: (v1_funct_2('#skF_7'(A_51, B_52), A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_141])).
% 12.40/5.07  tff(c_31661, plain, (v1_funct_2('#skF_10', '#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_31603, c_80])).
% 12.40/5.07  tff(c_31681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31018, c_31661])).
% 12.40/5.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.40/5.07  
% 12.40/5.07  Inference rules
% 12.40/5.07  ----------------------
% 12.40/5.07  #Ref     : 0
% 12.40/5.07  #Sup     : 8016
% 12.40/5.07  #Fact    : 0
% 12.40/5.07  #Define  : 0
% 12.40/5.07  #Split   : 38
% 12.40/5.07  #Chain   : 0
% 12.40/5.07  #Close   : 0
% 12.40/5.07  
% 12.40/5.07  Ordering : KBO
% 12.40/5.07  
% 12.40/5.07  Simplification rules
% 12.40/5.07  ----------------------
% 12.40/5.07  #Subsume      : 3423
% 12.40/5.07  #Demod        : 6439
% 12.40/5.07  #Tautology    : 2557
% 12.40/5.07  #SimpNegUnit  : 89
% 12.40/5.07  #BackRed      : 241
% 12.40/5.07  
% 12.40/5.07  #Partial instantiations: 0
% 12.40/5.07  #Strategies tried      : 1
% 12.40/5.07  
% 12.40/5.07  Timing (in seconds)
% 12.40/5.07  ----------------------
% 12.40/5.07  Preprocessing        : 0.36
% 12.40/5.07  Parsing              : 0.18
% 12.40/5.07  CNF conversion       : 0.03
% 12.40/5.07  Main loop            : 3.88
% 12.40/5.07  Inferencing          : 0.91
% 12.40/5.07  Reduction            : 1.33
% 12.40/5.07  Demodulation         : 1.01
% 12.40/5.07  BG Simplification    : 0.09
% 12.40/5.07  Subsumption          : 1.33
% 12.40/5.07  Abstraction          : 0.13
% 12.40/5.07  MUC search           : 0.00
% 12.40/5.07  Cooper               : 0.00
% 12.40/5.07  Total                : 4.30
% 12.40/5.07  Index Insertion      : 0.00
% 12.40/5.07  Index Deletion       : 0.00
% 12.40/5.07  Index Matching       : 0.00
% 12.40/5.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
