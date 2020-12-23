%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:18 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 720 expanded)
%              Number of leaves         :   44 ( 239 expanded)
%              Depth                    :   12
%              Number of atoms          :  199 (1625 expanded)
%              Number of equality atoms :   77 ( 726 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_146,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_50,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_102,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_965,plain,(
    ! [A_171,B_172,C_173] :
      ( k2_relset_1(A_171,B_172,C_173) = k2_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_986,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_102,c_965])).

tff(c_1023,plain,(
    ! [A_180,B_181,C_182] :
      ( m1_subset_1(k2_relset_1(A_180,B_181,C_182),k1_zfmisc_1(B_181))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1059,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_1023])).

tff(c_1075,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1059])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1089,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1075,c_18])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_429,plain,(
    ! [C_106,A_107,B_108] :
      ( v1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_580,plain,(
    ! [A_127,A_128,B_129] :
      ( v1_relat_1(A_127)
      | ~ r1_tarski(A_127,k2_zfmisc_1(A_128,B_129)) ) ),
    inference(resolution,[status(thm)],[c_20,c_429])).

tff(c_596,plain,(
    ! [A_128,B_129] : v1_relat_1(k2_zfmisc_1(A_128,B_129)) ),
    inference(resolution,[status(thm)],[c_6,c_580])).

tff(c_376,plain,(
    ! [B_102,A_103] :
      ( v1_relat_1(B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_103))
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_388,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_102,c_376])).

tff(c_428,plain,(
    ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_428])).

tff(c_600,plain,(
    v1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_106,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_100,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_120,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_104,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_807,plain,(
    ! [A_155,B_156,C_157] :
      ( k1_relset_1(A_155,B_156,C_157) = k1_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_822,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_102,c_807])).

tff(c_3047,plain,(
    ! [B_348,A_349,C_350] :
      ( k1_xboole_0 = B_348
      | k1_relset_1(A_349,B_348,C_350) = A_349
      | ~ v1_funct_2(C_350,A_349,B_348)
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_349,B_348))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3074,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_102,c_3047])).

tff(c_3082,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_822,c_3074])).

tff(c_3083,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_3082])).

tff(c_62,plain,(
    ! [E_60,B_42] :
      ( r2_hidden(E_60,k1_funct_2(k1_relat_1(E_60),B_42))
      | ~ r1_tarski(k2_relat_1(E_60),B_42)
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3089,plain,(
    ! [B_42] :
      ( r2_hidden('#skF_8',k1_funct_2('#skF_6',B_42))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_42)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3083,c_62])).

tff(c_3099,plain,(
    ! [B_351] :
      ( r2_hidden('#skF_8',k1_funct_2('#skF_6',B_351))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_106,c_3089])).

tff(c_98,plain,(
    ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_3104,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_3099,c_98])).

tff(c_3109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_3104])).

tff(c_3110,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_3111,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_3118,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3110,c_3111])).

tff(c_3144,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3118,c_102])).

tff(c_3330,plain,(
    ! [C_387,A_388,B_389] :
      ( v1_relat_1(C_387)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(k2_zfmisc_1(A_388,B_389))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3343,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_3144,c_3330])).

tff(c_14,plain,(
    ! [A_8] : v1_xboole_0('#skF_1'(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3147,plain,(
    ! [B_357,A_358] :
      ( ~ v1_xboole_0(B_357)
      | B_357 = A_358
      | ~ v1_xboole_0(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3151,plain,(
    ! [A_359,A_360] :
      ( A_359 = '#skF_1'(A_360)
      | ~ v1_xboole_0(A_359) ) ),
    inference(resolution,[status(thm)],[c_14,c_3147])).

tff(c_3155,plain,(
    ! [A_362,A_361] : '#skF_1'(A_362) = '#skF_1'(A_361) ),
    inference(resolution,[status(thm)],[c_14,c_3151])).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1('#skF_1'(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3166,plain,(
    ! [A_362,A_361] : m1_subset_1('#skF_1'(A_362),k1_zfmisc_1(A_361)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3155,c_16])).

tff(c_3222,plain,(
    ! [A_372,B_373] :
      ( r1_tarski(A_372,B_373)
      | ~ m1_subset_1(A_372,k1_zfmisc_1(B_373)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3239,plain,(
    ! [A_374,A_375] : r1_tarski('#skF_1'(A_374),A_375) ),
    inference(resolution,[status(thm)],[c_3166,c_3222])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3272,plain,(
    ! [A_381,A_382] : k3_xboole_0('#skF_1'(A_381),A_382) = '#skF_1'(A_381) ),
    inference(resolution,[status(thm)],[c_3239,c_8])).

tff(c_10,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3131,plain,(
    ! [A_5] : k3_xboole_0(A_5,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3110,c_3110,c_10])).

tff(c_3282,plain,(
    ! [A_381] : '#skF_1'(A_381) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3272,c_3131])).

tff(c_3306,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3282,c_14])).

tff(c_3572,plain,(
    ! [C_413,B_414,A_415] :
      ( v1_xboole_0(C_413)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(B_414,A_415)))
      | ~ v1_xboole_0(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3583,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_3144,c_3572])).

tff(c_3589,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3306,c_3583])).

tff(c_3150,plain,(
    ! [A_358,A_8] :
      ( A_358 = '#skF_1'(A_8)
      | ~ v1_xboole_0(A_358) ) ),
    inference(resolution,[status(thm)],[c_14,c_3147])).

tff(c_3305,plain,(
    ! [A_358] :
      ( A_358 = '#skF_6'
      | ~ v1_xboole_0(A_358) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3282,c_3150])).

tff(c_3595,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3589,c_3305])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3112,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3110,c_3110,c_24])).

tff(c_3623,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3595,c_3595,c_3112])).

tff(c_28,plain,(
    ! [A_15] :
      ( k2_relat_1(A_15) != k1_xboole_0
      | k1_xboole_0 = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3217,plain,(
    ! [A_15] :
      ( k2_relat_1(A_15) != '#skF_6'
      | A_15 = '#skF_6'
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3110,c_3110,c_28])).

tff(c_3385,plain,
    ( k2_relat_1('#skF_8') != '#skF_6'
    | '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3343,c_3217])).

tff(c_3427,plain,(
    k2_relat_1('#skF_8') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3385])).

tff(c_3602,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3595,c_3427])).

tff(c_3681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3623,c_3602])).

tff(c_3682,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3385])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3113,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3110,c_3110,c_26])).

tff(c_3718,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3682,c_3682,c_3113])).

tff(c_30,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) != k1_xboole_0
      | k1_xboole_0 = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3220,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) != '#skF_6'
      | A_15 = '#skF_6'
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3110,c_3110,c_30])).

tff(c_3384,plain,
    ( k1_relat_1('#skF_8') != '#skF_6'
    | '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3343,c_3220])).

tff(c_3412,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3384])).

tff(c_3700,plain,(
    k1_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3682,c_3412])).

tff(c_3749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_3700])).

tff(c_3750,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3384])).

tff(c_3236,plain,(
    ! [A_362,A_361] : r1_tarski('#skF_1'(A_362),A_361) ),
    inference(resolution,[status(thm)],[c_3166,c_3222])).

tff(c_3302,plain,(
    ! [A_361] : r1_tarski('#skF_6',A_361) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3282,c_3236])).

tff(c_3770,plain,(
    ! [A_361] : r1_tarski('#skF_8',A_361) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3750,c_3302])).

tff(c_3786,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3750,c_3750,c_3112])).

tff(c_3751,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3384])).

tff(c_3805,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3750,c_3751])).

tff(c_4361,plain,(
    ! [E_498,B_499] :
      ( r2_hidden(E_498,k1_funct_2(k1_relat_1(E_498),B_499))
      | ~ r1_tarski(k2_relat_1(E_498),B_499)
      | ~ v1_funct_1(E_498)
      | ~ v1_relat_1(E_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_4366,plain,(
    ! [B_499] :
      ( r2_hidden('#skF_8',k1_funct_2('#skF_8',B_499))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_499)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3805,c_4361])).

tff(c_4369,plain,(
    ! [B_499] : r2_hidden('#skF_8',k1_funct_2('#skF_8',B_499)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3343,c_106,c_3770,c_3786,c_4366])).

tff(c_3140,plain,(
    ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3118,c_98])).

tff(c_3782,plain,(
    ~ r2_hidden('#skF_8',k1_funct_2('#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3750,c_3750,c_3140])).

tff(c_4372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4369,c_3782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n024.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:28:51 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/1.94  
% 5.18/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/1.94  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3
% 5.18/1.94  
% 5.18/1.94  %Foreground sorts:
% 5.18/1.94  
% 5.18/1.94  
% 5.18/1.94  %Background operators:
% 5.18/1.94  
% 5.18/1.94  
% 5.18/1.94  %Foreground operators:
% 5.18/1.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.18/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.18/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.18/1.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.18/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.18/1.94  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.18/1.94  tff('#skF_7', type, '#skF_7': $i).
% 5.18/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.18/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.18/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.18/1.94  tff('#skF_6', type, '#skF_6': $i).
% 5.18/1.94  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.18/1.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.18/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.18/1.94  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 5.18/1.94  tff('#skF_8', type, '#skF_8': $i).
% 5.18/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/1.94  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.18/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.18/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.18/1.94  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.18/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.18/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.18/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.18/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.18/1.94  
% 5.18/1.96  tff(f_159, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => r2_hidden(C, k1_funct_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 5.18/1.96  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.18/1.96  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.18/1.96  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.18/1.96  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.18/1.96  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.18/1.96  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.18/1.96  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.18/1.96  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.18/1.96  tff(f_146, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 5.18/1.96  tff(f_50, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 5.18/1.96  tff(f_45, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 5.18/1.96  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.18/1.96  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.18/1.96  tff(f_98, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.18/1.96  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.18/1.96  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.18/1.96  tff(c_102, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.18/1.96  tff(c_965, plain, (![A_171, B_172, C_173]: (k2_relset_1(A_171, B_172, C_173)=k2_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.18/1.96  tff(c_986, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_102, c_965])).
% 5.18/1.96  tff(c_1023, plain, (![A_180, B_181, C_182]: (m1_subset_1(k2_relset_1(A_180, B_181, C_182), k1_zfmisc_1(B_181)) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.18/1.96  tff(c_1059, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_986, c_1023])).
% 5.18/1.96  tff(c_1075, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1059])).
% 5.18/1.96  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.18/1.96  tff(c_1089, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_1075, c_18])).
% 5.18/1.96  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.18/1.96  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.18/1.96  tff(c_429, plain, (![C_106, A_107, B_108]: (v1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.18/1.96  tff(c_580, plain, (![A_127, A_128, B_129]: (v1_relat_1(A_127) | ~r1_tarski(A_127, k2_zfmisc_1(A_128, B_129)))), inference(resolution, [status(thm)], [c_20, c_429])).
% 5.18/1.96  tff(c_596, plain, (![A_128, B_129]: (v1_relat_1(k2_zfmisc_1(A_128, B_129)))), inference(resolution, [status(thm)], [c_6, c_580])).
% 5.18/1.96  tff(c_376, plain, (![B_102, A_103]: (v1_relat_1(B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_103)) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.18/1.96  tff(c_388, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_102, c_376])).
% 5.18/1.96  tff(c_428, plain, (~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_388])).
% 5.18/1.96  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_596, c_428])).
% 5.18/1.96  tff(c_600, plain, (v1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_388])).
% 5.18/1.96  tff(c_106, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.18/1.96  tff(c_100, plain, (k1_xboole_0='#skF_6' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.18/1.96  tff(c_120, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_100])).
% 5.18/1.96  tff(c_104, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.18/1.96  tff(c_807, plain, (![A_155, B_156, C_157]: (k1_relset_1(A_155, B_156, C_157)=k1_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.18/1.96  tff(c_822, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_102, c_807])).
% 5.18/1.96  tff(c_3047, plain, (![B_348, A_349, C_350]: (k1_xboole_0=B_348 | k1_relset_1(A_349, B_348, C_350)=A_349 | ~v1_funct_2(C_350, A_349, B_348) | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_349, B_348))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.18/1.96  tff(c_3074, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_102, c_3047])).
% 5.18/1.96  tff(c_3082, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_822, c_3074])).
% 5.18/1.96  tff(c_3083, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_120, c_3082])).
% 5.18/1.96  tff(c_62, plain, (![E_60, B_42]: (r2_hidden(E_60, k1_funct_2(k1_relat_1(E_60), B_42)) | ~r1_tarski(k2_relat_1(E_60), B_42) | ~v1_funct_1(E_60) | ~v1_relat_1(E_60))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.18/1.96  tff(c_3089, plain, (![B_42]: (r2_hidden('#skF_8', k1_funct_2('#skF_6', B_42)) | ~r1_tarski(k2_relat_1('#skF_8'), B_42) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3083, c_62])).
% 5.18/1.96  tff(c_3099, plain, (![B_351]: (r2_hidden('#skF_8', k1_funct_2('#skF_6', B_351)) | ~r1_tarski(k2_relat_1('#skF_8'), B_351))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_106, c_3089])).
% 5.18/1.96  tff(c_98, plain, (~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.18/1.96  tff(c_3104, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_3099, c_98])).
% 5.18/1.96  tff(c_3109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1089, c_3104])).
% 5.18/1.96  tff(c_3110, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_100])).
% 5.18/1.96  tff(c_3111, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_100])).
% 5.18/1.96  tff(c_3118, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3110, c_3111])).
% 5.18/1.96  tff(c_3144, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3118, c_102])).
% 5.18/1.96  tff(c_3330, plain, (![C_387, A_388, B_389]: (v1_relat_1(C_387) | ~m1_subset_1(C_387, k1_zfmisc_1(k2_zfmisc_1(A_388, B_389))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.18/1.96  tff(c_3343, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_3144, c_3330])).
% 5.18/1.96  tff(c_14, plain, (![A_8]: (v1_xboole_0('#skF_1'(A_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.18/1.96  tff(c_3147, plain, (![B_357, A_358]: (~v1_xboole_0(B_357) | B_357=A_358 | ~v1_xboole_0(A_358))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.18/1.96  tff(c_3151, plain, (![A_359, A_360]: (A_359='#skF_1'(A_360) | ~v1_xboole_0(A_359))), inference(resolution, [status(thm)], [c_14, c_3147])).
% 5.18/1.96  tff(c_3155, plain, (![A_362, A_361]: ('#skF_1'(A_362)='#skF_1'(A_361))), inference(resolution, [status(thm)], [c_14, c_3151])).
% 5.18/1.96  tff(c_16, plain, (![A_8]: (m1_subset_1('#skF_1'(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.18/1.96  tff(c_3166, plain, (![A_362, A_361]: (m1_subset_1('#skF_1'(A_362), k1_zfmisc_1(A_361)))), inference(superposition, [status(thm), theory('equality')], [c_3155, c_16])).
% 5.18/1.96  tff(c_3222, plain, (![A_372, B_373]: (r1_tarski(A_372, B_373) | ~m1_subset_1(A_372, k1_zfmisc_1(B_373)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.18/1.96  tff(c_3239, plain, (![A_374, A_375]: (r1_tarski('#skF_1'(A_374), A_375))), inference(resolution, [status(thm)], [c_3166, c_3222])).
% 5.18/1.96  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.18/1.96  tff(c_3272, plain, (![A_381, A_382]: (k3_xboole_0('#skF_1'(A_381), A_382)='#skF_1'(A_381))), inference(resolution, [status(thm)], [c_3239, c_8])).
% 5.18/1.96  tff(c_10, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.18/1.96  tff(c_3131, plain, (![A_5]: (k3_xboole_0(A_5, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3110, c_3110, c_10])).
% 5.18/1.96  tff(c_3282, plain, (![A_381]: ('#skF_1'(A_381)='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3272, c_3131])).
% 5.18/1.96  tff(c_3306, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3282, c_14])).
% 5.18/1.96  tff(c_3572, plain, (![C_413, B_414, A_415]: (v1_xboole_0(C_413) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(B_414, A_415))) | ~v1_xboole_0(A_415))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.18/1.96  tff(c_3583, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_3144, c_3572])).
% 5.18/1.96  tff(c_3589, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3306, c_3583])).
% 5.18/1.96  tff(c_3150, plain, (![A_358, A_8]: (A_358='#skF_1'(A_8) | ~v1_xboole_0(A_358))), inference(resolution, [status(thm)], [c_14, c_3147])).
% 5.18/1.96  tff(c_3305, plain, (![A_358]: (A_358='#skF_6' | ~v1_xboole_0(A_358))), inference(demodulation, [status(thm), theory('equality')], [c_3282, c_3150])).
% 5.18/1.96  tff(c_3595, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_3589, c_3305])).
% 5.18/1.96  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.18/1.96  tff(c_3112, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3110, c_3110, c_24])).
% 5.18/1.96  tff(c_3623, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3595, c_3595, c_3112])).
% 5.18/1.96  tff(c_28, plain, (![A_15]: (k2_relat_1(A_15)!=k1_xboole_0 | k1_xboole_0=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.18/1.96  tff(c_3217, plain, (![A_15]: (k2_relat_1(A_15)!='#skF_6' | A_15='#skF_6' | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_3110, c_3110, c_28])).
% 5.18/1.96  tff(c_3385, plain, (k2_relat_1('#skF_8')!='#skF_6' | '#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_3343, c_3217])).
% 5.18/1.96  tff(c_3427, plain, (k2_relat_1('#skF_8')!='#skF_6'), inference(splitLeft, [status(thm)], [c_3385])).
% 5.18/1.96  tff(c_3602, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3595, c_3427])).
% 5.18/1.96  tff(c_3681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3623, c_3602])).
% 5.18/1.96  tff(c_3682, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_3385])).
% 5.18/1.96  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.18/1.96  tff(c_3113, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3110, c_3110, c_26])).
% 5.18/1.96  tff(c_3718, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3682, c_3682, c_3113])).
% 5.18/1.96  tff(c_30, plain, (![A_15]: (k1_relat_1(A_15)!=k1_xboole_0 | k1_xboole_0=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.18/1.96  tff(c_3220, plain, (![A_15]: (k1_relat_1(A_15)!='#skF_6' | A_15='#skF_6' | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_3110, c_3110, c_30])).
% 5.18/1.96  tff(c_3384, plain, (k1_relat_1('#skF_8')!='#skF_6' | '#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_3343, c_3220])).
% 5.18/1.96  tff(c_3412, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitLeft, [status(thm)], [c_3384])).
% 5.18/1.96  tff(c_3700, plain, (k1_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3682, c_3412])).
% 5.18/1.96  tff(c_3749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3718, c_3700])).
% 5.18/1.96  tff(c_3750, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_3384])).
% 5.18/1.96  tff(c_3236, plain, (![A_362, A_361]: (r1_tarski('#skF_1'(A_362), A_361))), inference(resolution, [status(thm)], [c_3166, c_3222])).
% 5.18/1.96  tff(c_3302, plain, (![A_361]: (r1_tarski('#skF_6', A_361))), inference(demodulation, [status(thm), theory('equality')], [c_3282, c_3236])).
% 5.18/1.96  tff(c_3770, plain, (![A_361]: (r1_tarski('#skF_8', A_361))), inference(demodulation, [status(thm), theory('equality')], [c_3750, c_3302])).
% 5.18/1.96  tff(c_3786, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3750, c_3750, c_3112])).
% 5.18/1.96  tff(c_3751, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_3384])).
% 5.18/1.96  tff(c_3805, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3750, c_3751])).
% 5.18/1.96  tff(c_4361, plain, (![E_498, B_499]: (r2_hidden(E_498, k1_funct_2(k1_relat_1(E_498), B_499)) | ~r1_tarski(k2_relat_1(E_498), B_499) | ~v1_funct_1(E_498) | ~v1_relat_1(E_498))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.18/1.96  tff(c_4366, plain, (![B_499]: (r2_hidden('#skF_8', k1_funct_2('#skF_8', B_499)) | ~r1_tarski(k2_relat_1('#skF_8'), B_499) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3805, c_4361])).
% 5.18/1.96  tff(c_4369, plain, (![B_499]: (r2_hidden('#skF_8', k1_funct_2('#skF_8', B_499)))), inference(demodulation, [status(thm), theory('equality')], [c_3343, c_106, c_3770, c_3786, c_4366])).
% 5.18/1.96  tff(c_3140, plain, (~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3118, c_98])).
% 5.18/1.96  tff(c_3782, plain, (~r2_hidden('#skF_8', k1_funct_2('#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3750, c_3750, c_3140])).
% 5.18/1.96  tff(c_4372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4369, c_3782])).
% 5.18/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/1.96  
% 5.18/1.96  Inference rules
% 5.18/1.96  ----------------------
% 5.18/1.96  #Ref     : 0
% 5.18/1.96  #Sup     : 943
% 5.18/1.96  #Fact    : 0
% 5.18/1.96  #Define  : 0
% 5.18/1.96  #Split   : 22
% 5.18/1.96  #Chain   : 0
% 5.18/1.96  #Close   : 0
% 5.18/1.96  
% 5.18/1.96  Ordering : KBO
% 5.18/1.96  
% 5.18/1.96  Simplification rules
% 5.18/1.96  ----------------------
% 5.18/1.96  #Subsume      : 136
% 5.18/1.96  #Demod        : 870
% 5.18/1.96  #Tautology    : 499
% 5.18/1.96  #SimpNegUnit  : 14
% 5.18/1.96  #BackRed      : 91
% 5.18/1.96  
% 5.18/1.96  #Partial instantiations: 0
% 5.18/1.96  #Strategies tried      : 1
% 5.18/1.96  
% 5.18/1.96  Timing (in seconds)
% 5.18/1.96  ----------------------
% 5.18/1.97  Preprocessing        : 0.36
% 5.18/1.97  Parsing              : 0.18
% 5.18/1.97  CNF conversion       : 0.03
% 5.18/1.97  Main loop            : 0.83
% 5.18/1.97  Inferencing          : 0.27
% 5.18/1.97  Reduction            : 0.27
% 5.18/1.97  Demodulation         : 0.20
% 5.18/1.97  BG Simplification    : 0.04
% 5.18/1.97  Subsumption          : 0.17
% 5.18/1.97  Abstraction          : 0.04
% 5.18/1.97  MUC search           : 0.00
% 5.18/1.97  Cooper               : 0.00
% 5.18/1.97  Total                : 1.23
% 5.18/1.97  Index Insertion      : 0.00
% 5.18/1.97  Index Deletion       : 0.00
% 5.18/1.97  Index Matching       : 0.00
% 5.18/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
