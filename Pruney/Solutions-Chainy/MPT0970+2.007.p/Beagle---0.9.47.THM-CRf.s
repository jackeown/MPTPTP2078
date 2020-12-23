%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:19 EST 2020

% Result     : Theorem 6.28s
% Output     : CNFRefutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :  238 (2282 expanded)
%              Number of leaves         :   40 ( 784 expanded)
%              Depth                    :   17
%              Number of atoms          :  430 (7122 expanded)
%              Number of equality atoms :  143 (2670 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_68,axiom,(
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

tff(f_47,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_66,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_68,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4259,plain,(
    ! [C_620,B_621,A_622] :
      ( v5_relat_1(C_620,B_621)
      | ~ m1_subset_1(C_620,k1_zfmisc_1(k2_zfmisc_1(A_622,B_621))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4263,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_4259])).

tff(c_88,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_92,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_88])).

tff(c_795,plain,(
    ! [A_206,B_207,C_208] :
      ( k2_relset_1(A_206,B_207,C_208) = k2_relat_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_799,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_795])).

tff(c_801,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_66])).

tff(c_770,plain,(
    ! [C_195,B_196,A_197] :
      ( v5_relat_1(C_195,B_196)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_774,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_770])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_806,plain,(
    ! [A_210,B_211,C_212] :
      ( k1_relset_1(A_210,B_211,C_212) = k1_relat_1(C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_810,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_806])).

tff(c_3101,plain,(
    ! [B_489,A_490,C_491] :
      ( k1_xboole_0 = B_489
      | k1_relset_1(A_490,B_489,C_491) = A_490
      | ~ v1_funct_2(C_491,A_490,B_489)
      | ~ m1_subset_1(C_491,k1_zfmisc_1(k2_zfmisc_1(A_490,B_489))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3104,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_3101])).

tff(c_3107,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_810,c_3104])).

tff(c_3120,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3107])).

tff(c_76,plain,(
    ! [D_69] :
      ( r2_hidden('#skF_9'(D_69),'#skF_6')
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_775,plain,(
    ! [C_198,B_199,A_200] :
      ( r2_hidden(C_198,B_199)
      | ~ r2_hidden(C_198,A_200)
      | ~ r1_tarski(A_200,B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_781,plain,(
    ! [D_69,B_199] :
      ( r2_hidden('#skF_9'(D_69),B_199)
      | ~ r1_tarski('#skF_6',B_199)
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_76,c_775])).

tff(c_72,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_74,plain,(
    ! [D_69] :
      ( k1_funct_1('#skF_8','#skF_9'(D_69)) = D_69
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_859,plain,(
    ! [A_221,D_222] :
      ( r2_hidden(k1_funct_1(A_221,D_222),k2_relat_1(A_221))
      | ~ r2_hidden(D_222,k1_relat_1(A_221))
      | ~ v1_funct_1(A_221)
      | ~ v1_relat_1(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_864,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_69),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_859])).

tff(c_2245,plain,(
    ! [D_376] :
      ( r2_hidden(D_376,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_376),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_376,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_72,c_864])).

tff(c_2250,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_781,c_2245])).

tff(c_2255,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2250])).

tff(c_3123,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3120,c_2255])).

tff(c_3129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3123])).

tff(c_3130,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3107])).

tff(c_56,plain,(
    ! [C_65,A_63] :
      ( k1_xboole_0 = C_65
      | ~ v1_funct_2(C_65,A_63,k1_xboole_0)
      | k1_xboole_0 = A_63
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3560,plain,(
    ! [C_538,A_539] :
      ( C_538 = '#skF_7'
      | ~ v1_funct_2(C_538,A_539,'#skF_7')
      | A_539 = '#skF_7'
      | ~ m1_subset_1(C_538,k1_zfmisc_1(k2_zfmisc_1(A_539,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3130,c_3130,c_3130,c_3130,c_56])).

tff(c_3563,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68,c_3560])).

tff(c_3566,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3563])).

tff(c_3567,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3566])).

tff(c_2391,plain,(
    ! [B_406,A_407,C_408] :
      ( k1_xboole_0 = B_406
      | k1_relset_1(A_407,B_406,C_408) = A_407
      | ~ v1_funct_2(C_408,A_407,B_406)
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_407,B_406))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2394,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_2391])).

tff(c_2397,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_810,c_2394])).

tff(c_2398,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2397])).

tff(c_2399,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_2255])).

tff(c_2405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2399])).

tff(c_2406,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2397])).

tff(c_2691,plain,(
    ! [C_439,A_440] :
      ( C_439 = '#skF_7'
      | ~ v1_funct_2(C_439,A_440,'#skF_7')
      | A_440 = '#skF_7'
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(A_440,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_2406,c_2406,c_2406,c_56])).

tff(c_2694,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68,c_2691])).

tff(c_2697,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2694])).

tff(c_2698,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2697])).

tff(c_185,plain,(
    ! [A_105,B_106,C_107] :
      ( k2_relset_1(A_105,B_106,C_107) = k2_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_189,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_185])).

tff(c_190,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_66])).

tff(c_166,plain,(
    ! [C_96,B_97,A_98] :
      ( v5_relat_1(C_96,B_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_170,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_166])).

tff(c_195,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_relset_1(A_108,B_109,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_199,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_195])).

tff(c_303,plain,(
    ! [B_143,A_144,C_145] :
      ( k1_xboole_0 = B_143
      | k1_relset_1(A_144,B_143,C_145) = A_144
      | ~ v1_funct_2(C_145,A_144,B_143)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_306,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_303])).

tff(c_309,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_199,c_306])).

tff(c_321,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_148,plain,(
    ! [C_91,B_92,A_93] :
      ( r2_hidden(C_91,B_92)
      | ~ r2_hidden(C_91,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_154,plain,(
    ! [D_69,B_92] :
      ( r2_hidden('#skF_9'(D_69),B_92)
      | ~ r1_tarski('#skF_6',B_92)
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_76,c_148])).

tff(c_228,plain,(
    ! [A_118,D_119] :
      ( r2_hidden(k1_funct_1(A_118,D_119),k2_relat_1(A_118))
      | ~ r2_hidden(D_119,k1_relat_1(A_118))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_233,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_69),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_228])).

tff(c_241,plain,(
    ! [D_120] :
      ( r2_hidden(D_120,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_120),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_120,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_72,c_233])).

tff(c_246,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_154,c_241])).

tff(c_247,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_322,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_247])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_322])).

tff(c_330,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_329,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_420,plain,(
    ! [C_153,A_154] :
      ( C_153 = '#skF_7'
      | ~ v1_funct_2(C_153,A_154,'#skF_7')
      | A_154 = '#skF_7'
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_154,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_329,c_329,c_329,c_56])).

tff(c_423,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68,c_420])).

tff(c_426,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_423])).

tff(c_427,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_448,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_70])).

tff(c_440,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_199])).

tff(c_447,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_68])).

tff(c_62,plain,(
    ! [B_64,C_65] :
      ( k1_relset_1(k1_xboole_0,B_64,C_65) = k1_xboole_0
      | ~ v1_funct_2(C_65,k1_xboole_0,B_64)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_333,plain,(
    ! [B_64,C_65] :
      ( k1_relset_1('#skF_7',B_64,C_65) = '#skF_7'
      | ~ v1_funct_2(C_65,'#skF_7',B_64)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_64))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_329,c_329,c_329,c_62])).

tff(c_609,plain,(
    ! [B_177,C_178] :
      ( k1_relset_1('#skF_6',B_177,C_178) = '#skF_6'
      | ~ v1_funct_2(C_178,'#skF_6',B_177)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_177))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_427,c_427,c_427,c_333])).

tff(c_612,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_447,c_609])).

tff(c_615,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_440,c_612])).

tff(c_617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_615])).

tff(c_618,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_129,plain,(
    ! [B_85,A_86] :
      ( v5_relat_1(B_85,A_86)
      | ~ r1_tarski(k2_relat_1(B_85),A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_138,plain,(
    ! [B_87] :
      ( v5_relat_1(B_87,k2_relat_1(B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_12,c_129])).

tff(c_141,plain,
    ( v5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_138])).

tff(c_142,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_337,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_142])).

tff(c_627,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_337])).

tff(c_643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_627])).

tff(c_654,plain,(
    ! [D_179] :
      ( r2_hidden(D_179,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_179,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_693,plain,(
    ! [A_187] :
      ( r1_tarski(A_187,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_187,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_654,c_4])).

tff(c_703,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_693])).

tff(c_155,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(k2_relat_1(B_94),A_95)
      | ~ v5_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_165,plain,(
    ! [B_94,A_95] :
      ( k2_relat_1(B_94) = A_95
      | ~ r1_tarski(A_95,k2_relat_1(B_94))
      | ~ v5_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_155,c_8])).

tff(c_709,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_703,c_165])).

tff(c_715,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_170,c_709])).

tff(c_717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_715])).

tff(c_719,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_782,plain,(
    ! [D_201,B_202] :
      ( r2_hidden('#skF_9'(D_201),B_202)
      | ~ r1_tarski('#skF_6',B_202)
      | ~ r2_hidden(D_201,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_76,c_775])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_851,plain,(
    ! [D_216,B_217,B_218] :
      ( r2_hidden('#skF_9'(D_216),B_217)
      | ~ r1_tarski(B_218,B_217)
      | ~ r1_tarski('#skF_6',B_218)
      | ~ r2_hidden(D_216,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_782,c_2])).

tff(c_2293,plain,(
    ! [D_392,A_393,B_394] :
      ( r2_hidden('#skF_9'(D_392),A_393)
      | ~ r1_tarski('#skF_6',k2_relat_1(B_394))
      | ~ r2_hidden(D_392,'#skF_7')
      | ~ v5_relat_1(B_394,A_393)
      | ~ v1_relat_1(B_394) ) ),
    inference(resolution,[status(thm)],[c_16,c_851])).

tff(c_2295,plain,(
    ! [D_392,A_393] :
      ( r2_hidden('#skF_9'(D_392),A_393)
      | ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r2_hidden(D_392,'#skF_7')
      | ~ v5_relat_1(k1_xboole_0,A_393)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2293])).

tff(c_2297,plain,(
    ! [D_392,A_393] :
      ( r2_hidden('#skF_9'(D_392),A_393)
      | ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r2_hidden(D_392,'#skF_7')
      | ~ v5_relat_1(k1_xboole_0,A_393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_2295])).

tff(c_2302,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2297])).

tff(c_2412,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_2302])).

tff(c_2713,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2698,c_2412])).

tff(c_2736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2713])).

tff(c_2737,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2697])).

tff(c_2779,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2737,c_801])).

tff(c_2432,plain,(
    k2_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_2406,c_18])).

tff(c_2770,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2737,c_2737,c_2432])).

tff(c_2814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2779,c_2770])).

tff(c_2816,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2297])).

tff(c_2830,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(resolution,[status(thm)],[c_2816,c_8])).

tff(c_2860,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2830])).

tff(c_3154,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3130,c_2860])).

tff(c_3595,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3567,c_3154])).

tff(c_3619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3595])).

tff(c_3620,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3566])).

tff(c_3663,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3620,c_801])).

tff(c_3175,plain,(
    k2_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3130,c_3130,c_18])).

tff(c_3654,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3620,c_3620,c_3175])).

tff(c_3698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3663,c_3654])).

tff(c_3699,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2830])).

tff(c_117,plain,(
    ! [A_83] :
      ( k2_relat_1(A_83) = k1_xboole_0
      | k1_relat_1(A_83) != k1_xboole_0
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_121,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_117])).

tff(c_127,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_3725,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3699,c_127])).

tff(c_64,plain,(
    ! [B_64,A_63,C_65] :
      ( k1_xboole_0 = B_64
      | k1_relset_1(A_63,B_64,C_65) = A_63
      | ~ v1_funct_2(C_65,A_63,B_64)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3853,plain,(
    ! [B_550,A_551,C_552] :
      ( B_550 = '#skF_6'
      | k1_relset_1(A_551,B_550,C_552) = A_551
      | ~ v1_funct_2(C_552,A_551,B_550)
      | ~ m1_subset_1(C_552,k1_zfmisc_1(k2_zfmisc_1(A_551,B_550))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3699,c_64])).

tff(c_3856,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_3853])).

tff(c_3859,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_810,c_3856])).

tff(c_3860,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_3725,c_3859])).

tff(c_3872,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3860,c_70])).

tff(c_3864,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3860,c_810])).

tff(c_3871,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3860,c_68])).

tff(c_4114,plain,(
    ! [B_597,C_598] :
      ( k1_relset_1('#skF_6',B_597,C_598) = '#skF_6'
      | ~ v1_funct_2(C_598,'#skF_6',B_597)
      | ~ m1_subset_1(C_598,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_597))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3699,c_3699,c_3699,c_3699,c_62])).

tff(c_4117,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_3871,c_4114])).

tff(c_4120,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3872,c_3864,c_4117])).

tff(c_4122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3725,c_4120])).

tff(c_4133,plain,(
    ! [D_599] :
      ( r2_hidden(D_599,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_599,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_2250])).

tff(c_4153,plain,(
    ! [A_606] :
      ( r1_tarski(A_606,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_606,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4133,c_4])).

tff(c_4163,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_4153])).

tff(c_740,plain,(
    ! [B_192,A_193] :
      ( r1_tarski(k2_relat_1(B_192),A_193)
      | ~ v5_relat_1(B_192,A_193)
      | ~ v1_relat_1(B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_750,plain,(
    ! [B_192,A_193] :
      ( k2_relat_1(B_192) = A_193
      | ~ r1_tarski(A_193,k2_relat_1(B_192))
      | ~ v5_relat_1(B_192,A_193)
      | ~ v1_relat_1(B_192) ) ),
    inference(resolution,[status(thm)],[c_740,c_8])).

tff(c_4168,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_4163,c_750])).

tff(c_4174,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_774,c_4168])).

tff(c_4176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_801,c_4174])).

tff(c_4177,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_4226,plain,(
    ! [B_617,A_618] :
      ( r1_tarski(k2_relat_1(B_617),A_618)
      | ~ v5_relat_1(B_617,A_618)
      | ~ v1_relat_1(B_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4234,plain,(
    ! [A_618] :
      ( r1_tarski(k1_xboole_0,A_618)
      | ~ v5_relat_1('#skF_8',A_618)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4177,c_4226])).

tff(c_4241,plain,(
    ! [A_618] :
      ( r1_tarski(k1_xboole_0,A_618)
      | ~ v5_relat_1('#skF_8',A_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_4234])).

tff(c_4267,plain,(
    r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(resolution,[status(thm)],[c_4263,c_4241])).

tff(c_4274,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4267,c_8])).

tff(c_4275,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_4274])).

tff(c_4296,plain,(
    ! [A_632,B_633,C_634] :
      ( k2_relset_1(A_632,B_633,C_634) = k2_relat_1(C_634)
      | ~ m1_subset_1(C_634,k1_zfmisc_1(k2_zfmisc_1(A_632,B_633))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4299,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_4296])).

tff(c_4301,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4177,c_4299])).

tff(c_4302,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4301,c_66])).

tff(c_4178,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_4285,plain,(
    ! [A_628,B_629,C_630] :
      ( k1_relset_1(A_628,B_629,C_630) = k1_relat_1(C_630)
      | ~ m1_subset_1(C_630,k1_zfmisc_1(k2_zfmisc_1(A_628,B_629))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4288,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_4285])).

tff(c_4290,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4178,c_4288])).

tff(c_4947,plain,(
    ! [B_721,A_722,C_723] :
      ( k1_xboole_0 = B_721
      | k1_relset_1(A_722,B_721,C_723) = A_722
      | ~ v1_funct_2(C_723,A_722,B_721)
      | ~ m1_subset_1(C_723,k1_zfmisc_1(k2_zfmisc_1(A_722,B_721))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4950,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_4947])).

tff(c_4953,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4290,c_4950])).

tff(c_4954,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_4302,c_4953])).

tff(c_4219,plain,(
    ! [C_614,B_615,A_616] :
      ( r2_hidden(C_614,B_615)
      | ~ r2_hidden(C_614,A_616)
      | ~ r1_tarski(A_616,B_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4268,plain,(
    ! [D_623,B_624] :
      ( r2_hidden('#skF_9'(D_623),B_624)
      | ~ r1_tarski('#skF_6',B_624)
      | ~ r2_hidden(D_623,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_76,c_4219])).

tff(c_4352,plain,(
    ! [D_638,B_639,B_640] :
      ( r2_hidden('#skF_9'(D_638),B_639)
      | ~ r1_tarski(B_640,B_639)
      | ~ r1_tarski('#skF_6',B_640)
      | ~ r2_hidden(D_638,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4268,c_2])).

tff(c_4359,plain,(
    ! [D_638] :
      ( r2_hidden('#skF_9'(D_638),'#skF_7')
      | ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r2_hidden(D_638,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4267,c_4352])).

tff(c_4362,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_4359])).

tff(c_4991,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4954,c_4362])).

tff(c_5011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4991])).

tff(c_5013,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4359])).

tff(c_4225,plain,(
    ! [D_69,B_615] :
      ( r2_hidden('#skF_9'(D_69),B_615)
      | ~ r1_tarski('#skF_6',B_615)
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_76,c_4219])).

tff(c_5096,plain,(
    ! [A_746,D_747] :
      ( r2_hidden(k1_funct_1(A_746,D_747),k2_relat_1(A_746))
      | ~ r2_hidden(D_747,k1_relat_1(A_746))
      | ~ v1_funct_1(A_746)
      | ~ v1_relat_1(A_746) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5104,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_69),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_5096])).

tff(c_5121,plain,(
    ! [D_749] :
      ( r2_hidden(D_749,k1_xboole_0)
      | ~ r2_hidden('#skF_9'(D_749),k1_xboole_0)
      | ~ r2_hidden(D_749,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_72,c_4178,c_4177,c_5104])).

tff(c_5140,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k1_xboole_0)
      | ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4225,c_5121])).

tff(c_5152,plain,(
    ! [D_750] :
      ( r2_hidden(D_750,k1_xboole_0)
      | ~ r2_hidden(D_750,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5013,c_5140])).

tff(c_5162,plain,(
    ! [A_753] :
      ( r1_tarski(A_753,k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_753,k1_xboole_0),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5152,c_4])).

tff(c_5170,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_5162])).

tff(c_5175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4275,c_4275,c_5170])).

tff(c_5176,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4274])).

tff(c_5194,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5176,c_4177])).

tff(c_5282,plain,(
    ! [A_763,B_764,C_765] :
      ( k2_relset_1(A_763,B_764,C_765) = k2_relat_1(C_765)
      | ~ m1_subset_1(C_765,k1_zfmisc_1(k2_zfmisc_1(A_763,B_764))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5285,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_5282])).

tff(c_5287,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5194,c_5285])).

tff(c_5289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:42:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.28/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.28/2.30  
% 6.28/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.28/2.30  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 6.28/2.30  
% 6.28/2.30  %Foreground sorts:
% 6.28/2.30  
% 6.28/2.30  
% 6.28/2.30  %Background operators:
% 6.28/2.30  
% 6.28/2.30  
% 6.28/2.30  %Foreground operators:
% 6.28/2.30  tff('#skF_9', type, '#skF_9': $i > $i).
% 6.28/2.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.28/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.28/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.28/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.28/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.28/2.30  tff('#skF_7', type, '#skF_7': $i).
% 6.28/2.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.28/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.28/2.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.28/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.28/2.30  tff('#skF_6', type, '#skF_6': $i).
% 6.28/2.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.28/2.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.28/2.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.28/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.28/2.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.28/2.30  tff('#skF_8', type, '#skF_8': $i).
% 6.28/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.28/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.28/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.28/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.28/2.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.28/2.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.28/2.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.28/2.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.28/2.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.28/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.28/2.30  
% 6.63/2.33  tff(f_123, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 6.63/2.33  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.63/2.33  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.63/2.33  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.63/2.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.63/2.33  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.63/2.33  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.63/2.33  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.63/2.33  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 6.63/2.33  tff(f_47, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.63/2.33  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.63/2.33  tff(f_53, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 6.63/2.33  tff(c_66, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.63/2.33  tff(c_68, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.63/2.33  tff(c_4259, plain, (![C_620, B_621, A_622]: (v5_relat_1(C_620, B_621) | ~m1_subset_1(C_620, k1_zfmisc_1(k2_zfmisc_1(A_622, B_621))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.63/2.33  tff(c_4263, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_4259])).
% 6.63/2.33  tff(c_88, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.63/2.33  tff(c_92, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_88])).
% 6.63/2.33  tff(c_795, plain, (![A_206, B_207, C_208]: (k2_relset_1(A_206, B_207, C_208)=k2_relat_1(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.63/2.33  tff(c_799, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_795])).
% 6.63/2.33  tff(c_801, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_799, c_66])).
% 6.63/2.33  tff(c_770, plain, (![C_195, B_196, A_197]: (v5_relat_1(C_195, B_196) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_196))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.63/2.33  tff(c_774, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_770])).
% 6.63/2.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.63/2.33  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.63/2.33  tff(c_70, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.63/2.33  tff(c_806, plain, (![A_210, B_211, C_212]: (k1_relset_1(A_210, B_211, C_212)=k1_relat_1(C_212) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.63/2.33  tff(c_810, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_806])).
% 6.63/2.33  tff(c_3101, plain, (![B_489, A_490, C_491]: (k1_xboole_0=B_489 | k1_relset_1(A_490, B_489, C_491)=A_490 | ~v1_funct_2(C_491, A_490, B_489) | ~m1_subset_1(C_491, k1_zfmisc_1(k2_zfmisc_1(A_490, B_489))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.63/2.33  tff(c_3104, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_3101])).
% 6.63/2.33  tff(c_3107, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_810, c_3104])).
% 6.63/2.33  tff(c_3120, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_3107])).
% 6.63/2.33  tff(c_76, plain, (![D_69]: (r2_hidden('#skF_9'(D_69), '#skF_6') | ~r2_hidden(D_69, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.63/2.33  tff(c_775, plain, (![C_198, B_199, A_200]: (r2_hidden(C_198, B_199) | ~r2_hidden(C_198, A_200) | ~r1_tarski(A_200, B_199))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.63/2.33  tff(c_781, plain, (![D_69, B_199]: (r2_hidden('#skF_9'(D_69), B_199) | ~r1_tarski('#skF_6', B_199) | ~r2_hidden(D_69, '#skF_7'))), inference(resolution, [status(thm)], [c_76, c_775])).
% 6.63/2.33  tff(c_72, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.63/2.33  tff(c_74, plain, (![D_69]: (k1_funct_1('#skF_8', '#skF_9'(D_69))=D_69 | ~r2_hidden(D_69, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.63/2.33  tff(c_859, plain, (![A_221, D_222]: (r2_hidden(k1_funct_1(A_221, D_222), k2_relat_1(A_221)) | ~r2_hidden(D_222, k1_relat_1(A_221)) | ~v1_funct_1(A_221) | ~v1_relat_1(A_221))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.63/2.33  tff(c_864, plain, (![D_69]: (r2_hidden(D_69, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_69), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_69, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_859])).
% 6.63/2.33  tff(c_2245, plain, (![D_376]: (r2_hidden(D_376, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_376), k1_relat_1('#skF_8')) | ~r2_hidden(D_376, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_72, c_864])).
% 6.63/2.33  tff(c_2250, plain, (![D_69]: (r2_hidden(D_69, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_69, '#skF_7'))), inference(resolution, [status(thm)], [c_781, c_2245])).
% 6.63/2.33  tff(c_2255, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_2250])).
% 6.63/2.33  tff(c_3123, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3120, c_2255])).
% 6.63/2.33  tff(c_3129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3123])).
% 6.63/2.33  tff(c_3130, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_3107])).
% 6.63/2.33  tff(c_56, plain, (![C_65, A_63]: (k1_xboole_0=C_65 | ~v1_funct_2(C_65, A_63, k1_xboole_0) | k1_xboole_0=A_63 | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.63/2.33  tff(c_3560, plain, (![C_538, A_539]: (C_538='#skF_7' | ~v1_funct_2(C_538, A_539, '#skF_7') | A_539='#skF_7' | ~m1_subset_1(C_538, k1_zfmisc_1(k2_zfmisc_1(A_539, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_3130, c_3130, c_3130, c_3130, c_56])).
% 6.63/2.33  tff(c_3563, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_68, c_3560])).
% 6.63/2.33  tff(c_3566, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3563])).
% 6.63/2.33  tff(c_3567, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_3566])).
% 6.63/2.33  tff(c_2391, plain, (![B_406, A_407, C_408]: (k1_xboole_0=B_406 | k1_relset_1(A_407, B_406, C_408)=A_407 | ~v1_funct_2(C_408, A_407, B_406) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_407, B_406))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.63/2.33  tff(c_2394, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_2391])).
% 6.63/2.33  tff(c_2397, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_810, c_2394])).
% 6.63/2.33  tff(c_2398, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_2397])).
% 6.63/2.33  tff(c_2399, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_2255])).
% 6.63/2.33  tff(c_2405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2399])).
% 6.63/2.33  tff(c_2406, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2397])).
% 6.63/2.33  tff(c_2691, plain, (![C_439, A_440]: (C_439='#skF_7' | ~v1_funct_2(C_439, A_440, '#skF_7') | A_440='#skF_7' | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(A_440, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_2406, c_2406, c_2406, c_56])).
% 6.63/2.33  tff(c_2694, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_68, c_2691])).
% 6.63/2.33  tff(c_2697, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2694])).
% 6.63/2.33  tff(c_2698, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_2697])).
% 6.63/2.33  tff(c_185, plain, (![A_105, B_106, C_107]: (k2_relset_1(A_105, B_106, C_107)=k2_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.63/2.33  tff(c_189, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_185])).
% 6.63/2.33  tff(c_190, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_66])).
% 6.63/2.33  tff(c_166, plain, (![C_96, B_97, A_98]: (v5_relat_1(C_96, B_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.63/2.33  tff(c_170, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_166])).
% 6.63/2.33  tff(c_195, plain, (![A_108, B_109, C_110]: (k1_relset_1(A_108, B_109, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.63/2.33  tff(c_199, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_195])).
% 6.63/2.33  tff(c_303, plain, (![B_143, A_144, C_145]: (k1_xboole_0=B_143 | k1_relset_1(A_144, B_143, C_145)=A_144 | ~v1_funct_2(C_145, A_144, B_143) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.63/2.33  tff(c_306, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_303])).
% 6.63/2.33  tff(c_309, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_199, c_306])).
% 6.63/2.33  tff(c_321, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_309])).
% 6.63/2.33  tff(c_148, plain, (![C_91, B_92, A_93]: (r2_hidden(C_91, B_92) | ~r2_hidden(C_91, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.63/2.33  tff(c_154, plain, (![D_69, B_92]: (r2_hidden('#skF_9'(D_69), B_92) | ~r1_tarski('#skF_6', B_92) | ~r2_hidden(D_69, '#skF_7'))), inference(resolution, [status(thm)], [c_76, c_148])).
% 6.63/2.33  tff(c_228, plain, (![A_118, D_119]: (r2_hidden(k1_funct_1(A_118, D_119), k2_relat_1(A_118)) | ~r2_hidden(D_119, k1_relat_1(A_118)) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.63/2.33  tff(c_233, plain, (![D_69]: (r2_hidden(D_69, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_69), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_69, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_228])).
% 6.63/2.33  tff(c_241, plain, (![D_120]: (r2_hidden(D_120, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_120), k1_relat_1('#skF_8')) | ~r2_hidden(D_120, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_72, c_233])).
% 6.63/2.33  tff(c_246, plain, (![D_69]: (r2_hidden(D_69, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_69, '#skF_7'))), inference(resolution, [status(thm)], [c_154, c_241])).
% 6.63/2.33  tff(c_247, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_246])).
% 6.63/2.33  tff(c_322, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_321, c_247])).
% 6.63/2.33  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_322])).
% 6.63/2.33  tff(c_330, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_309])).
% 6.63/2.33  tff(c_329, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_309])).
% 6.63/2.33  tff(c_420, plain, (![C_153, A_154]: (C_153='#skF_7' | ~v1_funct_2(C_153, A_154, '#skF_7') | A_154='#skF_7' | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_154, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_329, c_329, c_329, c_56])).
% 6.63/2.33  tff(c_423, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_68, c_420])).
% 6.63/2.33  tff(c_426, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_423])).
% 6.63/2.33  tff(c_427, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_426])).
% 6.63/2.33  tff(c_448, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_70])).
% 6.63/2.33  tff(c_440, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_199])).
% 6.63/2.33  tff(c_447, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_427, c_68])).
% 6.63/2.33  tff(c_62, plain, (![B_64, C_65]: (k1_relset_1(k1_xboole_0, B_64, C_65)=k1_xboole_0 | ~v1_funct_2(C_65, k1_xboole_0, B_64) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_64))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.63/2.33  tff(c_333, plain, (![B_64, C_65]: (k1_relset_1('#skF_7', B_64, C_65)='#skF_7' | ~v1_funct_2(C_65, '#skF_7', B_64) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_64))))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_329, c_329, c_329, c_62])).
% 6.63/2.33  tff(c_609, plain, (![B_177, C_178]: (k1_relset_1('#skF_6', B_177, C_178)='#skF_6' | ~v1_funct_2(C_178, '#skF_6', B_177) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_177))))), inference(demodulation, [status(thm), theory('equality')], [c_427, c_427, c_427, c_427, c_333])).
% 6.63/2.33  tff(c_612, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_447, c_609])).
% 6.63/2.33  tff(c_615, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_448, c_440, c_612])).
% 6.63/2.33  tff(c_617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_330, c_615])).
% 6.63/2.33  tff(c_618, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_426])).
% 6.63/2.33  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.63/2.33  tff(c_129, plain, (![B_85, A_86]: (v5_relat_1(B_85, A_86) | ~r1_tarski(k2_relat_1(B_85), A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.63/2.33  tff(c_138, plain, (![B_87]: (v5_relat_1(B_87, k2_relat_1(B_87)) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_12, c_129])).
% 6.63/2.33  tff(c_141, plain, (v5_relat_1(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_138])).
% 6.63/2.33  tff(c_142, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_141])).
% 6.63/2.33  tff(c_337, plain, (~v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_142])).
% 6.63/2.33  tff(c_627, plain, (~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_618, c_337])).
% 6.63/2.33  tff(c_643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_627])).
% 6.63/2.33  tff(c_654, plain, (![D_179]: (r2_hidden(D_179, k2_relat_1('#skF_8')) | ~r2_hidden(D_179, '#skF_7'))), inference(splitRight, [status(thm)], [c_246])).
% 6.63/2.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.63/2.33  tff(c_693, plain, (![A_187]: (r1_tarski(A_187, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_187, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_654, c_4])).
% 6.63/2.33  tff(c_703, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_693])).
% 6.63/2.33  tff(c_155, plain, (![B_94, A_95]: (r1_tarski(k2_relat_1(B_94), A_95) | ~v5_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.63/2.33  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.63/2.33  tff(c_165, plain, (![B_94, A_95]: (k2_relat_1(B_94)=A_95 | ~r1_tarski(A_95, k2_relat_1(B_94)) | ~v5_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_155, c_8])).
% 6.63/2.33  tff(c_709, plain, (k2_relat_1('#skF_8')='#skF_7' | ~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_703, c_165])).
% 6.63/2.33  tff(c_715, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_170, c_709])).
% 6.63/2.33  tff(c_717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_715])).
% 6.63/2.33  tff(c_719, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_141])).
% 6.63/2.33  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.63/2.33  tff(c_782, plain, (![D_201, B_202]: (r2_hidden('#skF_9'(D_201), B_202) | ~r1_tarski('#skF_6', B_202) | ~r2_hidden(D_201, '#skF_7'))), inference(resolution, [status(thm)], [c_76, c_775])).
% 6.63/2.33  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.63/2.33  tff(c_851, plain, (![D_216, B_217, B_218]: (r2_hidden('#skF_9'(D_216), B_217) | ~r1_tarski(B_218, B_217) | ~r1_tarski('#skF_6', B_218) | ~r2_hidden(D_216, '#skF_7'))), inference(resolution, [status(thm)], [c_782, c_2])).
% 6.63/2.33  tff(c_2293, plain, (![D_392, A_393, B_394]: (r2_hidden('#skF_9'(D_392), A_393) | ~r1_tarski('#skF_6', k2_relat_1(B_394)) | ~r2_hidden(D_392, '#skF_7') | ~v5_relat_1(B_394, A_393) | ~v1_relat_1(B_394))), inference(resolution, [status(thm)], [c_16, c_851])).
% 6.63/2.33  tff(c_2295, plain, (![D_392, A_393]: (r2_hidden('#skF_9'(D_392), A_393) | ~r1_tarski('#skF_6', k1_xboole_0) | ~r2_hidden(D_392, '#skF_7') | ~v5_relat_1(k1_xboole_0, A_393) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2293])).
% 6.63/2.33  tff(c_2297, plain, (![D_392, A_393]: (r2_hidden('#skF_9'(D_392), A_393) | ~r1_tarski('#skF_6', k1_xboole_0) | ~r2_hidden(D_392, '#skF_7') | ~v5_relat_1(k1_xboole_0, A_393))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_2295])).
% 6.63/2.33  tff(c_2302, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2297])).
% 6.63/2.33  tff(c_2412, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_2302])).
% 6.63/2.33  tff(c_2713, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2698, c_2412])).
% 6.63/2.33  tff(c_2736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2713])).
% 6.63/2.33  tff(c_2737, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_2697])).
% 6.63/2.33  tff(c_2779, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2737, c_801])).
% 6.63/2.33  tff(c_2432, plain, (k2_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_2406, c_18])).
% 6.63/2.33  tff(c_2770, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2737, c_2737, c_2432])).
% 6.63/2.33  tff(c_2814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2779, c_2770])).
% 6.63/2.33  tff(c_2816, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2297])).
% 6.63/2.33  tff(c_2830, plain, (k1_xboole_0='#skF_6' | ~r1_tarski(k1_xboole_0, '#skF_6')), inference(resolution, [status(thm)], [c_2816, c_8])).
% 6.63/2.33  tff(c_2860, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(splitLeft, [status(thm)], [c_2830])).
% 6.63/2.33  tff(c_3154, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3130, c_2860])).
% 6.63/2.33  tff(c_3595, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3567, c_3154])).
% 6.63/2.33  tff(c_3619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3595])).
% 6.63/2.33  tff(c_3620, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_3566])).
% 6.63/2.33  tff(c_3663, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3620, c_801])).
% 6.63/2.33  tff(c_3175, plain, (k2_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3130, c_3130, c_18])).
% 6.63/2.33  tff(c_3654, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3620, c_3620, c_3175])).
% 6.63/2.33  tff(c_3698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3663, c_3654])).
% 6.63/2.33  tff(c_3699, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2830])).
% 6.63/2.33  tff(c_117, plain, (![A_83]: (k2_relat_1(A_83)=k1_xboole_0 | k1_relat_1(A_83)!=k1_xboole_0 | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.63/2.33  tff(c_121, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_117])).
% 6.63/2.33  tff(c_127, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_121])).
% 6.63/2.33  tff(c_3725, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3699, c_127])).
% 6.63/2.33  tff(c_64, plain, (![B_64, A_63, C_65]: (k1_xboole_0=B_64 | k1_relset_1(A_63, B_64, C_65)=A_63 | ~v1_funct_2(C_65, A_63, B_64) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.63/2.33  tff(c_3853, plain, (![B_550, A_551, C_552]: (B_550='#skF_6' | k1_relset_1(A_551, B_550, C_552)=A_551 | ~v1_funct_2(C_552, A_551, B_550) | ~m1_subset_1(C_552, k1_zfmisc_1(k2_zfmisc_1(A_551, B_550))))), inference(demodulation, [status(thm), theory('equality')], [c_3699, c_64])).
% 6.63/2.33  tff(c_3856, plain, ('#skF_7'='#skF_6' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_3853])).
% 6.63/2.33  tff(c_3859, plain, ('#skF_7'='#skF_6' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_810, c_3856])).
% 6.63/2.33  tff(c_3860, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_3725, c_3859])).
% 6.63/2.33  tff(c_3872, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3860, c_70])).
% 6.63/2.33  tff(c_3864, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3860, c_810])).
% 6.63/2.33  tff(c_3871, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3860, c_68])).
% 6.63/2.33  tff(c_4114, plain, (![B_597, C_598]: (k1_relset_1('#skF_6', B_597, C_598)='#skF_6' | ~v1_funct_2(C_598, '#skF_6', B_597) | ~m1_subset_1(C_598, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_597))))), inference(demodulation, [status(thm), theory('equality')], [c_3699, c_3699, c_3699, c_3699, c_62])).
% 6.63/2.33  tff(c_4117, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_3871, c_4114])).
% 6.63/2.33  tff(c_4120, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3872, c_3864, c_4117])).
% 6.63/2.33  tff(c_4122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3725, c_4120])).
% 6.63/2.33  tff(c_4133, plain, (![D_599]: (r2_hidden(D_599, k2_relat_1('#skF_8')) | ~r2_hidden(D_599, '#skF_7'))), inference(splitRight, [status(thm)], [c_2250])).
% 6.63/2.33  tff(c_4153, plain, (![A_606]: (r1_tarski(A_606, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_606, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_4133, c_4])).
% 6.63/2.33  tff(c_4163, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_4153])).
% 6.63/2.33  tff(c_740, plain, (![B_192, A_193]: (r1_tarski(k2_relat_1(B_192), A_193) | ~v5_relat_1(B_192, A_193) | ~v1_relat_1(B_192))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.63/2.33  tff(c_750, plain, (![B_192, A_193]: (k2_relat_1(B_192)=A_193 | ~r1_tarski(A_193, k2_relat_1(B_192)) | ~v5_relat_1(B_192, A_193) | ~v1_relat_1(B_192))), inference(resolution, [status(thm)], [c_740, c_8])).
% 6.63/2.33  tff(c_4168, plain, (k2_relat_1('#skF_8')='#skF_7' | ~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_4163, c_750])).
% 6.63/2.33  tff(c_4174, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_774, c_4168])).
% 6.63/2.33  tff(c_4176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_801, c_4174])).
% 6.63/2.33  tff(c_4177, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_121])).
% 6.63/2.33  tff(c_4226, plain, (![B_617, A_618]: (r1_tarski(k2_relat_1(B_617), A_618) | ~v5_relat_1(B_617, A_618) | ~v1_relat_1(B_617))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.63/2.33  tff(c_4234, plain, (![A_618]: (r1_tarski(k1_xboole_0, A_618) | ~v5_relat_1('#skF_8', A_618) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_4177, c_4226])).
% 6.63/2.33  tff(c_4241, plain, (![A_618]: (r1_tarski(k1_xboole_0, A_618) | ~v5_relat_1('#skF_8', A_618))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_4234])).
% 6.63/2.33  tff(c_4267, plain, (r1_tarski(k1_xboole_0, '#skF_7')), inference(resolution, [status(thm)], [c_4263, c_4241])).
% 6.63/2.33  tff(c_4274, plain, (k1_xboole_0='#skF_7' | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_4267, c_8])).
% 6.63/2.33  tff(c_4275, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_4274])).
% 6.63/2.33  tff(c_4296, plain, (![A_632, B_633, C_634]: (k2_relset_1(A_632, B_633, C_634)=k2_relat_1(C_634) | ~m1_subset_1(C_634, k1_zfmisc_1(k2_zfmisc_1(A_632, B_633))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.63/2.33  tff(c_4299, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_4296])).
% 6.63/2.33  tff(c_4301, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4177, c_4299])).
% 6.63/2.33  tff(c_4302, plain, (k1_xboole_0!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_4301, c_66])).
% 6.63/2.33  tff(c_4178, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_121])).
% 6.63/2.33  tff(c_4285, plain, (![A_628, B_629, C_630]: (k1_relset_1(A_628, B_629, C_630)=k1_relat_1(C_630) | ~m1_subset_1(C_630, k1_zfmisc_1(k2_zfmisc_1(A_628, B_629))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.63/2.33  tff(c_4288, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_4285])).
% 6.63/2.33  tff(c_4290, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4178, c_4288])).
% 6.63/2.33  tff(c_4947, plain, (![B_721, A_722, C_723]: (k1_xboole_0=B_721 | k1_relset_1(A_722, B_721, C_723)=A_722 | ~v1_funct_2(C_723, A_722, B_721) | ~m1_subset_1(C_723, k1_zfmisc_1(k2_zfmisc_1(A_722, B_721))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.63/2.33  tff(c_4950, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_4947])).
% 6.63/2.33  tff(c_4953, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4290, c_4950])).
% 6.63/2.33  tff(c_4954, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_4302, c_4953])).
% 6.63/2.33  tff(c_4219, plain, (![C_614, B_615, A_616]: (r2_hidden(C_614, B_615) | ~r2_hidden(C_614, A_616) | ~r1_tarski(A_616, B_615))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.63/2.33  tff(c_4268, plain, (![D_623, B_624]: (r2_hidden('#skF_9'(D_623), B_624) | ~r1_tarski('#skF_6', B_624) | ~r2_hidden(D_623, '#skF_7'))), inference(resolution, [status(thm)], [c_76, c_4219])).
% 6.63/2.33  tff(c_4352, plain, (![D_638, B_639, B_640]: (r2_hidden('#skF_9'(D_638), B_639) | ~r1_tarski(B_640, B_639) | ~r1_tarski('#skF_6', B_640) | ~r2_hidden(D_638, '#skF_7'))), inference(resolution, [status(thm)], [c_4268, c_2])).
% 6.63/2.33  tff(c_4359, plain, (![D_638]: (r2_hidden('#skF_9'(D_638), '#skF_7') | ~r1_tarski('#skF_6', k1_xboole_0) | ~r2_hidden(D_638, '#skF_7'))), inference(resolution, [status(thm)], [c_4267, c_4352])).
% 6.63/2.33  tff(c_4362, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_4359])).
% 6.63/2.33  tff(c_4991, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4954, c_4362])).
% 6.63/2.33  tff(c_5011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4991])).
% 6.63/2.33  tff(c_5013, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_4359])).
% 6.63/2.33  tff(c_4225, plain, (![D_69, B_615]: (r2_hidden('#skF_9'(D_69), B_615) | ~r1_tarski('#skF_6', B_615) | ~r2_hidden(D_69, '#skF_7'))), inference(resolution, [status(thm)], [c_76, c_4219])).
% 6.63/2.33  tff(c_5096, plain, (![A_746, D_747]: (r2_hidden(k1_funct_1(A_746, D_747), k2_relat_1(A_746)) | ~r2_hidden(D_747, k1_relat_1(A_746)) | ~v1_funct_1(A_746) | ~v1_relat_1(A_746))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.63/2.33  tff(c_5104, plain, (![D_69]: (r2_hidden(D_69, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_69), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_69, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_5096])).
% 6.63/2.33  tff(c_5121, plain, (![D_749]: (r2_hidden(D_749, k1_xboole_0) | ~r2_hidden('#skF_9'(D_749), k1_xboole_0) | ~r2_hidden(D_749, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_72, c_4178, c_4177, c_5104])).
% 6.63/2.33  tff(c_5140, plain, (![D_69]: (r2_hidden(D_69, k1_xboole_0) | ~r1_tarski('#skF_6', k1_xboole_0) | ~r2_hidden(D_69, '#skF_7'))), inference(resolution, [status(thm)], [c_4225, c_5121])).
% 6.63/2.33  tff(c_5152, plain, (![D_750]: (r2_hidden(D_750, k1_xboole_0) | ~r2_hidden(D_750, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_5013, c_5140])).
% 6.63/2.33  tff(c_5162, plain, (![A_753]: (r1_tarski(A_753, k1_xboole_0) | ~r2_hidden('#skF_1'(A_753, k1_xboole_0), '#skF_7'))), inference(resolution, [status(thm)], [c_5152, c_4])).
% 6.63/2.33  tff(c_5170, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_5162])).
% 6.63/2.33  tff(c_5175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4275, c_4275, c_5170])).
% 6.63/2.33  tff(c_5176, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_4274])).
% 6.63/2.33  tff(c_5194, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5176, c_4177])).
% 6.63/2.33  tff(c_5282, plain, (![A_763, B_764, C_765]: (k2_relset_1(A_763, B_764, C_765)=k2_relat_1(C_765) | ~m1_subset_1(C_765, k1_zfmisc_1(k2_zfmisc_1(A_763, B_764))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.63/2.33  tff(c_5285, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_5282])).
% 6.63/2.33  tff(c_5287, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5194, c_5285])).
% 6.63/2.33  tff(c_5289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_5287])).
% 6.63/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.63/2.33  
% 6.63/2.33  Inference rules
% 6.63/2.33  ----------------------
% 6.63/2.33  #Ref     : 5
% 6.63/2.33  #Sup     : 1004
% 6.63/2.33  #Fact    : 0
% 6.63/2.33  #Define  : 0
% 6.63/2.33  #Split   : 35
% 6.63/2.33  #Chain   : 0
% 6.63/2.33  #Close   : 0
% 6.63/2.33  
% 6.63/2.33  Ordering : KBO
% 6.63/2.33  
% 6.63/2.33  Simplification rules
% 6.63/2.33  ----------------------
% 6.63/2.33  #Subsume      : 379
% 6.63/2.33  #Demod        : 1931
% 6.63/2.33  #Tautology    : 327
% 6.63/2.33  #SimpNegUnit  : 32
% 6.63/2.33  #BackRed      : 643
% 6.63/2.33  
% 6.63/2.33  #Partial instantiations: 0
% 6.63/2.33  #Strategies tried      : 1
% 6.63/2.33  
% 6.63/2.33  Timing (in seconds)
% 6.63/2.33  ----------------------
% 6.63/2.33  Preprocessing        : 0.34
% 6.63/2.33  Parsing              : 0.17
% 6.63/2.33  CNF conversion       : 0.03
% 6.63/2.33  Main loop            : 1.20
% 6.63/2.33  Inferencing          : 0.42
% 6.63/2.33  Reduction            : 0.38
% 6.63/2.33  Demodulation         : 0.26
% 6.63/2.33  BG Simplification    : 0.05
% 6.63/2.33  Subsumption          : 0.25
% 6.63/2.33  Abstraction          : 0.05
% 6.63/2.33  MUC search           : 0.00
% 6.63/2.33  Cooper               : 0.00
% 6.63/2.33  Total                : 1.60
% 6.63/2.33  Index Insertion      : 0.00
% 6.63/2.34  Index Deletion       : 0.00
% 6.63/2.34  Index Matching       : 0.00
% 6.63/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
