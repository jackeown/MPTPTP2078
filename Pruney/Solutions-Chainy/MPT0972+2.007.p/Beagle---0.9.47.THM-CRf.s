%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:35 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 313 expanded)
%              Number of leaves         :   38 ( 123 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 914 expanded)
%              Number of equality atoms :   55 ( 215 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_131,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_50,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_359,plain,(
    ! [C_104,B_105,A_106] :
      ( v1_xboole_0(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(B_105,A_106)))
      | ~ v1_xboole_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_380,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_359])).

tff(c_387,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_729,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( r2_relset_1(A_138,B_139,C_140,C_140)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_775,plain,(
    ! [C_149] :
      ( r2_relset_1('#skF_4','#skF_5',C_149,C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_60,c_729])).

tff(c_790,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_775])).

tff(c_124,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_144,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_124])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_431,plain,(
    ! [A_109,B_110,C_111] :
      ( k1_relset_1(A_109,B_110,C_111) = k1_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_453,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_431])).

tff(c_660,plain,(
    ! [B_132,A_133,C_134] :
      ( k1_xboole_0 = B_132
      | k1_relset_1(A_133,B_132,C_134) = A_133
      | ~ v1_funct_2(C_134,A_133,B_132)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_670,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_660])).

tff(c_691,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_453,c_670])).

tff(c_704,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_691])).

tff(c_143,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_124])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_452,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_431])).

tff(c_667,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_660])).

tff(c_688,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_452,c_667])).

tff(c_696,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_688])).

tff(c_810,plain,(
    ! [A_152,B_153] :
      ( r2_hidden('#skF_3'(A_152,B_153),k1_relat_1(A_152))
      | B_153 = A_152
      | k1_relat_1(B_153) != k1_relat_1(A_152)
      | ~ v1_funct_1(B_153)
      | ~ v1_relat_1(B_153)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_818,plain,(
    ! [B_153] :
      ( r2_hidden('#skF_3'('#skF_6',B_153),'#skF_4')
      | B_153 = '#skF_6'
      | k1_relat_1(B_153) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_153)
      | ~ v1_relat_1(B_153)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_810])).

tff(c_2003,plain,(
    ! [B_234] :
      ( r2_hidden('#skF_3'('#skF_6',B_234),'#skF_4')
      | B_234 = '#skF_6'
      | k1_relat_1(B_234) != '#skF_4'
      | ~ v1_funct_1(B_234)
      | ~ v1_relat_1(B_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_70,c_696,c_818])).

tff(c_58,plain,(
    ! [E_50] :
      ( k1_funct_1('#skF_7',E_50) = k1_funct_1('#skF_6',E_50)
      | ~ r2_hidden(E_50,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2138,plain,(
    ! [B_246] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_246)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_246))
      | B_246 = '#skF_6'
      | k1_relat_1(B_246) != '#skF_4'
      | ~ v1_funct_1(B_246)
      | ~ v1_relat_1(B_246) ) ),
    inference(resolution,[status(thm)],[c_2003,c_58])).

tff(c_28,plain,(
    ! [B_24,A_20] :
      ( k1_funct_1(B_24,'#skF_3'(A_20,B_24)) != k1_funct_1(A_20,'#skF_3'(A_20,B_24))
      | B_24 = A_20
      | k1_relat_1(B_24) != k1_relat_1(A_20)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2145,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_28])).

tff(c_2152,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_64,c_704,c_143,c_70,c_704,c_696,c_2145])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2167,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2152,c_56])).

tff(c_2180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_2167])).

tff(c_2181,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_691])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2207,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2181,c_8])).

tff(c_2209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_387,c_2207])).

tff(c_2210,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_688])).

tff(c_2236,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2210,c_8])).

tff(c_2238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_387,c_2236])).

tff(c_2239,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_101,plain,(
    ! [B_56,A_57] :
      ( ~ v1_xboole_0(B_56)
      | B_56 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_8,c_101])).

tff(c_2246,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2239,c_104])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2296,plain,(
    ! [A_12] : m1_subset_1('#skF_6',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2246,c_20])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1('#skF_2'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2681,plain,(
    ! [A_284,B_285,C_286,D_287] :
      ( r2_relset_1(A_284,B_285,C_286,C_286)
      | ~ m1_subset_1(D_287,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285)))
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2942,plain,(
    ! [A_319,B_320,C_321] :
      ( r2_relset_1(A_319,B_320,C_321,C_321)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_319,B_320))) ) ),
    inference(resolution,[status(thm)],[c_18,c_2681])).

tff(c_2957,plain,(
    ! [A_319,B_320] : r2_relset_1(A_319,B_320,'#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_2296,c_2942])).

tff(c_2240,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_2253,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2240,c_104])).

tff(c_2304,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2246,c_2253])).

tff(c_381,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_359])).

tff(c_2328,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2239,c_2304,c_381])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | B_7 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2254,plain,(
    ! [A_6] :
      ( A_6 = '#skF_5'
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_2240,c_10])).

tff(c_2335,plain,(
    ! [A_252] :
      ( A_252 = '#skF_6'
      | ~ v1_xboole_0(A_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2304,c_2254])).

tff(c_2342,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2328,c_2335])).

tff(c_2311,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2304,c_56])).

tff(c_2375,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2342,c_2311])).

tff(c_2961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_2375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:10:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.81  
% 4.63/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.81  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_1
% 4.63/1.81  
% 4.63/1.81  %Foreground sorts:
% 4.63/1.81  
% 4.63/1.81  
% 4.63/1.81  %Background operators:
% 4.63/1.81  
% 4.63/1.81  
% 4.63/1.81  %Foreground operators:
% 4.63/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.63/1.81  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.63/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.81  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.63/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.63/1.81  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.63/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.81  tff('#skF_7', type, '#skF_7': $i).
% 4.63/1.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.63/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.63/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.63/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.63/1.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.63/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.81  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.63/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.63/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.63/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.63/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.63/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.63/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.63/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.81  
% 4.74/1.83  tff(f_152, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 4.74/1.83  tff(f_103, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.74/1.83  tff(f_113, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.74/1.83  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.74/1.83  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.74/1.83  tff(f_131, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.74/1.83  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 4.74/1.83  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.74/1.83  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.74/1.83  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.74/1.83  tff(f_50, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.74/1.83  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.74/1.83  tff(c_359, plain, (![C_104, B_105, A_106]: (v1_xboole_0(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(B_105, A_106))) | ~v1_xboole_0(A_106))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.74/1.83  tff(c_380, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_359])).
% 4.74/1.83  tff(c_387, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_380])).
% 4.74/1.83  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.74/1.83  tff(c_729, plain, (![A_138, B_139, C_140, D_141]: (r2_relset_1(A_138, B_139, C_140, C_140) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.74/1.83  tff(c_775, plain, (![C_149]: (r2_relset_1('#skF_4', '#skF_5', C_149, C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_60, c_729])).
% 4.74/1.83  tff(c_790, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_775])).
% 4.74/1.83  tff(c_124, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.74/1.83  tff(c_144, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_124])).
% 4.74/1.83  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.74/1.83  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.74/1.83  tff(c_431, plain, (![A_109, B_110, C_111]: (k1_relset_1(A_109, B_110, C_111)=k1_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.74/1.83  tff(c_453, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_431])).
% 4.74/1.83  tff(c_660, plain, (![B_132, A_133, C_134]: (k1_xboole_0=B_132 | k1_relset_1(A_133, B_132, C_134)=A_133 | ~v1_funct_2(C_134, A_133, B_132) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.74/1.83  tff(c_670, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_660])).
% 4.74/1.83  tff(c_691, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_453, c_670])).
% 4.74/1.83  tff(c_704, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_691])).
% 4.74/1.83  tff(c_143, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_124])).
% 4.74/1.83  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.74/1.83  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.74/1.83  tff(c_452, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_431])).
% 4.74/1.83  tff(c_667, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_660])).
% 4.74/1.83  tff(c_688, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_452, c_667])).
% 4.74/1.83  tff(c_696, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_688])).
% 4.74/1.83  tff(c_810, plain, (![A_152, B_153]: (r2_hidden('#skF_3'(A_152, B_153), k1_relat_1(A_152)) | B_153=A_152 | k1_relat_1(B_153)!=k1_relat_1(A_152) | ~v1_funct_1(B_153) | ~v1_relat_1(B_153) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.74/1.83  tff(c_818, plain, (![B_153]: (r2_hidden('#skF_3'('#skF_6', B_153), '#skF_4') | B_153='#skF_6' | k1_relat_1(B_153)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_153) | ~v1_relat_1(B_153) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_696, c_810])).
% 4.74/1.83  tff(c_2003, plain, (![B_234]: (r2_hidden('#skF_3'('#skF_6', B_234), '#skF_4') | B_234='#skF_6' | k1_relat_1(B_234)!='#skF_4' | ~v1_funct_1(B_234) | ~v1_relat_1(B_234))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_70, c_696, c_818])).
% 4.74/1.83  tff(c_58, plain, (![E_50]: (k1_funct_1('#skF_7', E_50)=k1_funct_1('#skF_6', E_50) | ~r2_hidden(E_50, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.74/1.83  tff(c_2138, plain, (![B_246]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_246))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_246)) | B_246='#skF_6' | k1_relat_1(B_246)!='#skF_4' | ~v1_funct_1(B_246) | ~v1_relat_1(B_246))), inference(resolution, [status(thm)], [c_2003, c_58])).
% 4.74/1.83  tff(c_28, plain, (![B_24, A_20]: (k1_funct_1(B_24, '#skF_3'(A_20, B_24))!=k1_funct_1(A_20, '#skF_3'(A_20, B_24)) | B_24=A_20 | k1_relat_1(B_24)!=k1_relat_1(A_20) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.74/1.83  tff(c_2145, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2138, c_28])).
% 4.74/1.83  tff(c_2152, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_64, c_704, c_143, c_70, c_704, c_696, c_2145])).
% 4.74/1.83  tff(c_56, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.74/1.83  tff(c_2167, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2152, c_56])).
% 4.74/1.83  tff(c_2180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_790, c_2167])).
% 4.74/1.83  tff(c_2181, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_691])).
% 4.74/1.83  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.74/1.83  tff(c_2207, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2181, c_8])).
% 4.74/1.83  tff(c_2209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_387, c_2207])).
% 4.74/1.83  tff(c_2210, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_688])).
% 4.74/1.83  tff(c_2236, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2210, c_8])).
% 4.74/1.83  tff(c_2238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_387, c_2236])).
% 4.74/1.83  tff(c_2239, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_380])).
% 4.74/1.83  tff(c_101, plain, (![B_56, A_57]: (~v1_xboole_0(B_56) | B_56=A_57 | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.74/1.83  tff(c_104, plain, (![A_57]: (k1_xboole_0=A_57 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_8, c_101])).
% 4.74/1.83  tff(c_2246, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_2239, c_104])).
% 4.74/1.83  tff(c_20, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.74/1.83  tff(c_2296, plain, (![A_12]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_2246, c_20])).
% 4.74/1.83  tff(c_18, plain, (![A_10]: (m1_subset_1('#skF_2'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.74/1.83  tff(c_2681, plain, (![A_284, B_285, C_286, D_287]: (r2_relset_1(A_284, B_285, C_286, C_286) | ~m1_subset_1(D_287, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.74/1.83  tff(c_2942, plain, (![A_319, B_320, C_321]: (r2_relset_1(A_319, B_320, C_321, C_321) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_319, B_320))))), inference(resolution, [status(thm)], [c_18, c_2681])).
% 4.74/1.83  tff(c_2957, plain, (![A_319, B_320]: (r2_relset_1(A_319, B_320, '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_2296, c_2942])).
% 4.74/1.83  tff(c_2240, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_380])).
% 4.74/1.83  tff(c_2253, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2240, c_104])).
% 4.74/1.83  tff(c_2304, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2246, c_2253])).
% 4.74/1.83  tff(c_381, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_359])).
% 4.74/1.83  tff(c_2328, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2239, c_2304, c_381])).
% 4.74/1.83  tff(c_10, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | B_7=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.74/1.83  tff(c_2254, plain, (![A_6]: (A_6='#skF_5' | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_2240, c_10])).
% 4.74/1.83  tff(c_2335, plain, (![A_252]: (A_252='#skF_6' | ~v1_xboole_0(A_252))), inference(demodulation, [status(thm), theory('equality')], [c_2304, c_2254])).
% 4.74/1.83  tff(c_2342, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_2328, c_2335])).
% 4.74/1.83  tff(c_2311, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2304, c_56])).
% 4.74/1.83  tff(c_2375, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2342, c_2311])).
% 4.74/1.83  tff(c_2961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2957, c_2375])).
% 4.74/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.83  
% 4.74/1.83  Inference rules
% 4.74/1.83  ----------------------
% 4.74/1.83  #Ref     : 2
% 4.74/1.83  #Sup     : 608
% 4.74/1.83  #Fact    : 2
% 4.74/1.83  #Define  : 0
% 4.74/1.83  #Split   : 7
% 4.74/1.83  #Chain   : 0
% 4.74/1.83  #Close   : 0
% 4.74/1.83  
% 4.74/1.83  Ordering : KBO
% 4.74/1.83  
% 4.74/1.83  Simplification rules
% 4.74/1.83  ----------------------
% 4.74/1.83  #Subsume      : 146
% 4.74/1.83  #Demod        : 579
% 4.74/1.83  #Tautology    : 291
% 4.74/1.83  #SimpNegUnit  : 45
% 4.74/1.83  #BackRed      : 110
% 4.74/1.83  
% 4.74/1.83  #Partial instantiations: 0
% 4.74/1.83  #Strategies tried      : 1
% 4.74/1.83  
% 4.74/1.83  Timing (in seconds)
% 4.74/1.83  ----------------------
% 4.74/1.83  Preprocessing        : 0.33
% 4.74/1.83  Parsing              : 0.17
% 4.74/1.83  CNF conversion       : 0.02
% 4.74/1.83  Main loop            : 0.72
% 4.74/1.83  Inferencing          : 0.24
% 4.74/1.83  Reduction            : 0.26
% 4.74/1.83  Demodulation         : 0.18
% 4.74/1.83  BG Simplification    : 0.03
% 4.74/1.83  Subsumption          : 0.12
% 4.74/1.83  Abstraction          : 0.03
% 4.74/1.83  MUC search           : 0.00
% 4.74/1.83  Cooper               : 0.00
% 4.74/1.83  Total                : 1.09
% 4.74/1.83  Index Insertion      : 0.00
% 4.74/1.83  Index Deletion       : 0.00
% 4.74/1.83  Index Matching       : 0.00
% 4.74/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
