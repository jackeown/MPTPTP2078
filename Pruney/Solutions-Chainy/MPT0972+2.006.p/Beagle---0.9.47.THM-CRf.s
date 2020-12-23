%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:35 EST 2020

% Result     : Theorem 5.09s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 296 expanded)
%              Number of leaves         :   38 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  164 ( 867 expanded)
%              Number of equality atoms :   53 ( 208 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_1

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

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

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

tff(f_151,negated_conjecture,(
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

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_85,axiom,(
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

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_55,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_324,plain,(
    ! [C_101,B_102,A_103] :
      ( v1_xboole_0(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(B_102,A_103)))
      | ~ v1_xboole_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_345,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_324])).

tff(c_352,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_594,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( r2_relset_1(A_131,B_132,C_133,C_133)
      | ~ m1_subset_1(D_134,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_637,plain,(
    ! [C_145] :
      ( r2_relset_1('#skF_4','#skF_5',C_145,C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_62,c_594])).

tff(c_652,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_637])).

tff(c_139,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_159,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_139])).

tff(c_66,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_64,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_411,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_433,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_411])).

tff(c_1048,plain,(
    ! [B_182,A_183,C_184] :
      ( k1_xboole_0 = B_182
      | k1_relset_1(A_183,B_182,C_184) = A_183
      | ~ v1_funct_2(C_184,A_183,B_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1066,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_1048])).

tff(c_1089,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_433,c_1066])).

tff(c_1115,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1089])).

tff(c_158,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_139])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_70,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_432,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_411])).

tff(c_1063,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_1048])).

tff(c_1086,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_432,c_1063])).

tff(c_1094,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1086])).

tff(c_1163,plain,(
    ! [A_188,B_189] :
      ( r2_hidden('#skF_3'(A_188,B_189),k1_relat_1(A_188))
      | B_189 = A_188
      | k1_relat_1(B_189) != k1_relat_1(A_188)
      | ~ v1_funct_1(B_189)
      | ~ v1_relat_1(B_189)
      | ~ v1_funct_1(A_188)
      | ~ v1_relat_1(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1171,plain,(
    ! [B_189] :
      ( r2_hidden('#skF_3'('#skF_6',B_189),'#skF_4')
      | B_189 = '#skF_6'
      | k1_relat_1(B_189) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_189)
      | ~ v1_relat_1(B_189)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_1163])).

tff(c_2365,plain,(
    ! [B_297] :
      ( r2_hidden('#skF_3'('#skF_6',B_297),'#skF_4')
      | B_297 = '#skF_6'
      | k1_relat_1(B_297) != '#skF_4'
      | ~ v1_funct_1(B_297)
      | ~ v1_relat_1(B_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_72,c_1094,c_1171])).

tff(c_60,plain,(
    ! [E_48] :
      ( k1_funct_1('#skF_7',E_48) = k1_funct_1('#skF_6',E_48)
      | ~ r2_hidden(E_48,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2490,plain,(
    ! [B_303] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_303)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_303))
      | B_303 = '#skF_6'
      | k1_relat_1(B_303) != '#skF_4'
      | ~ v1_funct_1(B_303)
      | ~ v1_relat_1(B_303) ) ),
    inference(resolution,[status(thm)],[c_2365,c_60])).

tff(c_30,plain,(
    ! [B_22,A_18] :
      ( k1_funct_1(B_22,'#skF_3'(A_18,B_22)) != k1_funct_1(A_18,'#skF_3'(A_18,B_22))
      | B_22 = A_18
      | k1_relat_1(B_22) != k1_relat_1(A_18)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2500,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2490,c_30])).

tff(c_2514,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_66,c_1115,c_158,c_72,c_1094,c_1115,c_2500])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2538,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2514,c_58])).

tff(c_2550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_2538])).

tff(c_2551,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1089])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2594,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2551,c_8])).

tff(c_2596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_2594])).

tff(c_2597,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1086])).

tff(c_2640,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2597,c_8])).

tff(c_2642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_2640])).

tff(c_2643,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_104,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_8,c_104])).

tff(c_2650,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2643,c_107])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2684,plain,(
    ! [A_10] : m1_subset_1('#skF_6',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2650,c_18])).

tff(c_22,plain,(
    ! [A_11] : m1_subset_1('#skF_2'(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3100,plain,(
    ! [A_348,B_349,C_350,D_351] :
      ( r2_relset_1(A_348,B_349,C_350,C_350)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(k2_zfmisc_1(A_348,B_349)))
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_348,B_349))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3264,plain,(
    ! [A_375,B_376,C_377] :
      ( r2_relset_1(A_375,B_376,C_377,C_377)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376))) ) ),
    inference(resolution,[status(thm)],[c_22,c_3100])).

tff(c_3279,plain,(
    ! [A_375,B_376] : r2_relset_1(A_375,B_376,'#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_2684,c_3264])).

tff(c_2644,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_2657,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2644,c_107])).

tff(c_2694,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2650,c_2657])).

tff(c_346,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_324])).

tff(c_2711,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2643,c_2694,c_346])).

tff(c_2756,plain,(
    ! [A_313] :
      ( A_313 = '#skF_6'
      | ~ v1_xboole_0(A_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2650,c_107])).

tff(c_2763,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2711,c_2756])).

tff(c_2700,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2694,c_58])).

tff(c_2868,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2763,c_2700])).

tff(c_3283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3279,c_2868])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:57:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.09/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/1.97  
% 5.09/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/1.97  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_1
% 5.09/1.97  
% 5.09/1.97  %Foreground sorts:
% 5.09/1.97  
% 5.09/1.97  
% 5.09/1.97  %Background operators:
% 5.09/1.97  
% 5.09/1.97  
% 5.09/1.97  %Foreground operators:
% 5.09/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.09/1.97  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.09/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.09/1.97  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.09/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.09/1.97  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.09/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.09/1.97  tff('#skF_7', type, '#skF_7': $i).
% 5.09/1.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.09/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.09/1.97  tff('#skF_5', type, '#skF_5': $i).
% 5.09/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.09/1.97  tff('#skF_6', type, '#skF_6': $i).
% 5.09/1.97  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.09/1.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.09/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.09/1.97  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.09/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.09/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.09/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.09/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.09/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.09/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.09/1.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.09/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.09/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.09/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.09/1.97  
% 5.31/1.99  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 5.31/1.99  tff(f_102, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.31/1.99  tff(f_112, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.31/1.99  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.31/1.99  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.31/1.99  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.31/1.99  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 5.31/1.99  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.31/1.99  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 5.31/1.99  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.31/1.99  tff(f_55, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 5.31/1.99  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.31/1.99  tff(c_324, plain, (![C_101, B_102, A_103]: (v1_xboole_0(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(B_102, A_103))) | ~v1_xboole_0(A_103))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.31/1.99  tff(c_345, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_324])).
% 5.31/1.99  tff(c_352, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_345])).
% 5.31/1.99  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.31/1.99  tff(c_594, plain, (![A_131, B_132, C_133, D_134]: (r2_relset_1(A_131, B_132, C_133, C_133) | ~m1_subset_1(D_134, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.31/1.99  tff(c_637, plain, (![C_145]: (r2_relset_1('#skF_4', '#skF_5', C_145, C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_62, c_594])).
% 5.31/1.99  tff(c_652, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_637])).
% 5.31/1.99  tff(c_139, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.31/1.99  tff(c_159, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_62, c_139])).
% 5.31/1.99  tff(c_66, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.31/1.99  tff(c_64, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.31/1.99  tff(c_411, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.31/1.99  tff(c_433, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_62, c_411])).
% 5.31/1.99  tff(c_1048, plain, (![B_182, A_183, C_184]: (k1_xboole_0=B_182 | k1_relset_1(A_183, B_182, C_184)=A_183 | ~v1_funct_2(C_184, A_183, B_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.31/1.99  tff(c_1066, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_1048])).
% 5.31/1.99  tff(c_1089, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_433, c_1066])).
% 5.31/1.99  tff(c_1115, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_1089])).
% 5.31/1.99  tff(c_158, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_139])).
% 5.31/1.99  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.31/1.99  tff(c_70, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.31/1.99  tff(c_432, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_411])).
% 5.31/1.99  tff(c_1063, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_1048])).
% 5.31/1.99  tff(c_1086, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_432, c_1063])).
% 5.31/1.99  tff(c_1094, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1086])).
% 5.31/1.99  tff(c_1163, plain, (![A_188, B_189]: (r2_hidden('#skF_3'(A_188, B_189), k1_relat_1(A_188)) | B_189=A_188 | k1_relat_1(B_189)!=k1_relat_1(A_188) | ~v1_funct_1(B_189) | ~v1_relat_1(B_189) | ~v1_funct_1(A_188) | ~v1_relat_1(A_188))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.31/1.99  tff(c_1171, plain, (![B_189]: (r2_hidden('#skF_3'('#skF_6', B_189), '#skF_4') | B_189='#skF_6' | k1_relat_1(B_189)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_189) | ~v1_relat_1(B_189) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1094, c_1163])).
% 5.31/1.99  tff(c_2365, plain, (![B_297]: (r2_hidden('#skF_3'('#skF_6', B_297), '#skF_4') | B_297='#skF_6' | k1_relat_1(B_297)!='#skF_4' | ~v1_funct_1(B_297) | ~v1_relat_1(B_297))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_72, c_1094, c_1171])).
% 5.31/1.99  tff(c_60, plain, (![E_48]: (k1_funct_1('#skF_7', E_48)=k1_funct_1('#skF_6', E_48) | ~r2_hidden(E_48, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.31/1.99  tff(c_2490, plain, (![B_303]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_303))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_303)) | B_303='#skF_6' | k1_relat_1(B_303)!='#skF_4' | ~v1_funct_1(B_303) | ~v1_relat_1(B_303))), inference(resolution, [status(thm)], [c_2365, c_60])).
% 5.31/1.99  tff(c_30, plain, (![B_22, A_18]: (k1_funct_1(B_22, '#skF_3'(A_18, B_22))!=k1_funct_1(A_18, '#skF_3'(A_18, B_22)) | B_22=A_18 | k1_relat_1(B_22)!=k1_relat_1(A_18) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.31/1.99  tff(c_2500, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2490, c_30])).
% 5.31/1.99  tff(c_2514, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_66, c_1115, c_158, c_72, c_1094, c_1115, c_2500])).
% 5.31/1.99  tff(c_58, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.31/1.99  tff(c_2538, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2514, c_58])).
% 5.31/1.99  tff(c_2550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_652, c_2538])).
% 5.31/1.99  tff(c_2551, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1089])).
% 5.31/1.99  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.31/1.99  tff(c_2594, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2551, c_8])).
% 5.31/1.99  tff(c_2596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_352, c_2594])).
% 5.31/1.99  tff(c_2597, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1086])).
% 5.31/1.99  tff(c_2640, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2597, c_8])).
% 5.31/1.99  tff(c_2642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_352, c_2640])).
% 5.31/1.99  tff(c_2643, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_345])).
% 5.31/1.99  tff(c_104, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.31/1.99  tff(c_107, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_8, c_104])).
% 5.31/1.99  tff(c_2650, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_2643, c_107])).
% 5.31/1.99  tff(c_18, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.31/1.99  tff(c_2684, plain, (![A_10]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_2650, c_18])).
% 5.31/1.99  tff(c_22, plain, (![A_11]: (m1_subset_1('#skF_2'(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.31/1.99  tff(c_3100, plain, (![A_348, B_349, C_350, D_351]: (r2_relset_1(A_348, B_349, C_350, C_350) | ~m1_subset_1(D_351, k1_zfmisc_1(k2_zfmisc_1(A_348, B_349))) | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_348, B_349))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.31/1.99  tff(c_3264, plain, (![A_375, B_376, C_377]: (r2_relset_1(A_375, B_376, C_377, C_377) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))))), inference(resolution, [status(thm)], [c_22, c_3100])).
% 5.31/1.99  tff(c_3279, plain, (![A_375, B_376]: (r2_relset_1(A_375, B_376, '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_2684, c_3264])).
% 5.31/1.99  tff(c_2644, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_345])).
% 5.31/1.99  tff(c_2657, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2644, c_107])).
% 5.31/1.99  tff(c_2694, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2650, c_2657])).
% 5.31/1.99  tff(c_346, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_324])).
% 5.31/1.99  tff(c_2711, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2643, c_2694, c_346])).
% 5.31/1.99  tff(c_2756, plain, (![A_313]: (A_313='#skF_6' | ~v1_xboole_0(A_313))), inference(demodulation, [status(thm), theory('equality')], [c_2650, c_107])).
% 5.31/1.99  tff(c_2763, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_2711, c_2756])).
% 5.31/1.99  tff(c_2700, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2694, c_58])).
% 5.31/1.99  tff(c_2868, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2763, c_2700])).
% 5.31/1.99  tff(c_3283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3279, c_2868])).
% 5.31/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/1.99  
% 5.31/1.99  Inference rules
% 5.31/1.99  ----------------------
% 5.31/1.99  #Ref     : 2
% 5.31/1.99  #Sup     : 700
% 5.31/1.99  #Fact    : 0
% 5.31/1.99  #Define  : 0
% 5.31/1.99  #Split   : 12
% 5.31/1.99  #Chain   : 0
% 5.31/1.99  #Close   : 0
% 5.31/1.99  
% 5.31/1.99  Ordering : KBO
% 5.31/1.99  
% 5.31/1.99  Simplification rules
% 5.31/1.99  ----------------------
% 5.31/1.99  #Subsume      : 216
% 5.31/1.99  #Demod        : 699
% 5.31/1.99  #Tautology    : 283
% 5.31/1.99  #SimpNegUnit  : 13
% 5.31/1.99  #BackRed      : 145
% 5.31/1.99  
% 5.31/1.99  #Partial instantiations: 0
% 5.31/1.99  #Strategies tried      : 1
% 5.31/1.99  
% 5.31/1.99  Timing (in seconds)
% 5.31/1.99  ----------------------
% 5.31/1.99  Preprocessing        : 0.36
% 5.31/1.99  Parsing              : 0.18
% 5.31/1.99  CNF conversion       : 0.03
% 5.31/1.99  Main loop            : 0.84
% 5.31/1.99  Inferencing          : 0.28
% 5.31/1.99  Reduction            : 0.29
% 5.31/1.99  Demodulation         : 0.21
% 5.31/1.99  BG Simplification    : 0.04
% 5.31/1.99  Subsumption          : 0.16
% 5.31/1.99  Abstraction          : 0.04
% 5.31/1.99  MUC search           : 0.00
% 5.31/1.99  Cooper               : 0.00
% 5.31/1.99  Total                : 1.23
% 5.31/1.99  Index Insertion      : 0.00
% 5.31/1.99  Index Deletion       : 0.00
% 5.31/1.99  Index Matching       : 0.00
% 5.31/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
