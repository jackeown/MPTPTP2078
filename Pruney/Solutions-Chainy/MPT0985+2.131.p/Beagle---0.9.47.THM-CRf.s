%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:47 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  161 (2305 expanded)
%              Number of leaves         :   32 ( 785 expanded)
%              Depth                    :   14
%              Number of atoms          :  260 (6664 expanded)
%              Number of equality atoms :  115 (2137 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_82,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_86,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_82])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_265,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_271,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_265])).

tff(c_274,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_271])).

tff(c_14,plain,(
    ! [A_4] :
      ( k1_relat_1(k2_funct_1(A_4)) = k2_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_funct_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_65,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_68,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_65])).

tff(c_71,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_68])).

tff(c_72,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_75,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_79,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_75])).

tff(c_80,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_109,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_87,plain,(
    ! [A_33] :
      ( k4_relat_1(A_33) = k2_funct_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_87])).

tff(c_93,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_90])).

tff(c_103,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_93])).

tff(c_139,plain,(
    ! [A_40,B_41,C_42] :
      ( k3_relset_1(A_40,B_41,C_42) = k4_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_142,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_139])).

tff(c_144,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_142])).

tff(c_185,plain,(
    ! [A_52,B_53,C_54] :
      ( m1_subset_1(k3_relset_1(A_52,B_53,C_54),k1_zfmisc_1(k2_zfmisc_1(B_53,A_52)))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_208,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_185])).

tff(c_216,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_208])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_216])).

tff(c_219,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_220,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_284,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_291,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_220,c_284])).

tff(c_548,plain,(
    ! [B_81,C_82,A_83] :
      ( k1_xboole_0 = B_81
      | v1_funct_2(C_82,A_83,B_81)
      | k1_relset_1(A_83,B_81,C_82) != A_83
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_563,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_220,c_548])).

tff(c_577,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_563])).

tff(c_578,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_577])).

tff(c_582,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_578])).

tff(c_585,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_582])).

tff(c_588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_48,c_42,c_274,c_585])).

tff(c_589,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_578])).

tff(c_4,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) = k1_xboole_0
      | k1_relat_1(A_1) != k1_xboole_0
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_4])).

tff(c_108,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_604,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_108])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) = k1_xboole_0
      | k2_relat_1(A_1) != k1_xboole_0
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_221,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_101])).

tff(c_275,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_221])).

tff(c_600,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_275])).

tff(c_292,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_284])).

tff(c_36,plain,(
    ! [B_21,A_20,C_22] :
      ( k1_xboole_0 = B_21
      | k1_relset_1(A_20,B_21,C_22) = A_20
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_633,plain,(
    ! [B_84,A_85,C_86] :
      ( B_84 = '#skF_1'
      | k1_relset_1(A_85,B_84,C_86) = A_85
      | ~ v1_funct_2(C_86,A_85,B_84)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_36])).

tff(c_651,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_633])).

tff(c_665,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_292,c_651])).

tff(c_667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_604,c_600,c_665])).

tff(c_668,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_1084,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1090,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1084])).

tff(c_1094,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_668,c_1090])).

tff(c_28,plain,(
    ! [C_22,A_20] :
      ( k1_xboole_0 = C_22
      | ~ v1_funct_2(C_22,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1230,plain,(
    ! [C_131,A_132] :
      ( C_131 = '#skF_2'
      | ~ v1_funct_2(C_131,A_132,'#skF_2')
      | A_132 = '#skF_2'
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,'#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_1094,c_1094,c_1094,c_28])).

tff(c_1233,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_1230])).

tff(c_1236,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1233])).

tff(c_1237,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1236])).

tff(c_700,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_703,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_700])).

tff(c_705,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_40,c_703])).

tff(c_782,plain,(
    ! [C_102,A_103] :
      ( C_102 = '#skF_2'
      | ~ v1_funct_2(C_102,A_103,'#skF_2')
      | A_103 = '#skF_2'
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,'#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_705,c_705,c_705,c_28])).

tff(c_785,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_782])).

tff(c_788,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_785])).

tff(c_789,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_788])).

tff(c_680,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_799,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_680])).

tff(c_800,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_44])).

tff(c_706,plain,(
    ! [A_93,B_94,C_95] :
      ( k3_relset_1(A_93,B_94,C_95) = k4_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_709,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_706])).

tff(c_711,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_709])).

tff(c_795,plain,(
    k3_relset_1('#skF_1','#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_711])).

tff(c_831,plain,(
    ! [A_104,B_105,C_106] :
      ( m1_subset_1(k3_relset_1(A_104,B_105,C_106),k1_zfmisc_1(k2_zfmisc_1(B_105,A_104)))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_846,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_831])).

tff(c_883,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_846])).

tff(c_884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_799,c_883])).

tff(c_885,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_788])).

tff(c_896,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_680])).

tff(c_897,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_44])).

tff(c_892,plain,(
    k3_relset_1('#skF_1','#skF_3','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_711])).

tff(c_974,plain,(
    ! [A_112,B_113,C_114] :
      ( m1_subset_1(k3_relset_1(A_112,B_113,C_114),k1_zfmisc_1(k2_zfmisc_1(B_113,A_112)))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_993,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_974])).

tff(c_1000,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_993])).

tff(c_1002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_896,c_1000])).

tff(c_1003,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1253,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_1003])).

tff(c_669,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_1019,plain,(
    ! [A_115] :
      ( k2_relat_1(k2_funct_1(A_115)) = k1_relat_1(A_115)
      | ~ v2_funct_1(A_115)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1004,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_16,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1008,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1004,c_16])).

tff(c_1015,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0
    | k1_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1008,c_4])).

tff(c_1017,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1015])).

tff(c_1016,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1008,c_2])).

tff(c_1018,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1017,c_1016])).

tff(c_1025,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_1018])).

tff(c_1032,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_48,c_42,c_669,c_1025])).

tff(c_1034,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1015])).

tff(c_1096,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_1034])).

tff(c_1142,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_relset_1(A_122,B_123,C_124) = k1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1145,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1004,c_1142])).

tff(c_1150,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_1145])).

tff(c_1244,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_1237,c_1150])).

tff(c_1252,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_1004])).

tff(c_1251,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_1094])).

tff(c_30,plain,(
    ! [C_22,B_21] :
      ( v1_funct_2(C_22,k1_xboole_0,B_21)
      | k1_relset_1(k1_xboole_0,B_21,C_22) != k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1379,plain,(
    ! [C_135,B_136] :
      ( v1_funct_2(C_135,'#skF_1',B_136)
      | k1_relset_1('#skF_1',B_136,C_135) != '#skF_1'
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_136))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1251,c_1251,c_1251,c_1251,c_30])).

tff(c_1382,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_1252,c_1379])).

tff(c_1388,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_1382])).

tff(c_1390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1253,c_1388])).

tff(c_1391,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1236])).

tff(c_1408,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_1003])).

tff(c_1399,plain,(
    k1_relset_1('#skF_3','#skF_1',k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_1391,c_1150])).

tff(c_1407,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_1004])).

tff(c_1406,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_1094])).

tff(c_1661,plain,(
    ! [C_144,B_145] :
      ( v1_funct_2(C_144,'#skF_3',B_145)
      | k1_relset_1('#skF_3',B_145,C_144) != '#skF_3'
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_145))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1406,c_1406,c_1406,c_1406,c_30])).

tff(c_1671,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1')
    | k1_relset_1('#skF_3','#skF_1',k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1407,c_1661])).

tff(c_1676,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1399,c_1671])).

tff(c_1678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1408,c_1676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:18:53 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.64  
% 3.63/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.64  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.63/1.64  
% 3.63/1.64  %Foreground sorts:
% 3.63/1.64  
% 3.63/1.64  
% 3.63/1.64  %Background operators:
% 3.63/1.64  
% 3.63/1.64  
% 3.63/1.64  %Foreground operators:
% 3.63/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.63/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.63/1.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.63/1.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.63/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.63/1.64  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 3.63/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.63/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.63/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.63/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.63/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.63/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.63/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.63/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.63/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.63/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.63/1.64  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.63/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.63/1.64  
% 3.63/1.66  tff(f_112, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.63/1.66  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.63/1.66  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.63/1.66  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.63/1.66  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.63/1.66  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 3.63/1.66  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 3.63/1.66  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 3.63/1.66  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.63/1.66  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.63/1.66  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.63/1.66  tff(c_46, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.63/1.66  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.63/1.66  tff(c_40, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.63/1.66  tff(c_82, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.63/1.66  tff(c_86, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_82])).
% 3.63/1.66  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.63/1.66  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.63/1.66  tff(c_265, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.63/1.66  tff(c_271, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_265])).
% 3.63/1.66  tff(c_274, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_271])).
% 3.63/1.66  tff(c_14, plain, (![A_4]: (k1_relat_1(k2_funct_1(A_4))=k2_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.63/1.66  tff(c_8, plain, (![A_3]: (v1_funct_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.63/1.66  tff(c_38, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.63/1.66  tff(c_65, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_38])).
% 3.63/1.66  tff(c_68, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_65])).
% 3.63/1.66  tff(c_71, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_68])).
% 3.63/1.66  tff(c_72, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.63/1.66  tff(c_75, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_72])).
% 3.63/1.66  tff(c_79, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_75])).
% 3.63/1.66  tff(c_80, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_38])).
% 3.63/1.66  tff(c_109, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_80])).
% 3.63/1.66  tff(c_87, plain, (![A_33]: (k4_relat_1(A_33)=k2_funct_1(A_33) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.66  tff(c_90, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_87])).
% 3.63/1.66  tff(c_93, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_90])).
% 3.63/1.66  tff(c_103, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_93])).
% 3.63/1.66  tff(c_139, plain, (![A_40, B_41, C_42]: (k3_relset_1(A_40, B_41, C_42)=k4_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.63/1.66  tff(c_142, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_139])).
% 3.63/1.66  tff(c_144, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_142])).
% 3.63/1.66  tff(c_185, plain, (![A_52, B_53, C_54]: (m1_subset_1(k3_relset_1(A_52, B_53, C_54), k1_zfmisc_1(k2_zfmisc_1(B_53, A_52))) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.63/1.66  tff(c_208, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_144, c_185])).
% 3.63/1.66  tff(c_216, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_208])).
% 3.63/1.66  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_216])).
% 3.63/1.66  tff(c_219, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_80])).
% 3.63/1.66  tff(c_220, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_80])).
% 3.63/1.66  tff(c_284, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.63/1.66  tff(c_291, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_220, c_284])).
% 3.63/1.66  tff(c_548, plain, (![B_81, C_82, A_83]: (k1_xboole_0=B_81 | v1_funct_2(C_82, A_83, B_81) | k1_relset_1(A_83, B_81, C_82)!=A_83 | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_81))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.63/1.66  tff(c_563, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_220, c_548])).
% 3.63/1.66  tff(c_577, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_291, c_563])).
% 3.63/1.66  tff(c_578, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_219, c_577])).
% 3.63/1.66  tff(c_582, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_578])).
% 3.63/1.66  tff(c_585, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_582])).
% 3.63/1.66  tff(c_588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_48, c_42, c_274, c_585])).
% 3.63/1.66  tff(c_589, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_578])).
% 3.63/1.66  tff(c_4, plain, (![A_1]: (k2_relat_1(A_1)=k1_xboole_0 | k1_relat_1(A_1)!=k1_xboole_0 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.63/1.66  tff(c_100, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_4])).
% 3.63/1.66  tff(c_108, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_100])).
% 3.63/1.66  tff(c_604, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_589, c_108])).
% 3.63/1.66  tff(c_2, plain, (![A_1]: (k1_relat_1(A_1)=k1_xboole_0 | k2_relat_1(A_1)!=k1_xboole_0 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.63/1.66  tff(c_101, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_2])).
% 3.63/1.66  tff(c_221, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_108, c_101])).
% 3.63/1.66  tff(c_275, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_274, c_221])).
% 3.63/1.66  tff(c_600, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_589, c_275])).
% 3.63/1.66  tff(c_292, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_284])).
% 3.63/1.66  tff(c_36, plain, (![B_21, A_20, C_22]: (k1_xboole_0=B_21 | k1_relset_1(A_20, B_21, C_22)=A_20 | ~v1_funct_2(C_22, A_20, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.63/1.66  tff(c_633, plain, (![B_84, A_85, C_86]: (B_84='#skF_1' | k1_relset_1(A_85, B_84, C_86)=A_85 | ~v1_funct_2(C_86, A_85, B_84) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(demodulation, [status(thm), theory('equality')], [c_589, c_36])).
% 3.63/1.66  tff(c_651, plain, ('#skF_2'='#skF_1' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_633])).
% 3.63/1.66  tff(c_665, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_292, c_651])).
% 3.63/1.66  tff(c_667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_604, c_600, c_665])).
% 3.63/1.66  tff(c_668, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_100])).
% 3.63/1.66  tff(c_1084, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.63/1.66  tff(c_1090, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1084])).
% 3.63/1.66  tff(c_1094, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_668, c_1090])).
% 3.63/1.66  tff(c_28, plain, (![C_22, A_20]: (k1_xboole_0=C_22 | ~v1_funct_2(C_22, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.63/1.66  tff(c_1230, plain, (![C_131, A_132]: (C_131='#skF_2' | ~v1_funct_2(C_131, A_132, '#skF_2') | A_132='#skF_2' | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_1094, c_1094, c_1094, c_28])).
% 3.63/1.66  tff(c_1233, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_44, c_1230])).
% 3.63/1.66  tff(c_1236, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1233])).
% 3.63/1.66  tff(c_1237, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_1236])).
% 3.63/1.66  tff(c_700, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.63/1.66  tff(c_703, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_700])).
% 3.63/1.66  tff(c_705, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_668, c_40, c_703])).
% 3.63/1.66  tff(c_782, plain, (![C_102, A_103]: (C_102='#skF_2' | ~v1_funct_2(C_102, A_103, '#skF_2') | A_103='#skF_2' | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_705, c_705, c_705, c_705, c_28])).
% 3.63/1.66  tff(c_785, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_44, c_782])).
% 3.63/1.66  tff(c_788, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_785])).
% 3.63/1.66  tff(c_789, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_788])).
% 3.63/1.66  tff(c_680, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_80])).
% 3.63/1.66  tff(c_799, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_789, c_680])).
% 3.63/1.66  tff(c_800, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_789, c_44])).
% 3.63/1.66  tff(c_706, plain, (![A_93, B_94, C_95]: (k3_relset_1(A_93, B_94, C_95)=k4_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.63/1.66  tff(c_709, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_706])).
% 3.63/1.66  tff(c_711, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_709])).
% 3.63/1.66  tff(c_795, plain, (k3_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_789, c_711])).
% 3.63/1.66  tff(c_831, plain, (![A_104, B_105, C_106]: (m1_subset_1(k3_relset_1(A_104, B_105, C_106), k1_zfmisc_1(k2_zfmisc_1(B_105, A_104))) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.63/1.66  tff(c_846, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_795, c_831])).
% 3.63/1.66  tff(c_883, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_800, c_846])).
% 3.63/1.66  tff(c_884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_799, c_883])).
% 3.63/1.66  tff(c_885, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_788])).
% 3.63/1.66  tff(c_896, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_885, c_680])).
% 3.63/1.66  tff(c_897, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_885, c_44])).
% 3.63/1.66  tff(c_892, plain, (k3_relset_1('#skF_1', '#skF_3', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_885, c_711])).
% 3.63/1.66  tff(c_974, plain, (![A_112, B_113, C_114]: (m1_subset_1(k3_relset_1(A_112, B_113, C_114), k1_zfmisc_1(k2_zfmisc_1(B_113, A_112))) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.63/1.66  tff(c_993, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_892, c_974])).
% 3.63/1.66  tff(c_1000, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_897, c_993])).
% 3.63/1.66  tff(c_1002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_896, c_1000])).
% 3.63/1.66  tff(c_1003, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_80])).
% 3.63/1.66  tff(c_1253, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_1003])).
% 3.63/1.66  tff(c_669, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_100])).
% 3.63/1.66  tff(c_1019, plain, (![A_115]: (k2_relat_1(k2_funct_1(A_115))=k1_relat_1(A_115) | ~v2_funct_1(A_115) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.63/1.66  tff(c_1004, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_80])).
% 3.63/1.66  tff(c_16, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.63/1.66  tff(c_1008, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1004, c_16])).
% 3.63/1.66  tff(c_1015, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0 | k1_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1008, c_4])).
% 3.63/1.66  tff(c_1017, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1015])).
% 3.63/1.66  tff(c_1016, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0 | k2_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1008, c_2])).
% 3.63/1.66  tff(c_1018, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1017, c_1016])).
% 3.63/1.66  tff(c_1025, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1019, c_1018])).
% 3.63/1.66  tff(c_1032, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_48, c_42, c_669, c_1025])).
% 3.63/1.66  tff(c_1034, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1015])).
% 3.63/1.66  tff(c_1096, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_1034])).
% 3.63/1.66  tff(c_1142, plain, (![A_122, B_123, C_124]: (k1_relset_1(A_122, B_123, C_124)=k1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.63/1.66  tff(c_1145, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1004, c_1142])).
% 3.63/1.66  tff(c_1150, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1096, c_1145])).
% 3.63/1.66  tff(c_1244, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_1237, c_1150])).
% 3.63/1.66  tff(c_1252, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_1004])).
% 3.63/1.66  tff(c_1251, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_1094])).
% 3.63/1.66  tff(c_30, plain, (![C_22, B_21]: (v1_funct_2(C_22, k1_xboole_0, B_21) | k1_relset_1(k1_xboole_0, B_21, C_22)!=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.63/1.66  tff(c_1379, plain, (![C_135, B_136]: (v1_funct_2(C_135, '#skF_1', B_136) | k1_relset_1('#skF_1', B_136, C_135)!='#skF_1' | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_136))))), inference(demodulation, [status(thm), theory('equality')], [c_1251, c_1251, c_1251, c_1251, c_30])).
% 3.63/1.66  tff(c_1382, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))!='#skF_1'), inference(resolution, [status(thm)], [c_1252, c_1379])).
% 3.63/1.66  tff(c_1388, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1244, c_1382])).
% 3.63/1.66  tff(c_1390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1253, c_1388])).
% 3.63/1.66  tff(c_1391, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1236])).
% 3.63/1.66  tff(c_1408, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1391, c_1003])).
% 3.63/1.66  tff(c_1399, plain, (k1_relset_1('#skF_3', '#skF_1', k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1391, c_1391, c_1150])).
% 3.63/1.66  tff(c_1407, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1391, c_1004])).
% 3.63/1.66  tff(c_1406, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1391, c_1094])).
% 3.63/1.66  tff(c_1661, plain, (![C_144, B_145]: (v1_funct_2(C_144, '#skF_3', B_145) | k1_relset_1('#skF_3', B_145, C_144)!='#skF_3' | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_145))))), inference(demodulation, [status(thm), theory('equality')], [c_1406, c_1406, c_1406, c_1406, c_30])).
% 3.63/1.66  tff(c_1671, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1') | k1_relset_1('#skF_3', '#skF_1', k2_funct_1('#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_1407, c_1661])).
% 3.63/1.66  tff(c_1676, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1399, c_1671])).
% 3.63/1.66  tff(c_1678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1408, c_1676])).
% 3.63/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.66  
% 3.63/1.66  Inference rules
% 3.63/1.66  ----------------------
% 3.63/1.66  #Ref     : 0
% 3.63/1.66  #Sup     : 394
% 3.63/1.66  #Fact    : 0
% 3.63/1.66  #Define  : 0
% 3.63/1.66  #Split   : 11
% 3.63/1.66  #Chain   : 0
% 3.63/1.66  #Close   : 0
% 3.63/1.66  
% 3.63/1.66  Ordering : KBO
% 3.63/1.66  
% 3.63/1.66  Simplification rules
% 3.63/1.66  ----------------------
% 3.63/1.66  #Subsume      : 8
% 3.63/1.66  #Demod        : 414
% 3.63/1.66  #Tautology    : 247
% 3.63/1.66  #SimpNegUnit  : 18
% 3.63/1.66  #BackRed      : 96
% 3.63/1.66  
% 3.63/1.66  #Partial instantiations: 0
% 3.63/1.66  #Strategies tried      : 1
% 3.63/1.66  
% 3.63/1.66  Timing (in seconds)
% 3.63/1.66  ----------------------
% 3.63/1.67  Preprocessing        : 0.34
% 3.63/1.67  Parsing              : 0.19
% 3.63/1.67  CNF conversion       : 0.02
% 3.63/1.67  Main loop            : 0.49
% 3.63/1.67  Inferencing          : 0.17
% 3.63/1.67  Reduction            : 0.16
% 3.63/1.67  Demodulation         : 0.11
% 3.63/1.67  BG Simplification    : 0.03
% 3.63/1.67  Subsumption          : 0.08
% 3.63/1.67  Abstraction          : 0.03
% 3.63/1.67  MUC search           : 0.00
% 3.63/1.67  Cooper               : 0.00
% 3.63/1.67  Total                : 0.89
% 3.63/1.67  Index Insertion      : 0.00
% 3.63/1.67  Index Deletion       : 0.00
% 3.63/1.67  Index Matching       : 0.00
% 3.63/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
