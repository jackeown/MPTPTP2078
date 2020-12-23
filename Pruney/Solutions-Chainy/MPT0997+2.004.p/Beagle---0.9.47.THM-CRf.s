%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:52 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 272 expanded)
%              Number of leaves         :   28 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 637 expanded)
%              Number of equality atoms :   65 ( 393 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_140,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k7_relset_1(A_51,B_52,C_53,D_54) = k9_relat_1(C_53,D_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_147,plain,(
    ! [D_54] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_54) = k9_relat_1('#skF_3',D_54) ),
    inference(resolution,[status(thm)],[c_36,c_140])).

tff(c_102,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_relset_1(A_31,B_32,C_33) = k2_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_112,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_102])).

tff(c_32,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_113,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_32])).

tff(c_148,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_113])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_83,plain,(
    ! [B_27,A_28] :
      ( v1_relat_1(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_86,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_83])).

tff(c_89,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_86])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_45,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_38,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_118,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_relset_1(A_34,B_35,C_36) = k1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_128,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_174,plain,(
    ! [B_65,A_66,C_67] :
      ( k1_xboole_0 = B_65
      | k1_relset_1(A_66,B_65,C_67) = A_66
      | ~ v1_funct_2(C_67,A_66,B_65)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_177,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_174])).

tff(c_186,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_128,c_177])).

tff(c_187,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_186])).

tff(c_12,plain,(
    ! [A_8] :
      ( k9_relat_1(A_8,k1_relat_1(A_8)) = k2_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_193,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_12])).

tff(c_197,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_193])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_197])).

tff(c_200,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_216,plain,(
    ! [A_70] : k2_zfmisc_1(A_70,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_4])).

tff(c_220,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_10])).

tff(c_214,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_4])).

tff(c_201,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_206,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_201])).

tff(c_213,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_36])).

tff(c_215,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_213])).

tff(c_244,plain,(
    ! [B_72,A_73] :
      ( v1_relat_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_247,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_215,c_244])).

tff(c_250,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_247])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_225,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_6])).

tff(c_321,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_328,plain,(
    ! [B_91,C_92] :
      ( k1_relset_1('#skF_1',B_91,C_92) = k1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_321])).

tff(c_331,plain,(
    ! [B_91] : k1_relset_1('#skF_1',B_91,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_215,c_328])).

tff(c_207,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_38])).

tff(c_28,plain,(
    ! [B_20,C_21] :
      ( k1_relset_1(k1_xboole_0,B_20,C_21) = k1_xboole_0
      | ~ v1_funct_2(C_21,k1_xboole_0,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    ! [B_20,C_21] :
      ( k1_relset_1(k1_xboole_0,B_20,C_21) = k1_xboole_0
      | ~ v1_funct_2(C_21,k1_xboole_0,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_365,plain,(
    ! [B_99,C_100] :
      ( k1_relset_1('#skF_1',B_99,C_100) = '#skF_1'
      | ~ v1_funct_2(C_100,'#skF_1',B_99)
      | ~ m1_subset_1(C_100,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_200,c_200,c_42])).

tff(c_367,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_207,c_365])).

tff(c_370,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_331,c_367])).

tff(c_376,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_12])).

tff(c_380,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_376])).

tff(c_424,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k7_relset_1(A_104,B_105,C_106,D_107) = k9_relat_1(C_106,D_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_429,plain,(
    ! [B_108,C_109,D_110] :
      ( k7_relset_1('#skF_1',B_108,C_109,D_110) = k9_relat_1(C_109,D_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_424])).

tff(c_432,plain,(
    ! [B_108,D_110] : k7_relset_1('#skF_1',B_108,'#skF_3',D_110) = k9_relat_1('#skF_3',D_110) ),
    inference(resolution,[status(thm)],[c_215,c_429])).

tff(c_275,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_282,plain,(
    ! [B_80,C_81] :
      ( k2_relset_1('#skF_1',B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_275])).

tff(c_285,plain,(
    ! [B_80] : k2_relset_1('#skF_1',B_80,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_215,c_282])).

tff(c_272,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_206,c_32])).

tff(c_286,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_272])).

tff(c_433,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_286])).

tff(c_436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.35  
% 2.43/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.36  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.43/1.36  
% 2.43/1.36  %Foreground sorts:
% 2.43/1.36  
% 2.43/1.36  
% 2.43/1.36  %Background operators:
% 2.43/1.36  
% 2.43/1.36  
% 2.43/1.36  %Foreground operators:
% 2.43/1.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.43/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.43/1.36  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.43/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.43/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.43/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.43/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.43/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.36  
% 2.43/1.38  tff(f_87, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_funct_2)).
% 2.43/1.38  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.43/1.38  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.43/1.38  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.43/1.38  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.43/1.38  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.43/1.38  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.43/1.38  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.43/1.38  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.43/1.38  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.43/1.38  tff(c_140, plain, (![A_51, B_52, C_53, D_54]: (k7_relset_1(A_51, B_52, C_53, D_54)=k9_relat_1(C_53, D_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.43/1.38  tff(c_147, plain, (![D_54]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_54)=k9_relat_1('#skF_3', D_54))), inference(resolution, [status(thm)], [c_36, c_140])).
% 2.43/1.38  tff(c_102, plain, (![A_31, B_32, C_33]: (k2_relset_1(A_31, B_32, C_33)=k2_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.43/1.38  tff(c_112, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_102])).
% 2.43/1.38  tff(c_32, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.43/1.38  tff(c_113, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_32])).
% 2.43/1.38  tff(c_148, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_113])).
% 2.43/1.38  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.43/1.38  tff(c_83, plain, (![B_27, A_28]: (v1_relat_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.43/1.38  tff(c_86, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_83])).
% 2.43/1.38  tff(c_89, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_86])).
% 2.43/1.38  tff(c_34, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.43/1.38  tff(c_45, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 2.43/1.38  tff(c_38, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.43/1.38  tff(c_118, plain, (![A_34, B_35, C_36]: (k1_relset_1(A_34, B_35, C_36)=k1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.43/1.38  tff(c_128, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_118])).
% 2.43/1.38  tff(c_174, plain, (![B_65, A_66, C_67]: (k1_xboole_0=B_65 | k1_relset_1(A_66, B_65, C_67)=A_66 | ~v1_funct_2(C_67, A_66, B_65) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.43/1.38  tff(c_177, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_174])).
% 2.43/1.38  tff(c_186, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_128, c_177])).
% 2.43/1.38  tff(c_187, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_45, c_186])).
% 2.43/1.38  tff(c_12, plain, (![A_8]: (k9_relat_1(A_8, k1_relat_1(A_8))=k2_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.43/1.38  tff(c_193, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_187, c_12])).
% 2.43/1.38  tff(c_197, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_193])).
% 2.43/1.38  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_197])).
% 2.43/1.38  tff(c_200, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_34])).
% 2.43/1.38  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.38  tff(c_216, plain, (![A_70]: (k2_zfmisc_1(A_70, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_4])).
% 2.43/1.38  tff(c_220, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_216, c_10])).
% 2.43/1.38  tff(c_214, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_4])).
% 2.43/1.38  tff(c_201, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 2.43/1.38  tff(c_206, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_201])).
% 2.43/1.38  tff(c_213, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_36])).
% 2.43/1.38  tff(c_215, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_213])).
% 2.43/1.38  tff(c_244, plain, (![B_72, A_73]: (v1_relat_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.43/1.38  tff(c_247, plain, (v1_relat_1('#skF_3') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_215, c_244])).
% 2.43/1.38  tff(c_250, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_247])).
% 2.43/1.38  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.38  tff(c_225, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_6])).
% 2.43/1.38  tff(c_321, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.43/1.38  tff(c_328, plain, (![B_91, C_92]: (k1_relset_1('#skF_1', B_91, C_92)=k1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_225, c_321])).
% 2.43/1.38  tff(c_331, plain, (![B_91]: (k1_relset_1('#skF_1', B_91, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_215, c_328])).
% 2.43/1.38  tff(c_207, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_38])).
% 2.43/1.38  tff(c_28, plain, (![B_20, C_21]: (k1_relset_1(k1_xboole_0, B_20, C_21)=k1_xboole_0 | ~v1_funct_2(C_21, k1_xboole_0, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_20))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.43/1.38  tff(c_42, plain, (![B_20, C_21]: (k1_relset_1(k1_xboole_0, B_20, C_21)=k1_xboole_0 | ~v1_funct_2(C_21, k1_xboole_0, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_28])).
% 2.43/1.38  tff(c_365, plain, (![B_99, C_100]: (k1_relset_1('#skF_1', B_99, C_100)='#skF_1' | ~v1_funct_2(C_100, '#skF_1', B_99) | ~m1_subset_1(C_100, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_200, c_200, c_42])).
% 2.43/1.38  tff(c_367, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_207, c_365])).
% 2.43/1.38  tff(c_370, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_215, c_331, c_367])).
% 2.43/1.38  tff(c_376, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_370, c_12])).
% 2.43/1.38  tff(c_380, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_250, c_376])).
% 2.43/1.38  tff(c_424, plain, (![A_104, B_105, C_106, D_107]: (k7_relset_1(A_104, B_105, C_106, D_107)=k9_relat_1(C_106, D_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.43/1.38  tff(c_429, plain, (![B_108, C_109, D_110]: (k7_relset_1('#skF_1', B_108, C_109, D_110)=k9_relat_1(C_109, D_110) | ~m1_subset_1(C_109, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_225, c_424])).
% 2.43/1.38  tff(c_432, plain, (![B_108, D_110]: (k7_relset_1('#skF_1', B_108, '#skF_3', D_110)=k9_relat_1('#skF_3', D_110))), inference(resolution, [status(thm)], [c_215, c_429])).
% 2.43/1.38  tff(c_275, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.43/1.38  tff(c_282, plain, (![B_80, C_81]: (k2_relset_1('#skF_1', B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_225, c_275])).
% 2.43/1.38  tff(c_285, plain, (![B_80]: (k2_relset_1('#skF_1', B_80, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_215, c_282])).
% 2.43/1.38  tff(c_272, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_206, c_32])).
% 2.43/1.38  tff(c_286, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_272])).
% 2.43/1.38  tff(c_433, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_432, c_286])).
% 2.43/1.38  tff(c_436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_380, c_433])).
% 2.43/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.38  
% 2.43/1.38  Inference rules
% 2.43/1.38  ----------------------
% 2.43/1.38  #Ref     : 0
% 2.43/1.38  #Sup     : 93
% 2.43/1.38  #Fact    : 0
% 2.43/1.38  #Define  : 0
% 2.43/1.38  #Split   : 3
% 2.43/1.38  #Chain   : 0
% 2.43/1.38  #Close   : 0
% 2.43/1.38  
% 2.43/1.38  Ordering : KBO
% 2.43/1.38  
% 2.43/1.38  Simplification rules
% 2.43/1.38  ----------------------
% 2.43/1.38  #Subsume      : 2
% 2.43/1.38  #Demod        : 61
% 2.43/1.38  #Tautology    : 62
% 2.43/1.38  #SimpNegUnit  : 3
% 2.43/1.38  #BackRed      : 9
% 2.43/1.38  
% 2.43/1.38  #Partial instantiations: 0
% 2.43/1.38  #Strategies tried      : 1
% 2.43/1.38  
% 2.43/1.38  Timing (in seconds)
% 2.43/1.38  ----------------------
% 2.74/1.38  Preprocessing        : 0.33
% 2.74/1.38  Parsing              : 0.18
% 2.74/1.38  CNF conversion       : 0.02
% 2.74/1.38  Main loop            : 0.26
% 2.74/1.38  Inferencing          : 0.09
% 2.74/1.38  Reduction            : 0.08
% 2.74/1.38  Demodulation         : 0.06
% 2.74/1.38  BG Simplification    : 0.02
% 2.74/1.38  Subsumption          : 0.04
% 2.74/1.38  Abstraction          : 0.01
% 2.74/1.38  MUC search           : 0.00
% 2.74/1.38  Cooper               : 0.00
% 2.74/1.38  Total                : 0.63
% 2.74/1.38  Index Insertion      : 0.00
% 2.74/1.38  Index Deletion       : 0.00
% 2.74/1.38  Index Matching       : 0.00
% 2.74/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
