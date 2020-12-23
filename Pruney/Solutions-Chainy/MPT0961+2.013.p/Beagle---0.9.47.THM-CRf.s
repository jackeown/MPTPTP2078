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
% DateTime   : Thu Dec  3 10:10:43 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 450 expanded)
%              Number of leaves         :   31 ( 163 expanded)
%              Depth                    :   11
%              Number of atoms          :  139 (1125 expanded)
%              Number of equality atoms :   46 ( 315 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_100,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_xboole_0(C)
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_60,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1361,plain,(
    ! [A_186] :
      ( r1_tarski(A_186,k2_zfmisc_1(k1_relat_1(A_186),k2_relat_1(A_186)))
      | ~ v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_120,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_16,c_120])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,k2_zfmisc_1(k1_relat_1(A_14),k2_relat_1(A_14)))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_319,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_414,plain,(
    ! [A_95,B_96,A_97] :
      ( k1_relset_1(A_95,B_96,A_97) = k1_relat_1(A_97)
      | ~ r1_tarski(A_97,k2_zfmisc_1(A_95,B_96)) ) ),
    inference(resolution,[status(thm)],[c_20,c_319])).

tff(c_436,plain,(
    ! [A_14] :
      ( k1_relset_1(k1_relat_1(A_14),k2_relat_1(A_14),A_14) = k1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_28,c_414])).

tff(c_441,plain,(
    ! [B_98,C_99,A_100] :
      ( k1_xboole_0 = B_98
      | v1_funct_2(C_99,A_100,B_98)
      | k1_relset_1(A_100,B_98,C_99) != A_100
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_771,plain,(
    ! [B_136,A_137,A_138] :
      ( k1_xboole_0 = B_136
      | v1_funct_2(A_137,A_138,B_136)
      | k1_relset_1(A_138,B_136,A_137) != A_138
      | ~ r1_tarski(A_137,k2_zfmisc_1(A_138,B_136)) ) ),
    inference(resolution,[status(thm)],[c_20,c_441])).

tff(c_849,plain,(
    ! [A_143] :
      ( k2_relat_1(A_143) = k1_xboole_0
      | v1_funct_2(A_143,k1_relat_1(A_143),k2_relat_1(A_143))
      | k1_relset_1(k1_relat_1(A_143),k2_relat_1(A_143),A_143) != k1_relat_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(resolution,[status(thm)],[c_28,c_771])).

tff(c_58,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56])).

tff(c_100,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_856,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_849,c_100])).

tff(c_865,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_856])).

tff(c_868,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_865])).

tff(c_871,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_868])).

tff(c_875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_871])).

tff(c_876,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_865])).

tff(c_287,plain,(
    ! [A_67] :
      ( r1_tarski(A_67,k2_zfmisc_1(k1_relat_1(A_67),k2_relat_1(A_67)))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_302,plain,(
    ! [A_67] :
      ( k2_zfmisc_1(k1_relat_1(A_67),k2_relat_1(A_67)) = A_67
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_67),k2_relat_1(A_67)),A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_287,c_4])).

tff(c_907,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'),k1_xboole_0),'#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_876,c_302])).

tff(c_919,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_124,c_12,c_12,c_876,c_907])).

tff(c_52,plain,(
    ! [A_24,B_25] : v1_xboole_0('#skF_1'(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_79,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [A_24,B_25] : '#skF_1'(A_24,B_25) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_79])).

tff(c_50,plain,(
    ! [A_24,B_25] : v1_relat_1('#skF_1'(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_101,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_50])).

tff(c_48,plain,(
    ! [A_24,B_25] : v4_relat_1('#skF_1'(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_115,plain,(
    ! [A_24] : v4_relat_1(k1_xboole_0,A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_48])).

tff(c_230,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k1_relat_1(B_61),A_62)
      | ~ v4_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_131,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(B_46,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_136,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_124,c_131])).

tff(c_250,plain,(
    ! [B_64] :
      ( k1_relat_1(B_64) = k1_xboole_0
      | ~ v4_relat_1(B_64,k1_xboole_0)
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_230,c_136])).

tff(c_254,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_115,c_250])).

tff(c_257,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_254])).

tff(c_333,plain,(
    ! [A_74,B_75] : k1_relset_1(A_74,B_75,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_319])).

tff(c_336,plain,(
    ! [A_74,B_75] : k1_relset_1(A_74,B_75,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_333])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    ! [C_23,B_22] :
      ( v1_funct_2(C_23,k1_xboole_0,B_22)
      | k1_relset_1(k1_xboole_0,B_22,C_23) != k1_xboole_0
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_548,plain,(
    ! [C_110,B_111] :
      ( v1_funct_2(C_110,k1_xboole_0,B_111)
      | k1_relset_1(k1_xboole_0,B_111,C_110) != k1_xboole_0
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_554,plain,(
    ! [B_111] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_111)
      | k1_relset_1(k1_xboole_0,B_111,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_548])).

tff(c_558,plain,(
    ! [B_111] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_554])).

tff(c_938,plain,(
    ! [B_111] : v1_funct_2('#skF_2','#skF_2',B_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_919,c_558])).

tff(c_950,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_919,c_257])).

tff(c_900,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_100])).

tff(c_973,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_900])).

tff(c_993,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_973])).

tff(c_1206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_993])).

tff(c_1207,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1283,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_20,c_1207])).

tff(c_1369,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1361,c_1283])).

tff(c_1375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.50  
% 3.31/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.31/1.50  
% 3.31/1.50  %Foreground sorts:
% 3.31/1.50  
% 3.31/1.50  
% 3.31/1.50  %Background operators:
% 3.31/1.50  
% 3.31/1.50  
% 3.31/1.50  %Foreground operators:
% 3.31/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.31/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.31/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.31/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.31/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.31/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.50  
% 3.31/1.51  tff(f_111, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.31/1.51  tff(f_63, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.31/1.51  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.31/1.51  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.31/1.51  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.31/1.51  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.31/1.51  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.31/1.51  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.31/1.51  tff(f_100, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_xboole_0(C)) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_relset_1)).
% 3.31/1.51  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.31/1.51  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.31/1.52  tff(c_60, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.31/1.52  tff(c_1361, plain, (![A_186]: (r1_tarski(A_186, k2_zfmisc_1(k1_relat_1(A_186), k2_relat_1(A_186))) | ~v1_relat_1(A_186))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.31/1.52  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.31/1.52  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.31/1.52  tff(c_120, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.31/1.52  tff(c_124, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_16, c_120])).
% 3.31/1.52  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.31/1.52  tff(c_28, plain, (![A_14]: (r1_tarski(A_14, k2_zfmisc_1(k1_relat_1(A_14), k2_relat_1(A_14))) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.31/1.52  tff(c_319, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.31/1.52  tff(c_414, plain, (![A_95, B_96, A_97]: (k1_relset_1(A_95, B_96, A_97)=k1_relat_1(A_97) | ~r1_tarski(A_97, k2_zfmisc_1(A_95, B_96)))), inference(resolution, [status(thm)], [c_20, c_319])).
% 3.31/1.52  tff(c_436, plain, (![A_14]: (k1_relset_1(k1_relat_1(A_14), k2_relat_1(A_14), A_14)=k1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_28, c_414])).
% 3.31/1.52  tff(c_441, plain, (![B_98, C_99, A_100]: (k1_xboole_0=B_98 | v1_funct_2(C_99, A_100, B_98) | k1_relset_1(A_100, B_98, C_99)!=A_100 | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_98))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.31/1.52  tff(c_771, plain, (![B_136, A_137, A_138]: (k1_xboole_0=B_136 | v1_funct_2(A_137, A_138, B_136) | k1_relset_1(A_138, B_136, A_137)!=A_138 | ~r1_tarski(A_137, k2_zfmisc_1(A_138, B_136)))), inference(resolution, [status(thm)], [c_20, c_441])).
% 3.31/1.52  tff(c_849, plain, (![A_143]: (k2_relat_1(A_143)=k1_xboole_0 | v1_funct_2(A_143, k1_relat_1(A_143), k2_relat_1(A_143)) | k1_relset_1(k1_relat_1(A_143), k2_relat_1(A_143), A_143)!=k1_relat_1(A_143) | ~v1_relat_1(A_143))), inference(resolution, [status(thm)], [c_28, c_771])).
% 3.31/1.52  tff(c_58, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.31/1.52  tff(c_56, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.31/1.52  tff(c_62, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56])).
% 3.31/1.52  tff(c_100, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.31/1.52  tff(c_856, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_849, c_100])).
% 3.31/1.52  tff(c_865, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_856])).
% 3.31/1.52  tff(c_868, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_865])).
% 3.31/1.52  tff(c_871, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_436, c_868])).
% 3.31/1.52  tff(c_875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_871])).
% 3.31/1.52  tff(c_876, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_865])).
% 3.31/1.52  tff(c_287, plain, (![A_67]: (r1_tarski(A_67, k2_zfmisc_1(k1_relat_1(A_67), k2_relat_1(A_67))) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.31/1.52  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.31/1.52  tff(c_302, plain, (![A_67]: (k2_zfmisc_1(k1_relat_1(A_67), k2_relat_1(A_67))=A_67 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_67), k2_relat_1(A_67)), A_67) | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_287, c_4])).
% 3.31/1.52  tff(c_907, plain, (k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))='#skF_2' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'), k1_xboole_0), '#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_876, c_302])).
% 3.31/1.52  tff(c_919, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_124, c_12, c_12, c_876, c_907])).
% 3.31/1.52  tff(c_52, plain, (![A_24, B_25]: (v1_xboole_0('#skF_1'(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.31/1.52  tff(c_79, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.31/1.52  tff(c_83, plain, (![A_24, B_25]: ('#skF_1'(A_24, B_25)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_79])).
% 3.31/1.52  tff(c_50, plain, (![A_24, B_25]: (v1_relat_1('#skF_1'(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.31/1.52  tff(c_101, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_50])).
% 3.31/1.52  tff(c_48, plain, (![A_24, B_25]: (v4_relat_1('#skF_1'(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.31/1.52  tff(c_115, plain, (![A_24]: (v4_relat_1(k1_xboole_0, A_24))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_48])).
% 3.31/1.52  tff(c_230, plain, (![B_61, A_62]: (r1_tarski(k1_relat_1(B_61), A_62) | ~v4_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.31/1.52  tff(c_131, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(B_46, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.31/1.52  tff(c_136, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_124, c_131])).
% 3.31/1.52  tff(c_250, plain, (![B_64]: (k1_relat_1(B_64)=k1_xboole_0 | ~v4_relat_1(B_64, k1_xboole_0) | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_230, c_136])).
% 3.31/1.52  tff(c_254, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_115, c_250])).
% 3.31/1.52  tff(c_257, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_101, c_254])).
% 3.31/1.52  tff(c_333, plain, (![A_74, B_75]: (k1_relset_1(A_74, B_75, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_319])).
% 3.31/1.52  tff(c_336, plain, (![A_74, B_75]: (k1_relset_1(A_74, B_75, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_333])).
% 3.31/1.52  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.31/1.52  tff(c_38, plain, (![C_23, B_22]: (v1_funct_2(C_23, k1_xboole_0, B_22) | k1_relset_1(k1_xboole_0, B_22, C_23)!=k1_xboole_0 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.31/1.52  tff(c_548, plain, (![C_110, B_111]: (v1_funct_2(C_110, k1_xboole_0, B_111) | k1_relset_1(k1_xboole_0, B_111, C_110)!=k1_xboole_0 | ~m1_subset_1(C_110, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 3.31/1.52  tff(c_554, plain, (![B_111]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_111) | k1_relset_1(k1_xboole_0, B_111, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_548])).
% 3.31/1.52  tff(c_558, plain, (![B_111]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_111))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_554])).
% 3.31/1.52  tff(c_938, plain, (![B_111]: (v1_funct_2('#skF_2', '#skF_2', B_111))), inference(demodulation, [status(thm), theory('equality')], [c_919, c_919, c_558])).
% 3.31/1.52  tff(c_950, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_919, c_919, c_257])).
% 3.31/1.52  tff(c_900, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_876, c_100])).
% 3.31/1.52  tff(c_973, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_919, c_900])).
% 3.31/1.52  tff(c_993, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_950, c_973])).
% 3.31/1.52  tff(c_1206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_938, c_993])).
% 3.31/1.52  tff(c_1207, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_62])).
% 3.31/1.52  tff(c_1283, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_20, c_1207])).
% 3.31/1.52  tff(c_1369, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1361, c_1283])).
% 3.31/1.52  tff(c_1375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_1369])).
% 3.31/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.52  
% 3.31/1.52  Inference rules
% 3.31/1.52  ----------------------
% 3.31/1.52  #Ref     : 0
% 3.31/1.52  #Sup     : 260
% 3.31/1.52  #Fact    : 0
% 3.31/1.52  #Define  : 0
% 3.31/1.52  #Split   : 2
% 3.31/1.52  #Chain   : 0
% 3.31/1.52  #Close   : 0
% 3.31/1.52  
% 3.31/1.52  Ordering : KBO
% 3.31/1.52  
% 3.31/1.52  Simplification rules
% 3.31/1.52  ----------------------
% 3.31/1.52  #Subsume      : 28
% 3.31/1.52  #Demod        : 353
% 3.31/1.52  #Tautology    : 144
% 3.31/1.52  #SimpNegUnit  : 0
% 3.31/1.52  #BackRed      : 50
% 3.31/1.52  
% 3.31/1.52  #Partial instantiations: 0
% 3.31/1.52  #Strategies tried      : 1
% 3.31/1.52  
% 3.31/1.52  Timing (in seconds)
% 3.31/1.52  ----------------------
% 3.31/1.52  Preprocessing        : 0.32
% 3.31/1.52  Parsing              : 0.17
% 3.31/1.52  CNF conversion       : 0.02
% 3.31/1.52  Main loop            : 0.43
% 3.31/1.52  Inferencing          : 0.15
% 3.31/1.52  Reduction            : 0.14
% 3.31/1.52  Demodulation         : 0.11
% 3.31/1.52  BG Simplification    : 0.02
% 3.31/1.52  Subsumption          : 0.08
% 3.31/1.52  Abstraction          : 0.02
% 3.31/1.52  MUC search           : 0.00
% 3.31/1.52  Cooper               : 0.00
% 3.31/1.52  Total                : 0.79
% 3.31/1.52  Index Insertion      : 0.00
% 3.31/1.52  Index Deletion       : 0.00
% 3.31/1.52  Index Matching       : 0.00
% 3.31/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
