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
% DateTime   : Thu Dec  3 10:15:34 EST 2020

% Result     : Theorem 12.72s
% Output     : CNFRefutation 13.22s
% Verified   : 
% Statistics : Number of formulae       :  375 (6871 expanded)
%              Number of leaves         :   40 (2155 expanded)
%              Depth                    :   18
%              Number of atoms          :  566 (14580 expanded)
%              Number of equality atoms :  323 (6247 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v4_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_131,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_174,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_194,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_174])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_7073,plain,(
    ! [A_443,B_444,C_445] :
      ( k2_relset_1(A_443,B_444,C_445) = k2_relat_1(C_445)
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_443,B_444))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_7080,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_7073])).

tff(c_7086,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_7080])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_195,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_174])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_6323,plain,(
    ! [A_392,B_393,C_394] :
      ( k2_relset_1(A_392,B_393,C_394) = k2_relat_1(C_394)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6340,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_6323])).

tff(c_6345,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6340])).

tff(c_573,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_580,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_573])).

tff(c_596,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_580])).

tff(c_285,plain,(
    ! [A_75] :
      ( k1_relat_1(A_75) = k1_xboole_0
      | k2_relat_1(A_75) != k1_xboole_0
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_299,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_194,c_285])).

tff(c_303,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_600,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_303])).

tff(c_28,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_445,plain,(
    ! [A_93,B_94] :
      ( k1_relat_1(k2_zfmisc_1(A_93,B_94)) = A_93
      | k1_xboole_0 = B_94
      | k1_xboole_0 = A_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_413,plain,(
    ! [B_89,A_90] :
      ( v4_relat_1(B_89,A_90)
      | ~ r1_tarski(k1_relat_1(B_89),A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_427,plain,(
    ! [B_89] :
      ( v4_relat_1(B_89,k1_relat_1(B_89))
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_6,c_413])).

tff(c_454,plain,(
    ! [A_93,B_94] :
      ( v4_relat_1(k2_zfmisc_1(A_93,B_94),A_93)
      | ~ v1_relat_1(k2_zfmisc_1(A_93,B_94))
      | k1_xboole_0 = B_94
      | k1_xboole_0 = A_93 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_427])).

tff(c_480,plain,(
    ! [A_93,B_94] :
      ( v4_relat_1(k2_zfmisc_1(A_93,B_94),A_93)
      | k1_xboole_0 = B_94
      | k1_xboole_0 = A_93 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_454])).

tff(c_805,plain,(
    ! [C_130,A_131,B_132] :
      ( v4_relat_1(C_130,A_131)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(B_132))
      | ~ v4_relat_1(B_132,A_131)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_809,plain,(
    ! [A_131] :
      ( v4_relat_1('#skF_2',A_131)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_1','#skF_1'),A_131)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_66,c_805])).

tff(c_822,plain,(
    ! [A_133] :
      ( v4_relat_1('#skF_2',A_133)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_1','#skF_1'),A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_809])).

tff(c_826,plain,
    ( v4_relat_1('#skF_2','#skF_1')
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_480,c_822])).

tff(c_833,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_600,c_600,c_826])).

tff(c_38,plain,(
    ! [B_27,A_26] :
      ( k7_relat_1(B_27,A_26) = B_27
      | ~ v4_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_839,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_833,c_38])).

tff(c_842,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_839])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_846,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_30])).

tff(c_850,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_596,c_846])).

tff(c_583,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_573])).

tff(c_598,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_583])).

tff(c_675,plain,(
    ! [B_118,A_119] :
      ( k9_relat_1(B_118,k2_relat_1(A_119)) = k2_relat_1(k5_relat_1(A_119,B_118))
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_687,plain,(
    ! [B_118] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_118)) = k9_relat_1(B_118,'#skF_1')
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_675])).

tff(c_702,plain,(
    ! [B_118] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_118)) = k9_relat_1(B_118,'#skF_1')
      | ~ v1_relat_1(B_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_687])).

tff(c_901,plain,(
    ! [E_140,A_138,D_136,F_137,B_139,C_135] :
      ( k4_relset_1(A_138,B_139,C_135,D_136,E_140,F_137) = k5_relat_1(E_140,F_137)
      | ~ m1_subset_1(F_137,k1_zfmisc_1(k2_zfmisc_1(C_135,D_136)))
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_959,plain,(
    ! [A_141,B_142,E_143] :
      ( k4_relset_1(A_141,B_142,'#skF_1','#skF_1',E_143,'#skF_2') = k5_relat_1(E_143,'#skF_2')
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(resolution,[status(thm)],[c_66,c_901])).

tff(c_982,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_959])).

tff(c_52,plain,(
    ! [D_37,A_34,F_39,B_35,C_36,E_38] :
      ( m1_subset_1(k4_relset_1(A_34,B_35,C_36,D_37,E_38,F_39),k1_zfmisc_1(k2_zfmisc_1(A_34,D_37)))
      | ~ m1_subset_1(F_39,k1_zfmisc_1(k2_zfmisc_1(C_36,D_37)))
      | ~ m1_subset_1(E_38,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1126,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_52])).

tff(c_1130,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_1126])).

tff(c_54,plain,(
    ! [A_40,B_41,C_42] :
      ( k2_relset_1(A_40,B_41,C_42) = k2_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1658,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1130,c_54])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1122,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_58])).

tff(c_5394,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1658,c_1122])).

tff(c_5401,plain,
    ( k9_relat_1('#skF_2','#skF_1') != '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_5394])).

tff(c_5404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_850,c_5401])).

tff(c_5405,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_5406,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_5896,plain,(
    ! [A_364] :
      ( r1_tarski(A_364,k2_zfmisc_1(k1_relat_1(A_364),k2_relat_1(A_364)))
      | ~ v1_relat_1(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5920,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k1_xboole_0))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5406,c_5896])).

tff(c_5934,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_12,c_5405,c_5920])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_156,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_172,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_156])).

tff(c_218,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_229,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_172,c_218])).

tff(c_5947,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_5934,c_229])).

tff(c_298,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_195,c_285])).

tff(c_302,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_5963,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5947,c_302])).

tff(c_6346,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6345,c_5963])).

tff(c_5960,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5947,c_5406])).

tff(c_5981,plain,(
    ! [A_5] : m1_subset_1('#skF_2',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5947,c_14])).

tff(c_6330,plain,(
    ! [A_392,B_393] : k2_relset_1(A_392,B_393,'#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5981,c_6323])).

tff(c_6361,plain,(
    ! [A_395,B_396] : k2_relset_1(A_395,B_396,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5960,c_6330])).

tff(c_6365,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6361,c_62])).

tff(c_6372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6346,c_6365])).

tff(c_6373,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_6374,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_6907,plain,(
    ! [A_437] :
      ( r1_tarski(A_437,k2_zfmisc_1(k1_relat_1(A_437),k2_relat_1(A_437)))
      | ~ v1_relat_1(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6934,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),k1_xboole_0))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6374,c_6907])).

tff(c_6950,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_12,c_6373,c_6934])).

tff(c_6963,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6950,c_229])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6465,plain,(
    ! [A_407] :
      ( r1_tarski(A_407,k2_zfmisc_1(k1_relat_1(A_407),k2_relat_1(A_407)))
      | ~ v1_relat_1(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6477,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),k1_xboole_0))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6374,c_6465])).

tff(c_6485,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_10,c_6477])).

tff(c_6498,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6485,c_229])).

tff(c_6510,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6498,c_6373])).

tff(c_71,plain,(
    ! [A_54] : k2_zfmisc_1(A_54,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_28])).

tff(c_300,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75,c_285])).

tff(c_6384,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_6423,plain,(
    ! [A_402] :
      ( k2_relat_1(A_402) = k1_xboole_0
      | k1_relat_1(A_402) != k1_xboole_0
      | ~ v1_relat_1(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6432,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75,c_6423])).

tff(c_6444,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_6384,c_6432])).

tff(c_6503,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6498,c_6498,c_6444])).

tff(c_6609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6510,c_6503])).

tff(c_6611,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_6978,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6963,c_6963,c_6611])).

tff(c_7083,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_7073])).

tff(c_7088,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6978,c_60,c_7083])).

tff(c_6375,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_6980,plain,(
    k2_relat_1('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6963,c_6375])).

tff(c_7091,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7088,c_6980])).

tff(c_7197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7086,c_7091])).

tff(c_7198,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_7199,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_7830,plain,(
    ! [A_489] :
      ( r1_tarski(A_489,k2_zfmisc_1(k1_relat_1(A_489),k2_relat_1(A_489)))
      | ~ v1_relat_1(A_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_7844,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k1_xboole_0))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7199,c_7830])).

tff(c_7861,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_12,c_7198,c_7844])).

tff(c_7878,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7861,c_229])).

tff(c_7853,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6373,c_7830])).

tff(c_7867,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_12,c_6374,c_7853])).

tff(c_7920,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7878,c_7867])).

tff(c_8091,plain,(
    ! [A_498] :
      ( A_498 = '#skF_2'
      | ~ r1_tarski(A_498,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7878,c_7878,c_229])).

tff(c_8105,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7920,c_8091])).

tff(c_7889,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7878,c_6374])).

tff(c_8114,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8105,c_7889])).

tff(c_7908,plain,(
    ! [A_5] : m1_subset_1('#skF_2',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7878,c_14])).

tff(c_8110,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8105,c_7908])).

tff(c_8454,plain,(
    ! [A_527,B_528,C_529] :
      ( k2_relset_1(A_527,B_528,C_529) = k2_relat_1(C_529)
      | ~ m1_subset_1(C_529,k1_zfmisc_1(k2_zfmisc_1(A_527,B_528))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8464,plain,(
    ! [A_527,B_528] : k2_relset_1(A_527,B_528,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8110,c_8454])).

tff(c_8472,plain,(
    ! [A_530,B_531] : k2_relset_1(A_530,B_531,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8114,c_8464])).

tff(c_8476,plain,(
    '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8472,c_60])).

tff(c_7907,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7878,c_7878,c_10])).

tff(c_8112,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8105,c_8105,c_7907])).

tff(c_8493,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8476,c_8476,c_8112])).

tff(c_171,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_156])).

tff(c_227,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_171,c_218])).

tff(c_7208,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_8504,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8476,c_7208])).

tff(c_8719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8493,c_8504])).

tff(c_8720,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_170,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_156])).

tff(c_228,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_170,c_218])).

tff(c_246,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_8730,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8720,c_246])).

tff(c_8862,plain,(
    ! [A_557] :
      ( r1_tarski(A_557,k2_zfmisc_1(k1_relat_1(A_557),k2_relat_1(A_557)))
      | ~ v1_relat_1(A_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8870,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k1_xboole_0))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7199,c_8862])).

tff(c_8883,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_10,c_8870])).

tff(c_8900,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8883,c_229])).

tff(c_8879,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6373,c_8862])).

tff(c_8889,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_12,c_6374,c_8879])).

tff(c_8939,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8900,c_8889])).

tff(c_8940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8730,c_8939])).

tff(c_8941,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_9158,plain,(
    ! [A_576,B_577] :
      ( k1_relat_1(k2_zfmisc_1(A_576,B_577)) = A_576
      | k1_xboole_0 = B_577
      | k1_xboole_0 = A_576 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_9176,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8941,c_9158])).

tff(c_9194,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9176])).

tff(c_9020,plain,(
    ! [B_561,A_562] :
      ( k1_xboole_0 = B_561
      | k1_xboole_0 = A_562
      | k2_zfmisc_1(A_562,B_561) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9023,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_8941,c_9020])).

tff(c_9114,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_9023])).

tff(c_9196,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9194,c_9114])).

tff(c_9219,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9194,c_9194,c_12])).

tff(c_9259,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9219,c_8941])).

tff(c_9261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9196,c_9259])).

tff(c_9263,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9176])).

tff(c_9334,plain,(
    ! [A_585,B_586] :
      ( k2_relat_1(k2_zfmisc_1(A_585,B_586)) = B_586
      | k1_xboole_0 = B_586
      | k1_xboole_0 = A_585 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_9343,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8941,c_9334])).

tff(c_9352,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_9263,c_9263,c_9343])).

tff(c_9262,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9176])).

tff(c_9264,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_9263,c_9262])).

tff(c_9134,plain,(
    ! [B_570,A_571] :
      ( v4_relat_1(B_570,A_571)
      | ~ r1_tarski(k1_relat_1(B_570),A_571)
      | ~ v1_relat_1(B_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9141,plain,(
    ! [B_574] :
      ( v4_relat_1(B_574,k1_relat_1(B_574))
      | ~ v1_relat_1(B_574) ) ),
    inference(resolution,[status(thm)],[c_6,c_9134])).

tff(c_9145,plain,(
    ! [B_574] :
      ( k7_relat_1(B_574,k1_relat_1(B_574)) = B_574
      | ~ v1_relat_1(B_574) ) ),
    inference(resolution,[status(thm)],[c_9141,c_38])).

tff(c_9269,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9264,c_9145])).

tff(c_9279,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_9269])).

tff(c_9306,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9279,c_30])).

tff(c_9310,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_9306])).

tff(c_9356,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9352,c_9310])).

tff(c_8963,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8941,c_64])).

tff(c_9820,plain,(
    ! [A_623,B_624,C_625] :
      ( k2_relset_1(A_623,B_624,C_625) = k2_relat_1(C_625)
      | ~ m1_subset_1(C_625,k1_zfmisc_1(k2_zfmisc_1(A_623,B_624))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_9875,plain,(
    ! [C_632] :
      ( k2_relset_1('#skF_1','#skF_1',C_632) = k2_relat_1(C_632)
      | ~ m1_subset_1(C_632,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8941,c_9820])).

tff(c_9878,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8963,c_9875])).

tff(c_9891,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_9878])).

tff(c_32,plain,(
    ! [B_23,A_21] :
      ( k9_relat_1(B_23,k2_relat_1(A_21)) = k2_relat_1(k5_relat_1(A_21,B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9901,plain,(
    ! [B_23] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_23)) = k9_relat_1(B_23,'#skF_1')
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9891,c_32])).

tff(c_9908,plain,(
    ! [B_23] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_23)) = k9_relat_1(B_23,'#skF_1')
      | ~ v1_relat_1(B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_9901])).

tff(c_8962,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8941,c_66])).

tff(c_10100,plain,(
    ! [B_649,F_647,A_648,C_645,E_650,D_646] :
      ( k4_relset_1(A_648,B_649,C_645,D_646,E_650,F_647) = k5_relat_1(E_650,F_647)
      | ~ m1_subset_1(F_647,k1_zfmisc_1(k2_zfmisc_1(C_645,D_646)))
      | ~ m1_subset_1(E_650,k1_zfmisc_1(k2_zfmisc_1(A_648,B_649))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10147,plain,(
    ! [A_652,B_653,E_654,F_655] :
      ( k4_relset_1(A_652,B_653,'#skF_1','#skF_1',E_654,F_655) = k5_relat_1(E_654,F_655)
      | ~ m1_subset_1(F_655,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(E_654,k1_zfmisc_1(k2_zfmisc_1(A_652,B_653))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8941,c_10100])).

tff(c_10597,plain,(
    ! [A_677,B_678,E_679] :
      ( k4_relset_1(A_677,B_678,'#skF_1','#skF_1',E_679,'#skF_2') = k5_relat_1(E_679,'#skF_2')
      | ~ m1_subset_1(E_679,k1_zfmisc_1(k2_zfmisc_1(A_677,B_678))) ) ),
    inference(resolution,[status(thm)],[c_8962,c_10147])).

tff(c_10770,plain,(
    ! [E_690] :
      ( k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1',E_690,'#skF_2') = k5_relat_1(E_690,'#skF_2')
      | ~ m1_subset_1(E_690,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8941,c_10597])).

tff(c_10785,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_8963,c_10770])).

tff(c_11081,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10785,c_52])).

tff(c_11085,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8963,c_8941,c_8962,c_8941,c_8941,c_11081])).

tff(c_9823,plain,(
    ! [C_625] :
      ( k2_relset_1('#skF_1','#skF_1',C_625) = k2_relat_1(C_625)
      | ~ m1_subset_1(C_625,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8941,c_9820])).

tff(c_11110,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_11085,c_9823])).

tff(c_11077,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10785,c_58])).

tff(c_14022,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11110,c_11077])).

tff(c_14085,plain,
    ( k9_relat_1('#skF_2','#skF_1') != '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9908,c_14022])).

tff(c_14088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_9356,c_14085])).

tff(c_14090,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9023])).

tff(c_14107,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14090,c_172])).

tff(c_8960,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8941,c_171])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8982,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_8960,c_2])).

tff(c_9007,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_8982])).

tff(c_14124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14107,c_9007])).

tff(c_14125,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8982])).

tff(c_14131,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14125,c_8941])).

tff(c_14386,plain,(
    ! [A_840,B_841] :
      ( k2_relat_1(k2_zfmisc_1(A_840,B_841)) = B_841
      | k1_xboole_0 = B_841
      | k1_xboole_0 = A_840 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14398,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14131,c_14386])).

tff(c_14412,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14398])).

tff(c_14211,plain,(
    ! [B_821,A_822] :
      ( k1_xboole_0 = B_821
      | k1_xboole_0 = A_822
      | k2_zfmisc_1(A_822,B_821) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14214,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_14131,c_14211])).

tff(c_14259,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14214])).

tff(c_14422,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14412,c_14259])).

tff(c_14441,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14412,c_14412,c_12])).

tff(c_14512,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14441,c_14131])).

tff(c_14514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14422,c_14512])).

tff(c_14516,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14398])).

tff(c_14515,plain,
    ( k1_xboole_0 = '#skF_1'
    | k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14398])).

tff(c_14517,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_14516,c_14515])).

tff(c_14548,plain,(
    ! [A_848,B_849] :
      ( k1_relat_1(k2_zfmisc_1(A_848,B_849)) = A_848
      | k1_xboole_0 = B_849
      | k1_xboole_0 = A_848 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14581,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14131,c_14548])).

tff(c_14606,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_14516,c_14516,c_14581])).

tff(c_14356,plain,(
    ! [B_836,A_837] :
      ( v4_relat_1(B_836,A_837)
      | ~ r1_tarski(k1_relat_1(B_836),A_837)
      | ~ v1_relat_1(B_836) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14365,plain,(
    ! [B_836] :
      ( v4_relat_1(B_836,k1_relat_1(B_836))
      | ~ v1_relat_1(B_836) ) ),
    inference(resolution,[status(thm)],[c_6,c_14356])).

tff(c_14622,plain,
    ( v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14606,c_14365])).

tff(c_14645,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_14622])).

tff(c_14658,plain,(
    ! [B_850,A_851] :
      ( k7_relat_1(B_850,A_851) = B_850
      | ~ v4_relat_1(B_850,A_851)
      | ~ v1_relat_1(B_850) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_14661,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14645,c_14658])).

tff(c_14667,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_14661])).

tff(c_14672,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14667,c_30])).

tff(c_14676,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_14517,c_14672])).

tff(c_14941,plain,(
    ! [B_876,A_877] :
      ( k9_relat_1(B_876,k2_relat_1(A_877)) = k2_relat_1(k5_relat_1(A_877,B_876))
      | ~ v1_relat_1(B_876)
      | ~ v1_relat_1(A_877) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14953,plain,(
    ! [B_876] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_876)) = k9_relat_1(B_876,'#skF_1')
      | ~ v1_relat_1(B_876)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14517,c_14941])).

tff(c_14963,plain,(
    ! [B_876] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_876)) = k9_relat_1(B_876,'#skF_1')
      | ~ v1_relat_1(B_876) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_14953])).

tff(c_14128,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14125,c_8963])).

tff(c_15369,plain,(
    ! [E_912,A_910,D_908,B_911,C_907,F_909] :
      ( k4_relset_1(A_910,B_911,C_907,D_908,E_912,F_909) = k5_relat_1(E_912,F_909)
      | ~ m1_subset_1(F_909,k1_zfmisc_1(k2_zfmisc_1(C_907,D_908)))
      | ~ m1_subset_1(E_912,k1_zfmisc_1(k2_zfmisc_1(A_910,B_911))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_15417,plain,(
    ! [A_913,B_914,E_915,F_916] :
      ( k4_relset_1(A_913,B_914,'#skF_1','#skF_1',E_915,F_916) = k5_relat_1(E_915,F_916)
      | ~ m1_subset_1(F_916,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(E_915,k1_zfmisc_1(k2_zfmisc_1(A_913,B_914))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14131,c_15369])).

tff(c_15530,plain,(
    ! [A_923,B_924,E_925] :
      ( k4_relset_1(A_923,B_924,'#skF_1','#skF_1',E_925,'#skF_3') = k5_relat_1(E_925,'#skF_3')
      | ~ m1_subset_1(E_925,k1_zfmisc_1(k2_zfmisc_1(A_923,B_924))) ) ),
    inference(resolution,[status(thm)],[c_14128,c_15417])).

tff(c_16204,plain,(
    ! [E_963] :
      ( k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1',E_963,'#skF_3') = k5_relat_1(E_963,'#skF_3')
      | ~ m1_subset_1(E_963,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14131,c_15530])).

tff(c_16216,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_3') = k5_relat_1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_14128,c_16204])).

tff(c_16533,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16216,c_52])).

tff(c_16537,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14128,c_14131,c_14128,c_14131,c_14131,c_16533])).

tff(c_15199,plain,(
    ! [A_887,B_888,C_889] :
      ( k2_relset_1(A_887,B_888,C_889) = k2_relat_1(C_889)
      | ~ m1_subset_1(C_889,k1_zfmisc_1(k2_zfmisc_1(A_887,B_888))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_15202,plain,(
    ! [C_889] :
      ( k2_relset_1('#skF_1','#skF_1',C_889) = k2_relat_1(C_889)
      | ~ m1_subset_1(C_889,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14131,c_15199])).

tff(c_16559,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_3')) = k2_relat_1(k5_relat_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16537,c_15202])).

tff(c_14135,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14125,c_58])).

tff(c_16529,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16216,c_14135])).

tff(c_17241,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16559,c_16529])).

tff(c_17248,plain,
    ( k9_relat_1('#skF_3','#skF_1') != '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14963,c_17241])).

tff(c_17251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_14676,c_17248])).

tff(c_17253,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14214])).

tff(c_17252,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14214])).

tff(c_17306,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17253,c_17253,c_17252])).

tff(c_17307,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_17306])).

tff(c_8943,plain,(
    ! [A_558] :
      ( k1_relat_1(A_558) = k1_xboole_0
      | k2_relat_1(A_558) != k1_xboole_0
      | ~ v1_relat_1(A_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8957,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_194,c_8943])).

tff(c_14127,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8957])).

tff(c_14146,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14125,c_14127])).

tff(c_17261,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17253,c_14146])).

tff(c_17309,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17307,c_17307,c_17261])).

tff(c_17275,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17253,c_14])).

tff(c_17355,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17307,c_17275])).

tff(c_17734,plain,(
    ! [A_1047,B_1048,C_1049] :
      ( k2_relset_1(A_1047,B_1048,C_1049) = k2_relat_1(C_1049)
      | ~ m1_subset_1(C_1049,k1_zfmisc_1(k2_zfmisc_1(A_1047,B_1048))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_17752,plain,(
    ! [A_1052,B_1053] : k2_relset_1(A_1052,B_1053,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_17355,c_17734])).

tff(c_17320,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17307,c_60])).

tff(c_17756,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_17752,c_17320])).

tff(c_17763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17309,c_17756])).

tff(c_17764,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17306])).

tff(c_17765,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17306])).

tff(c_17796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17764,c_17765])).

tff(c_17798,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8957])).

tff(c_17835,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14125,c_17798])).

tff(c_17802,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14125,c_8941])).

tff(c_18456,plain,(
    ! [A_1097,B_1098] :
      ( k2_relat_1(k2_zfmisc_1(A_1097,B_1098)) = B_1098
      | k1_xboole_0 = B_1098
      | k1_xboole_0 = A_1097 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18465,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_17802,c_18456])).

tff(c_18474,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17835,c_18465])).

tff(c_18479,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_18474])).

tff(c_17887,plain,(
    ! [B_1057,A_1058] :
      ( k1_xboole_0 = B_1057
      | k1_xboole_0 = A_1058
      | k2_zfmisc_1(A_1058,B_1057) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_17890,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_17802,c_17887])).

tff(c_18326,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_17890])).

tff(c_18484,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18479,c_18326])).

tff(c_18503,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18479,c_18479,c_12])).

tff(c_18667,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18503,c_17802])).

tff(c_18669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18484,c_18667])).

tff(c_18671,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18474])).

tff(c_18670,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18474])).

tff(c_18672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18671,c_18671,c_18670])).

tff(c_18674,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17890])).

tff(c_18673,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17890])).

tff(c_18757,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18674,c_18674,c_18673])).

tff(c_18758,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_18757])).

tff(c_17797,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8957])).

tff(c_17830,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14125,c_17797])).

tff(c_18013,plain,(
    ! [A_1073,B_1074] :
      ( k1_relat_1(k2_zfmisc_1(A_1073,B_1074)) = A_1073
      | k1_xboole_0 = B_1074
      | k1_xboole_0 = A_1073 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18028,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_17802,c_18013])).

tff(c_18041,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17830,c_18028])).

tff(c_18052,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_18041])).

tff(c_17956,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_17890])).

tff(c_18055,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18052,c_17956])).

tff(c_18074,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18052,c_18052,c_12])).

tff(c_18172,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18074,c_17802])).

tff(c_18174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18055,c_18172])).

tff(c_18176,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18041])).

tff(c_18175,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18041])).

tff(c_18177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18176,c_18176,c_18175])).

tff(c_18179,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17890])).

tff(c_18185,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18179,c_17835])).

tff(c_8958,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75,c_8943])).

tff(c_17901,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8958])).

tff(c_18181,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18179,c_18179,c_17901])).

tff(c_18247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18185,c_18181])).

tff(c_18249,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8958])).

tff(c_18675,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18674,c_18674,c_18249])).

tff(c_18763,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18758,c_18758,c_18675])).

tff(c_18696,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18674,c_14])).

tff(c_18856,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18758,c_18696])).

tff(c_19475,plain,(
    ! [A_1165,B_1166,C_1167] :
      ( k2_relset_1(A_1165,B_1166,C_1167) = k2_relat_1(C_1167)
      | ~ m1_subset_1(C_1167,k1_zfmisc_1(k2_zfmisc_1(A_1165,B_1166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_19482,plain,(
    ! [A_1165,B_1166] : k2_relset_1(A_1165,B_1166,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18856,c_19475])).

tff(c_19491,plain,(
    ! [A_1165,B_1166] : k2_relset_1(A_1165,B_1166,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18763,c_19482])).

tff(c_44,plain,(
    ! [A_29] :
      ( k5_relat_1(k1_xboole_0,A_29) = k1_xboole_0
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_212,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_195,c_44])).

tff(c_18685,plain,(
    k5_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18674,c_18674,c_212])).

tff(c_18837,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18758,c_18758,c_18758,c_18685])).

tff(c_18687,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18674,c_172])).

tff(c_18761,plain,(
    ! [A_5] : r1_tarski('#skF_1',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18758,c_18687])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_19819,plain,(
    ! [C_1200,A_1203,F_1202,E_1205,B_1204,D_1201] :
      ( k4_relset_1(A_1203,B_1204,C_1200,D_1201,E_1205,F_1202) = k5_relat_1(E_1205,F_1202)
      | ~ m1_subset_1(F_1202,k1_zfmisc_1(k2_zfmisc_1(C_1200,D_1201)))
      | ~ m1_subset_1(E_1205,k1_zfmisc_1(k2_zfmisc_1(A_1203,B_1204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_22102,plain,(
    ! [A_1336,E_1337,B_1335,C_1333,A_1338,D_1334] :
      ( k4_relset_1(A_1338,B_1335,C_1333,D_1334,E_1337,A_1336) = k5_relat_1(E_1337,A_1336)
      | ~ m1_subset_1(E_1337,k1_zfmisc_1(k2_zfmisc_1(A_1338,B_1335)))
      | ~ r1_tarski(A_1336,k2_zfmisc_1(C_1333,D_1334)) ) ),
    inference(resolution,[status(thm)],[c_18,c_19819])).

tff(c_31093,plain,(
    ! [B_1701,D_1699,A_1702,A_1700,C_1703] :
      ( k4_relset_1(A_1700,B_1701,C_1703,D_1699,'#skF_1',A_1702) = k5_relat_1('#skF_1',A_1702)
      | ~ r1_tarski(A_1702,k2_zfmisc_1(C_1703,D_1699)) ) ),
    inference(resolution,[status(thm)],[c_18856,c_22102])).

tff(c_31110,plain,(
    ! [A_1700,B_1701,C_1703,D_1699] : k4_relset_1(A_1700,B_1701,C_1703,D_1699,'#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_18761,c_31093])).

tff(c_31127,plain,(
    ! [A_1700,B_1701,C_1703,D_1699] : k4_relset_1(A_1700,B_1701,C_1703,D_1699,'#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18837,c_31110])).

tff(c_17806,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14125,c_58])).

tff(c_18769,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18758,c_18758,c_17806])).

tff(c_31152,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31127,c_18769])).

tff(c_31159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19491,c_31152])).

tff(c_31160,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18757])).

tff(c_31161,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18757])).

tff(c_31181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31160,c_31161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.72/5.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.79/5.22  
% 12.79/5.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.79/5.23  %$ v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.79/5.23  
% 12.79/5.23  %Foreground sorts:
% 12.79/5.23  
% 12.79/5.23  
% 12.79/5.23  %Background operators:
% 12.79/5.23  
% 12.79/5.23  
% 12.79/5.23  %Foreground operators:
% 12.79/5.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.79/5.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.79/5.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.79/5.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.79/5.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.79/5.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.79/5.23  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.79/5.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.79/5.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.79/5.23  tff('#skF_2', type, '#skF_2': $i).
% 12.79/5.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.79/5.23  tff('#skF_3', type, '#skF_3': $i).
% 12.79/5.23  tff('#skF_1', type, '#skF_1': $i).
% 12.79/5.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.79/5.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.79/5.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.79/5.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.79/5.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.79/5.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.79/5.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.79/5.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.79/5.23  
% 13.22/5.27  tff(f_143, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_2)).
% 13.22/5.27  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.22/5.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.22/5.27  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.22/5.27  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.22/5.27  tff(f_111, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 13.22/5.27  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.22/5.27  tff(f_89, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 13.22/5.27  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 13.22/5.27  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v4_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_relat_1)).
% 13.22/5.27  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 13.22/5.27  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 13.22/5.27  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 13.22/5.27  tff(f_131, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 13.22/5.27  tff(f_121, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 13.22/5.27  tff(f_99, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 13.22/5.27  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 13.22/5.27  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.22/5.27  tff(f_105, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 13.22/5.27  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.22/5.27  tff(c_174, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 13.22/5.27  tff(c_194, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_174])).
% 13.22/5.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.22/5.27  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.22/5.27  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.22/5.27  tff(c_7073, plain, (![A_443, B_444, C_445]: (k2_relset_1(A_443, B_444, C_445)=k2_relat_1(C_445) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_443, B_444))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.22/5.27  tff(c_7080, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_7073])).
% 13.22/5.27  tff(c_7086, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_7080])).
% 13.22/5.27  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.22/5.27  tff(c_195, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_174])).
% 13.22/5.27  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.22/5.27  tff(c_6323, plain, (![A_392, B_393, C_394]: (k2_relset_1(A_392, B_393, C_394)=k2_relat_1(C_394) | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.22/5.27  tff(c_6340, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_6323])).
% 13.22/5.27  tff(c_6345, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6340])).
% 13.22/5.27  tff(c_573, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.22/5.27  tff(c_580, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_573])).
% 13.22/5.27  tff(c_596, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_580])).
% 13.22/5.27  tff(c_285, plain, (![A_75]: (k1_relat_1(A_75)=k1_xboole_0 | k2_relat_1(A_75)!=k1_xboole_0 | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.22/5.27  tff(c_299, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | k2_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_194, c_285])).
% 13.22/5.27  tff(c_303, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_299])).
% 13.22/5.27  tff(c_600, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_596, c_303])).
% 13.22/5.27  tff(c_28, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.22/5.27  tff(c_445, plain, (![A_93, B_94]: (k1_relat_1(k2_zfmisc_1(A_93, B_94))=A_93 | k1_xboole_0=B_94 | k1_xboole_0=A_93)), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.22/5.27  tff(c_413, plain, (![B_89, A_90]: (v4_relat_1(B_89, A_90) | ~r1_tarski(k1_relat_1(B_89), A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.22/5.27  tff(c_427, plain, (![B_89]: (v4_relat_1(B_89, k1_relat_1(B_89)) | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_6, c_413])).
% 13.22/5.27  tff(c_454, plain, (![A_93, B_94]: (v4_relat_1(k2_zfmisc_1(A_93, B_94), A_93) | ~v1_relat_1(k2_zfmisc_1(A_93, B_94)) | k1_xboole_0=B_94 | k1_xboole_0=A_93)), inference(superposition, [status(thm), theory('equality')], [c_445, c_427])).
% 13.22/5.27  tff(c_480, plain, (![A_93, B_94]: (v4_relat_1(k2_zfmisc_1(A_93, B_94), A_93) | k1_xboole_0=B_94 | k1_xboole_0=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_454])).
% 13.22/5.27  tff(c_805, plain, (![C_130, A_131, B_132]: (v4_relat_1(C_130, A_131) | ~m1_subset_1(C_130, k1_zfmisc_1(B_132)) | ~v4_relat_1(B_132, A_131) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.22/5.27  tff(c_809, plain, (![A_131]: (v4_relat_1('#skF_2', A_131) | ~v4_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'), A_131) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_805])).
% 13.22/5.27  tff(c_822, plain, (![A_133]: (v4_relat_1('#skF_2', A_133) | ~v4_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'), A_133))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_809])).
% 13.22/5.27  tff(c_826, plain, (v4_relat_1('#skF_2', '#skF_1') | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_480, c_822])).
% 13.22/5.27  tff(c_833, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_600, c_600, c_826])).
% 13.22/5.27  tff(c_38, plain, (![B_27, A_26]: (k7_relat_1(B_27, A_26)=B_27 | ~v4_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.22/5.27  tff(c_839, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_833, c_38])).
% 13.22/5.27  tff(c_842, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_839])).
% 13.22/5.27  tff(c_30, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.22/5.27  tff(c_846, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_842, c_30])).
% 13.22/5.27  tff(c_850, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_596, c_846])).
% 13.22/5.27  tff(c_583, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_573])).
% 13.22/5.27  tff(c_598, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_583])).
% 13.22/5.27  tff(c_675, plain, (![B_118, A_119]: (k9_relat_1(B_118, k2_relat_1(A_119))=k2_relat_1(k5_relat_1(A_119, B_118)) | ~v1_relat_1(B_118) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.22/5.27  tff(c_687, plain, (![B_118]: (k2_relat_1(k5_relat_1('#skF_3', B_118))=k9_relat_1(B_118, '#skF_1') | ~v1_relat_1(B_118) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_598, c_675])).
% 13.22/5.27  tff(c_702, plain, (![B_118]: (k2_relat_1(k5_relat_1('#skF_3', B_118))=k9_relat_1(B_118, '#skF_1') | ~v1_relat_1(B_118))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_687])).
% 13.22/5.27  tff(c_901, plain, (![E_140, A_138, D_136, F_137, B_139, C_135]: (k4_relset_1(A_138, B_139, C_135, D_136, E_140, F_137)=k5_relat_1(E_140, F_137) | ~m1_subset_1(F_137, k1_zfmisc_1(k2_zfmisc_1(C_135, D_136))) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 13.22/5.27  tff(c_959, plain, (![A_141, B_142, E_143]: (k4_relset_1(A_141, B_142, '#skF_1', '#skF_1', E_143, '#skF_2')=k5_relat_1(E_143, '#skF_2') | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(resolution, [status(thm)], [c_66, c_901])).
% 13.22/5.27  tff(c_982, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_959])).
% 13.22/5.27  tff(c_52, plain, (![D_37, A_34, F_39, B_35, C_36, E_38]: (m1_subset_1(k4_relset_1(A_34, B_35, C_36, D_37, E_38, F_39), k1_zfmisc_1(k2_zfmisc_1(A_34, D_37))) | ~m1_subset_1(F_39, k1_zfmisc_1(k2_zfmisc_1(C_36, D_37))) | ~m1_subset_1(E_38, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 13.22/5.27  tff(c_1126, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_982, c_52])).
% 13.22/5.27  tff(c_1130, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_1126])).
% 13.22/5.27  tff(c_54, plain, (![A_40, B_41, C_42]: (k2_relset_1(A_40, B_41, C_42)=k2_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.22/5.27  tff(c_1658, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_1130, c_54])).
% 13.22/5.27  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.22/5.27  tff(c_1122, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_982, c_58])).
% 13.22/5.27  tff(c_5394, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1658, c_1122])).
% 13.22/5.27  tff(c_5401, plain, (k9_relat_1('#skF_2', '#skF_1')!='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_702, c_5394])).
% 13.22/5.27  tff(c_5404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_850, c_5401])).
% 13.22/5.27  tff(c_5405, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_299])).
% 13.22/5.27  tff(c_5406, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_299])).
% 13.22/5.27  tff(c_5896, plain, (![A_364]: (r1_tarski(A_364, k2_zfmisc_1(k1_relat_1(A_364), k2_relat_1(A_364))) | ~v1_relat_1(A_364))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.22/5.27  tff(c_5920, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k1_xboole_0)) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5406, c_5896])).
% 13.22/5.27  tff(c_5934, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_12, c_5405, c_5920])).
% 13.22/5.27  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.22/5.27  tff(c_156, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.22/5.27  tff(c_172, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_156])).
% 13.22/5.27  tff(c_218, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.22/5.27  tff(c_229, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_172, c_218])).
% 13.22/5.27  tff(c_5947, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_5934, c_229])).
% 13.22/5.27  tff(c_298, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_195, c_285])).
% 13.22/5.27  tff(c_302, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_298])).
% 13.22/5.27  tff(c_5963, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5947, c_302])).
% 13.22/5.27  tff(c_6346, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6345, c_5963])).
% 13.22/5.27  tff(c_5960, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5947, c_5406])).
% 13.22/5.27  tff(c_5981, plain, (![A_5]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_5947, c_14])).
% 13.22/5.27  tff(c_6330, plain, (![A_392, B_393]: (k2_relset_1(A_392, B_393, '#skF_2')=k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_5981, c_6323])).
% 13.22/5.27  tff(c_6361, plain, (![A_395, B_396]: (k2_relset_1(A_395, B_396, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5960, c_6330])).
% 13.22/5.27  tff(c_6365, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6361, c_62])).
% 13.22/5.27  tff(c_6372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6346, c_6365])).
% 13.22/5.27  tff(c_6373, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_298])).
% 13.22/5.27  tff(c_6374, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_298])).
% 13.22/5.27  tff(c_6907, plain, (![A_437]: (r1_tarski(A_437, k2_zfmisc_1(k1_relat_1(A_437), k2_relat_1(A_437))) | ~v1_relat_1(A_437))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.22/5.27  tff(c_6934, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), k1_xboole_0)) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6374, c_6907])).
% 13.22/5.27  tff(c_6950, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_12, c_6373, c_6934])).
% 13.22/5.27  tff(c_6963, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6950, c_229])).
% 13.22/5.27  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.22/5.27  tff(c_6465, plain, (![A_407]: (r1_tarski(A_407, k2_zfmisc_1(k1_relat_1(A_407), k2_relat_1(A_407))) | ~v1_relat_1(A_407))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.22/5.27  tff(c_6477, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), k1_xboole_0)) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6374, c_6465])).
% 13.22/5.27  tff(c_6485, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_10, c_6477])).
% 13.22/5.27  tff(c_6498, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6485, c_229])).
% 13.22/5.27  tff(c_6510, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6498, c_6373])).
% 13.22/5.27  tff(c_71, plain, (![A_54]: (k2_zfmisc_1(A_54, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.22/5.27  tff(c_75, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_71, c_28])).
% 13.22/5.27  tff(c_300, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_75, c_285])).
% 13.22/5.27  tff(c_6384, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_300])).
% 13.22/5.27  tff(c_6423, plain, (![A_402]: (k2_relat_1(A_402)=k1_xboole_0 | k1_relat_1(A_402)!=k1_xboole_0 | ~v1_relat_1(A_402))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.22/5.27  tff(c_6432, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_75, c_6423])).
% 13.22/5.27  tff(c_6444, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_6384, c_6432])).
% 13.22/5.27  tff(c_6503, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6498, c_6498, c_6444])).
% 13.22/5.27  tff(c_6609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6510, c_6503])).
% 13.22/5.27  tff(c_6611, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_300])).
% 13.22/5.27  tff(c_6978, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6963, c_6963, c_6611])).
% 13.22/5.27  tff(c_7083, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_7073])).
% 13.22/5.27  tff(c_7088, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6978, c_60, c_7083])).
% 13.22/5.27  tff(c_6375, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_299])).
% 13.22/5.27  tff(c_6980, plain, (k2_relat_1('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6963, c_6375])).
% 13.22/5.27  tff(c_7091, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7088, c_6980])).
% 13.22/5.27  tff(c_7197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7086, c_7091])).
% 13.22/5.27  tff(c_7198, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_299])).
% 13.22/5.27  tff(c_7199, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_299])).
% 13.22/5.27  tff(c_7830, plain, (![A_489]: (r1_tarski(A_489, k2_zfmisc_1(k1_relat_1(A_489), k2_relat_1(A_489))) | ~v1_relat_1(A_489))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.22/5.27  tff(c_7844, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k1_xboole_0)) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7199, c_7830])).
% 13.22/5.27  tff(c_7861, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_12, c_7198, c_7844])).
% 13.22/5.27  tff(c_7878, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_7861, c_229])).
% 13.22/5.27  tff(c_7853, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6373, c_7830])).
% 13.22/5.27  tff(c_7867, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_12, c_6374, c_7853])).
% 13.22/5.27  tff(c_7920, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7878, c_7867])).
% 13.22/5.27  tff(c_8091, plain, (![A_498]: (A_498='#skF_2' | ~r1_tarski(A_498, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7878, c_7878, c_229])).
% 13.22/5.27  tff(c_8105, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_7920, c_8091])).
% 13.22/5.27  tff(c_7889, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7878, c_6374])).
% 13.22/5.27  tff(c_8114, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8105, c_7889])).
% 13.22/5.27  tff(c_7908, plain, (![A_5]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_7878, c_14])).
% 13.22/5.27  tff(c_8110, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_8105, c_7908])).
% 13.22/5.27  tff(c_8454, plain, (![A_527, B_528, C_529]: (k2_relset_1(A_527, B_528, C_529)=k2_relat_1(C_529) | ~m1_subset_1(C_529, k1_zfmisc_1(k2_zfmisc_1(A_527, B_528))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.22/5.27  tff(c_8464, plain, (![A_527, B_528]: (k2_relset_1(A_527, B_528, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8110, c_8454])).
% 13.22/5.27  tff(c_8472, plain, (![A_530, B_531]: (k2_relset_1(A_530, B_531, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8114, c_8464])).
% 13.22/5.27  tff(c_8476, plain, ('#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8472, c_60])).
% 13.22/5.27  tff(c_7907, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7878, c_7878, c_10])).
% 13.22/5.27  tff(c_8112, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8105, c_8105, c_7907])).
% 13.22/5.27  tff(c_8493, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8476, c_8476, c_8112])).
% 13.22/5.27  tff(c_171, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_156])).
% 13.22/5.27  tff(c_227, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_171, c_218])).
% 13.22/5.27  tff(c_7208, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_227])).
% 13.22/5.27  tff(c_8504, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8476, c_7208])).
% 13.22/5.27  tff(c_8719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8493, c_8504])).
% 13.22/5.27  tff(c_8720, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_227])).
% 13.22/5.27  tff(c_170, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_156])).
% 13.22/5.27  tff(c_228, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_170, c_218])).
% 13.22/5.27  tff(c_246, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_228])).
% 13.22/5.27  tff(c_8730, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8720, c_246])).
% 13.22/5.27  tff(c_8862, plain, (![A_557]: (r1_tarski(A_557, k2_zfmisc_1(k1_relat_1(A_557), k2_relat_1(A_557))) | ~v1_relat_1(A_557))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.22/5.27  tff(c_8870, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k1_xboole_0)) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7199, c_8862])).
% 13.22/5.27  tff(c_8883, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_10, c_8870])).
% 13.22/5.27  tff(c_8900, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8883, c_229])).
% 13.22/5.27  tff(c_8879, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6373, c_8862])).
% 13.22/5.27  tff(c_8889, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_12, c_6374, c_8879])).
% 13.22/5.27  tff(c_8939, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8900, c_8889])).
% 13.22/5.27  tff(c_8940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8730, c_8939])).
% 13.22/5.27  tff(c_8941, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_228])).
% 13.22/5.27  tff(c_9158, plain, (![A_576, B_577]: (k1_relat_1(k2_zfmisc_1(A_576, B_577))=A_576 | k1_xboole_0=B_577 | k1_xboole_0=A_576)), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.22/5.27  tff(c_9176, plain, (k1_relat_1('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8941, c_9158])).
% 13.22/5.27  tff(c_9194, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_9176])).
% 13.22/5.27  tff(c_9020, plain, (![B_561, A_562]: (k1_xboole_0=B_561 | k1_xboole_0=A_562 | k2_zfmisc_1(A_562, B_561)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.22/5.27  tff(c_9023, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_8941, c_9020])).
% 13.22/5.27  tff(c_9114, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_9023])).
% 13.22/5.27  tff(c_9196, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9194, c_9114])).
% 13.22/5.27  tff(c_9219, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9194, c_9194, c_12])).
% 13.22/5.27  tff(c_9259, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9219, c_8941])).
% 13.22/5.27  tff(c_9261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9196, c_9259])).
% 13.22/5.27  tff(c_9263, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_9176])).
% 13.22/5.27  tff(c_9334, plain, (![A_585, B_586]: (k2_relat_1(k2_zfmisc_1(A_585, B_586))=B_586 | k1_xboole_0=B_586 | k1_xboole_0=A_585)), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.22/5.27  tff(c_9343, plain, (k2_relat_1('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8941, c_9334])).
% 13.22/5.27  tff(c_9352, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_9263, c_9263, c_9343])).
% 13.22/5.27  tff(c_9262, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_9176])).
% 13.22/5.27  tff(c_9264, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_9263, c_9262])).
% 13.22/5.27  tff(c_9134, plain, (![B_570, A_571]: (v4_relat_1(B_570, A_571) | ~r1_tarski(k1_relat_1(B_570), A_571) | ~v1_relat_1(B_570))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.22/5.27  tff(c_9141, plain, (![B_574]: (v4_relat_1(B_574, k1_relat_1(B_574)) | ~v1_relat_1(B_574))), inference(resolution, [status(thm)], [c_6, c_9134])).
% 13.22/5.27  tff(c_9145, plain, (![B_574]: (k7_relat_1(B_574, k1_relat_1(B_574))=B_574 | ~v1_relat_1(B_574))), inference(resolution, [status(thm)], [c_9141, c_38])).
% 13.22/5.27  tff(c_9269, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9264, c_9145])).
% 13.22/5.27  tff(c_9279, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_9269])).
% 13.22/5.27  tff(c_9306, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9279, c_30])).
% 13.22/5.27  tff(c_9310, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_9306])).
% 13.22/5.27  tff(c_9356, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9352, c_9310])).
% 13.22/5.27  tff(c_8963, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8941, c_64])).
% 13.22/5.27  tff(c_9820, plain, (![A_623, B_624, C_625]: (k2_relset_1(A_623, B_624, C_625)=k2_relat_1(C_625) | ~m1_subset_1(C_625, k1_zfmisc_1(k2_zfmisc_1(A_623, B_624))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.22/5.27  tff(c_9875, plain, (![C_632]: (k2_relset_1('#skF_1', '#skF_1', C_632)=k2_relat_1(C_632) | ~m1_subset_1(C_632, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_8941, c_9820])).
% 13.22/5.27  tff(c_9878, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8963, c_9875])).
% 13.22/5.27  tff(c_9891, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_9878])).
% 13.22/5.27  tff(c_32, plain, (![B_23, A_21]: (k9_relat_1(B_23, k2_relat_1(A_21))=k2_relat_1(k5_relat_1(A_21, B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.22/5.27  tff(c_9901, plain, (![B_23]: (k2_relat_1(k5_relat_1('#skF_3', B_23))=k9_relat_1(B_23, '#skF_1') | ~v1_relat_1(B_23) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9891, c_32])).
% 13.22/5.27  tff(c_9908, plain, (![B_23]: (k2_relat_1(k5_relat_1('#skF_3', B_23))=k9_relat_1(B_23, '#skF_1') | ~v1_relat_1(B_23))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_9901])).
% 13.22/5.27  tff(c_8962, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8941, c_66])).
% 13.22/5.27  tff(c_10100, plain, (![B_649, F_647, A_648, C_645, E_650, D_646]: (k4_relset_1(A_648, B_649, C_645, D_646, E_650, F_647)=k5_relat_1(E_650, F_647) | ~m1_subset_1(F_647, k1_zfmisc_1(k2_zfmisc_1(C_645, D_646))) | ~m1_subset_1(E_650, k1_zfmisc_1(k2_zfmisc_1(A_648, B_649))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 13.22/5.27  tff(c_10147, plain, (![A_652, B_653, E_654, F_655]: (k4_relset_1(A_652, B_653, '#skF_1', '#skF_1', E_654, F_655)=k5_relat_1(E_654, F_655) | ~m1_subset_1(F_655, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(E_654, k1_zfmisc_1(k2_zfmisc_1(A_652, B_653))))), inference(superposition, [status(thm), theory('equality')], [c_8941, c_10100])).
% 13.22/5.27  tff(c_10597, plain, (![A_677, B_678, E_679]: (k4_relset_1(A_677, B_678, '#skF_1', '#skF_1', E_679, '#skF_2')=k5_relat_1(E_679, '#skF_2') | ~m1_subset_1(E_679, k1_zfmisc_1(k2_zfmisc_1(A_677, B_678))))), inference(resolution, [status(thm)], [c_8962, c_10147])).
% 13.22/5.27  tff(c_10770, plain, (![E_690]: (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', E_690, '#skF_2')=k5_relat_1(E_690, '#skF_2') | ~m1_subset_1(E_690, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_8941, c_10597])).
% 13.22/5.27  tff(c_10785, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_8963, c_10770])).
% 13.22/5.27  tff(c_11081, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_10785, c_52])).
% 13.22/5.27  tff(c_11085, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8963, c_8941, c_8962, c_8941, c_8941, c_11081])).
% 13.22/5.27  tff(c_9823, plain, (![C_625]: (k2_relset_1('#skF_1', '#skF_1', C_625)=k2_relat_1(C_625) | ~m1_subset_1(C_625, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_8941, c_9820])).
% 13.22/5.27  tff(c_11110, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_11085, c_9823])).
% 13.22/5.27  tff(c_11077, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10785, c_58])).
% 13.22/5.27  tff(c_14022, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11110, c_11077])).
% 13.22/5.27  tff(c_14085, plain, (k9_relat_1('#skF_2', '#skF_1')!='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9908, c_14022])).
% 13.22/5.27  tff(c_14088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_9356, c_14085])).
% 13.22/5.27  tff(c_14090, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_9023])).
% 13.22/5.27  tff(c_14107, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_14090, c_172])).
% 13.22/5.27  tff(c_8960, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8941, c_171])).
% 13.22/5.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.22/5.27  tff(c_8982, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_8960, c_2])).
% 13.22/5.27  tff(c_9007, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_8982])).
% 13.22/5.27  tff(c_14124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14107, c_9007])).
% 13.22/5.27  tff(c_14125, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_8982])).
% 13.22/5.27  tff(c_14131, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14125, c_8941])).
% 13.22/5.27  tff(c_14386, plain, (![A_840, B_841]: (k2_relat_1(k2_zfmisc_1(A_840, B_841))=B_841 | k1_xboole_0=B_841 | k1_xboole_0=A_840)), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.22/5.27  tff(c_14398, plain, (k2_relat_1('#skF_3')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14131, c_14386])).
% 13.22/5.27  tff(c_14412, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_14398])).
% 13.22/5.27  tff(c_14211, plain, (![B_821, A_822]: (k1_xboole_0=B_821 | k1_xboole_0=A_822 | k2_zfmisc_1(A_822, B_821)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.22/5.27  tff(c_14214, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_14131, c_14211])).
% 13.22/5.27  tff(c_14259, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_14214])).
% 13.22/5.27  tff(c_14422, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14412, c_14259])).
% 13.22/5.27  tff(c_14441, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14412, c_14412, c_12])).
% 13.22/5.27  tff(c_14512, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14441, c_14131])).
% 13.22/5.27  tff(c_14514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14422, c_14512])).
% 13.22/5.27  tff(c_14516, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_14398])).
% 13.22/5.27  tff(c_14515, plain, (k1_xboole_0='#skF_1' | k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_14398])).
% 13.22/5.27  tff(c_14517, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_14516, c_14515])).
% 13.22/5.27  tff(c_14548, plain, (![A_848, B_849]: (k1_relat_1(k2_zfmisc_1(A_848, B_849))=A_848 | k1_xboole_0=B_849 | k1_xboole_0=A_848)), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.22/5.27  tff(c_14581, plain, (k1_relat_1('#skF_3')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14131, c_14548])).
% 13.22/5.27  tff(c_14606, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_14516, c_14516, c_14581])).
% 13.22/5.27  tff(c_14356, plain, (![B_836, A_837]: (v4_relat_1(B_836, A_837) | ~r1_tarski(k1_relat_1(B_836), A_837) | ~v1_relat_1(B_836))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.22/5.27  tff(c_14365, plain, (![B_836]: (v4_relat_1(B_836, k1_relat_1(B_836)) | ~v1_relat_1(B_836))), inference(resolution, [status(thm)], [c_6, c_14356])).
% 13.22/5.27  tff(c_14622, plain, (v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14606, c_14365])).
% 13.22/5.27  tff(c_14645, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_14622])).
% 13.22/5.27  tff(c_14658, plain, (![B_850, A_851]: (k7_relat_1(B_850, A_851)=B_850 | ~v4_relat_1(B_850, A_851) | ~v1_relat_1(B_850))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.22/5.27  tff(c_14661, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14645, c_14658])).
% 13.22/5.27  tff(c_14667, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_195, c_14661])).
% 13.22/5.27  tff(c_14672, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14667, c_30])).
% 13.22/5.27  tff(c_14676, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_195, c_14517, c_14672])).
% 13.22/5.27  tff(c_14941, plain, (![B_876, A_877]: (k9_relat_1(B_876, k2_relat_1(A_877))=k2_relat_1(k5_relat_1(A_877, B_876)) | ~v1_relat_1(B_876) | ~v1_relat_1(A_877))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.22/5.27  tff(c_14953, plain, (![B_876]: (k2_relat_1(k5_relat_1('#skF_3', B_876))=k9_relat_1(B_876, '#skF_1') | ~v1_relat_1(B_876) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14517, c_14941])).
% 13.22/5.27  tff(c_14963, plain, (![B_876]: (k2_relat_1(k5_relat_1('#skF_3', B_876))=k9_relat_1(B_876, '#skF_1') | ~v1_relat_1(B_876))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_14953])).
% 13.22/5.27  tff(c_14128, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14125, c_8963])).
% 13.22/5.27  tff(c_15369, plain, (![E_912, A_910, D_908, B_911, C_907, F_909]: (k4_relset_1(A_910, B_911, C_907, D_908, E_912, F_909)=k5_relat_1(E_912, F_909) | ~m1_subset_1(F_909, k1_zfmisc_1(k2_zfmisc_1(C_907, D_908))) | ~m1_subset_1(E_912, k1_zfmisc_1(k2_zfmisc_1(A_910, B_911))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 13.22/5.27  tff(c_15417, plain, (![A_913, B_914, E_915, F_916]: (k4_relset_1(A_913, B_914, '#skF_1', '#skF_1', E_915, F_916)=k5_relat_1(E_915, F_916) | ~m1_subset_1(F_916, k1_zfmisc_1('#skF_3')) | ~m1_subset_1(E_915, k1_zfmisc_1(k2_zfmisc_1(A_913, B_914))))), inference(superposition, [status(thm), theory('equality')], [c_14131, c_15369])).
% 13.22/5.27  tff(c_15530, plain, (![A_923, B_924, E_925]: (k4_relset_1(A_923, B_924, '#skF_1', '#skF_1', E_925, '#skF_3')=k5_relat_1(E_925, '#skF_3') | ~m1_subset_1(E_925, k1_zfmisc_1(k2_zfmisc_1(A_923, B_924))))), inference(resolution, [status(thm)], [c_14128, c_15417])).
% 13.22/5.27  tff(c_16204, plain, (![E_963]: (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', E_963, '#skF_3')=k5_relat_1(E_963, '#skF_3') | ~m1_subset_1(E_963, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_14131, c_15530])).
% 13.22/5.27  tff(c_16216, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_3')=k5_relat_1('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_14128, c_16204])).
% 13.22/5.27  tff(c_16533, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16216, c_52])).
% 13.22/5.27  tff(c_16537, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14128, c_14131, c_14128, c_14131, c_14131, c_16533])).
% 13.22/5.27  tff(c_15199, plain, (![A_887, B_888, C_889]: (k2_relset_1(A_887, B_888, C_889)=k2_relat_1(C_889) | ~m1_subset_1(C_889, k1_zfmisc_1(k2_zfmisc_1(A_887, B_888))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.22/5.27  tff(c_15202, plain, (![C_889]: (k2_relset_1('#skF_1', '#skF_1', C_889)=k2_relat_1(C_889) | ~m1_subset_1(C_889, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_14131, c_15199])).
% 13.22/5.27  tff(c_16559, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_3'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_16537, c_15202])).
% 13.22/5.27  tff(c_14135, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14125, c_58])).
% 13.22/5.27  tff(c_16529, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16216, c_14135])).
% 13.22/5.27  tff(c_17241, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16559, c_16529])).
% 13.22/5.27  tff(c_17248, plain, (k9_relat_1('#skF_3', '#skF_1')!='#skF_1' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14963, c_17241])).
% 13.22/5.27  tff(c_17251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_195, c_14676, c_17248])).
% 13.22/5.27  tff(c_17253, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_14214])).
% 13.22/5.27  tff(c_17252, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_14214])).
% 13.22/5.27  tff(c_17306, plain, ('#skF_3'='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17253, c_17253, c_17252])).
% 13.22/5.27  tff(c_17307, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_17306])).
% 13.22/5.27  tff(c_8943, plain, (![A_558]: (k1_relat_1(A_558)=k1_xboole_0 | k2_relat_1(A_558)!=k1_xboole_0 | ~v1_relat_1(A_558))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.22/5.27  tff(c_8957, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | k2_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_194, c_8943])).
% 13.22/5.27  tff(c_14127, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8957])).
% 13.22/5.27  tff(c_14146, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14125, c_14127])).
% 13.22/5.27  tff(c_17261, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17253, c_14146])).
% 13.22/5.27  tff(c_17309, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17307, c_17307, c_17261])).
% 13.22/5.27  tff(c_17275, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_17253, c_14])).
% 13.22/5.27  tff(c_17355, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_17307, c_17275])).
% 13.22/5.27  tff(c_17734, plain, (![A_1047, B_1048, C_1049]: (k2_relset_1(A_1047, B_1048, C_1049)=k2_relat_1(C_1049) | ~m1_subset_1(C_1049, k1_zfmisc_1(k2_zfmisc_1(A_1047, B_1048))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.22/5.27  tff(c_17752, plain, (![A_1052, B_1053]: (k2_relset_1(A_1052, B_1053, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_17355, c_17734])).
% 13.22/5.27  tff(c_17320, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17307, c_60])).
% 13.22/5.27  tff(c_17756, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_17752, c_17320])).
% 13.22/5.27  tff(c_17763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17309, c_17756])).
% 13.22/5.27  tff(c_17764, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_17306])).
% 13.22/5.27  tff(c_17765, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_17306])).
% 13.22/5.27  tff(c_17796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17764, c_17765])).
% 13.22/5.27  tff(c_17798, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8957])).
% 13.22/5.27  tff(c_17835, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14125, c_17798])).
% 13.22/5.27  tff(c_17802, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14125, c_8941])).
% 13.22/5.27  tff(c_18456, plain, (![A_1097, B_1098]: (k2_relat_1(k2_zfmisc_1(A_1097, B_1098))=B_1098 | k1_xboole_0=B_1098 | k1_xboole_0=A_1097)), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.22/5.27  tff(c_18465, plain, (k2_relat_1('#skF_3')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_17802, c_18456])).
% 13.22/5.27  tff(c_18474, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17835, c_18465])).
% 13.22/5.27  tff(c_18479, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_18474])).
% 13.22/5.27  tff(c_17887, plain, (![B_1057, A_1058]: (k1_xboole_0=B_1057 | k1_xboole_0=A_1058 | k2_zfmisc_1(A_1058, B_1057)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.22/5.27  tff(c_17890, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_17802, c_17887])).
% 13.22/5.27  tff(c_18326, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_17890])).
% 13.22/5.27  tff(c_18484, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18479, c_18326])).
% 13.22/5.27  tff(c_18503, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18479, c_18479, c_12])).
% 13.22/5.27  tff(c_18667, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18503, c_17802])).
% 13.22/5.27  tff(c_18669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18484, c_18667])).
% 13.22/5.27  tff(c_18671, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_18474])).
% 13.22/5.27  tff(c_18670, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_18474])).
% 13.22/5.27  tff(c_18672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18671, c_18671, c_18670])).
% 13.22/5.27  tff(c_18674, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_17890])).
% 13.22/5.27  tff(c_18673, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_17890])).
% 13.22/5.27  tff(c_18757, plain, ('#skF_3'='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18674, c_18674, c_18673])).
% 13.22/5.27  tff(c_18758, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_18757])).
% 13.22/5.27  tff(c_17797, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8957])).
% 13.22/5.27  tff(c_17830, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14125, c_17797])).
% 13.22/5.27  tff(c_18013, plain, (![A_1073, B_1074]: (k1_relat_1(k2_zfmisc_1(A_1073, B_1074))=A_1073 | k1_xboole_0=B_1074 | k1_xboole_0=A_1073)), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.22/5.27  tff(c_18028, plain, (k1_relat_1('#skF_3')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_17802, c_18013])).
% 13.22/5.27  tff(c_18041, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17830, c_18028])).
% 13.22/5.27  tff(c_18052, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_18041])).
% 13.22/5.27  tff(c_17956, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_17890])).
% 13.22/5.27  tff(c_18055, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18052, c_17956])).
% 13.22/5.27  tff(c_18074, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18052, c_18052, c_12])).
% 13.22/5.27  tff(c_18172, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18074, c_17802])).
% 13.22/5.27  tff(c_18174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18055, c_18172])).
% 13.22/5.27  tff(c_18176, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_18041])).
% 13.22/5.27  tff(c_18175, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_18041])).
% 13.22/5.27  tff(c_18177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18176, c_18176, c_18175])).
% 13.22/5.27  tff(c_18179, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_17890])).
% 13.22/5.27  tff(c_18185, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18179, c_17835])).
% 13.22/5.27  tff(c_8958, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_75, c_8943])).
% 13.22/5.27  tff(c_17901, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8958])).
% 13.22/5.27  tff(c_18181, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18179, c_18179, c_17901])).
% 13.22/5.27  tff(c_18247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18185, c_18181])).
% 13.22/5.27  tff(c_18249, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_8958])).
% 13.22/5.27  tff(c_18675, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18674, c_18674, c_18249])).
% 13.22/5.27  tff(c_18763, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18758, c_18758, c_18675])).
% 13.22/5.27  tff(c_18696, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_18674, c_14])).
% 13.22/5.27  tff(c_18856, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_18758, c_18696])).
% 13.22/5.27  tff(c_19475, plain, (![A_1165, B_1166, C_1167]: (k2_relset_1(A_1165, B_1166, C_1167)=k2_relat_1(C_1167) | ~m1_subset_1(C_1167, k1_zfmisc_1(k2_zfmisc_1(A_1165, B_1166))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.22/5.27  tff(c_19482, plain, (![A_1165, B_1166]: (k2_relset_1(A_1165, B_1166, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_18856, c_19475])).
% 13.22/5.27  tff(c_19491, plain, (![A_1165, B_1166]: (k2_relset_1(A_1165, B_1166, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18763, c_19482])).
% 13.22/5.27  tff(c_44, plain, (![A_29]: (k5_relat_1(k1_xboole_0, A_29)=k1_xboole_0 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.22/5.27  tff(c_212, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_195, c_44])).
% 13.22/5.27  tff(c_18685, plain, (k5_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18674, c_18674, c_212])).
% 13.22/5.27  tff(c_18837, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18758, c_18758, c_18758, c_18685])).
% 13.22/5.27  tff(c_18687, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_18674, c_172])).
% 13.22/5.27  tff(c_18761, plain, (![A_5]: (r1_tarski('#skF_1', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_18758, c_18687])).
% 13.22/5.27  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.22/5.27  tff(c_19819, plain, (![C_1200, A_1203, F_1202, E_1205, B_1204, D_1201]: (k4_relset_1(A_1203, B_1204, C_1200, D_1201, E_1205, F_1202)=k5_relat_1(E_1205, F_1202) | ~m1_subset_1(F_1202, k1_zfmisc_1(k2_zfmisc_1(C_1200, D_1201))) | ~m1_subset_1(E_1205, k1_zfmisc_1(k2_zfmisc_1(A_1203, B_1204))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 13.22/5.27  tff(c_22102, plain, (![A_1336, E_1337, B_1335, C_1333, A_1338, D_1334]: (k4_relset_1(A_1338, B_1335, C_1333, D_1334, E_1337, A_1336)=k5_relat_1(E_1337, A_1336) | ~m1_subset_1(E_1337, k1_zfmisc_1(k2_zfmisc_1(A_1338, B_1335))) | ~r1_tarski(A_1336, k2_zfmisc_1(C_1333, D_1334)))), inference(resolution, [status(thm)], [c_18, c_19819])).
% 13.22/5.27  tff(c_31093, plain, (![B_1701, D_1699, A_1702, A_1700, C_1703]: (k4_relset_1(A_1700, B_1701, C_1703, D_1699, '#skF_1', A_1702)=k5_relat_1('#skF_1', A_1702) | ~r1_tarski(A_1702, k2_zfmisc_1(C_1703, D_1699)))), inference(resolution, [status(thm)], [c_18856, c_22102])).
% 13.22/5.27  tff(c_31110, plain, (![A_1700, B_1701, C_1703, D_1699]: (k4_relset_1(A_1700, B_1701, C_1703, D_1699, '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_18761, c_31093])).
% 13.22/5.27  tff(c_31127, plain, (![A_1700, B_1701, C_1703, D_1699]: (k4_relset_1(A_1700, B_1701, C_1703, D_1699, '#skF_1', '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18837, c_31110])).
% 13.22/5.27  tff(c_17806, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14125, c_58])).
% 13.22/5.27  tff(c_18769, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18758, c_18758, c_17806])).
% 13.22/5.27  tff(c_31152, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_31127, c_18769])).
% 13.22/5.27  tff(c_31159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19491, c_31152])).
% 13.22/5.27  tff(c_31160, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_18757])).
% 13.22/5.27  tff(c_31161, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_18757])).
% 13.22/5.27  tff(c_31181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31160, c_31161])).
% 13.22/5.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.22/5.27  
% 13.22/5.27  Inference rules
% 13.22/5.27  ----------------------
% 13.22/5.27  #Ref     : 0
% 13.22/5.27  #Sup     : 6733
% 13.22/5.27  #Fact    : 0
% 13.22/5.27  #Define  : 0
% 13.22/5.27  #Split   : 63
% 13.22/5.27  #Chain   : 0
% 13.22/5.27  #Close   : 0
% 13.22/5.27  
% 13.22/5.27  Ordering : KBO
% 13.22/5.27  
% 13.22/5.27  Simplification rules
% 13.22/5.27  ----------------------
% 13.22/5.27  #Subsume      : 935
% 13.22/5.27  #Demod        : 7800
% 13.22/5.27  #Tautology    : 3214
% 13.22/5.27  #SimpNegUnit  : 204
% 13.22/5.27  #BackRed      : 964
% 13.22/5.27  
% 13.22/5.27  #Partial instantiations: 0
% 13.22/5.27  #Strategies tried      : 1
% 13.22/5.27  
% 13.22/5.27  Timing (in seconds)
% 13.22/5.27  ----------------------
% 13.22/5.27  Preprocessing        : 0.34
% 13.22/5.27  Parsing              : 0.18
% 13.22/5.27  CNF conversion       : 0.02
% 13.22/5.27  Main loop            : 4.10
% 13.22/5.27  Inferencing          : 1.14
% 13.22/5.27  Reduction            : 1.49
% 13.22/5.27  Demodulation         : 1.10
% 13.22/5.27  BG Simplification    : 0.12
% 13.22/5.27  Subsumption          : 1.07
% 13.22/5.27  Abstraction          : 0.16
% 13.22/5.27  MUC search           : 0.00
% 13.22/5.27  Cooper               : 0.00
% 13.22/5.27  Total                : 4.55
% 13.22/5.27  Index Insertion      : 0.00
% 13.22/5.27  Index Deletion       : 0.00
% 13.22/5.27  Index Matching       : 0.00
% 13.22/5.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
