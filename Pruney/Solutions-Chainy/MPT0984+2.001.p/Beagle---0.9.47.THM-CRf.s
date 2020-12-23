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
% DateTime   : Thu Dec  3 10:12:24 EST 2020

% Result     : Theorem 7.06s
% Output     : CNFRefutation 7.42s
% Verified   : 
% Statistics : Number of formulae       :  347 (2510 expanded)
%              Number of leaves         :   50 ( 763 expanded)
%              Depth                    :   18
%              Number of atoms          :  572 (8571 expanded)
%              Number of equality atoms :  212 (3045 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_186,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
                & k2_relset_1(A,B,D) = B )
             => ( ( C = k1_xboole_0
                  & B != k1_xboole_0 )
                | ( v2_funct_1(D)
                  & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_139,axiom,(
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

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_45,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_159,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_74,plain,
    ( ~ v2_funct_1('#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_96,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_141,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_152,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_141])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_88,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_154,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_141])).

tff(c_92,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_97,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_84,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_476,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k8_relset_1(A_105,B_106,C_107,D_108) = k10_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_490,plain,(
    ! [D_108] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_108) = k10_relat_1('#skF_6',D_108) ),
    inference(resolution,[status(thm)],[c_82,c_476])).

tff(c_649,plain,(
    ! [A_129,B_130,C_131] :
      ( k8_relset_1(A_129,B_130,C_131,B_130) = k1_relset_1(A_129,B_130,C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_655,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_4') = k1_relset_1('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_649])).

tff(c_665,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k10_relat_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_655])).

tff(c_781,plain,(
    ! [B_139,A_140,C_141] :
      ( k1_xboole_0 = B_139
      | k1_relset_1(A_140,B_139,C_141) = A_140
      | ~ v1_funct_2(C_141,A_140,B_139)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_790,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_781])).

tff(c_805,plain,
    ( k1_xboole_0 = '#skF_4'
    | k10_relat_1('#skF_6','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_665,c_790])).

tff(c_806,plain,(
    k10_relat_1('#skF_6','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_805])).

tff(c_884,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_665])).

tff(c_292,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_307,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_292])).

tff(c_598,plain,(
    ! [A_121,B_122,C_123] :
      ( k7_relset_1(A_121,B_122,C_123,A_121) = k2_relset_1(A_121,B_122,C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_604,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_3') = k2_relset_1('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_598])).

tff(c_614,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_604])).

tff(c_1191,plain,(
    ! [B_171,A_172,C_173] :
      ( k8_relset_1(B_171,A_172,C_173,k7_relset_1(B_171,A_172,C_173,B_171)) = k1_relset_1(B_171,A_172,C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(B_171,A_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1195,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_6',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_3')) = k1_relset_1('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_1191])).

tff(c_1203,plain,(
    k10_relat_1('#skF_6',k2_relat_1('#skF_6')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_490,c_614,c_1195])).

tff(c_24,plain,(
    ! [A_11] :
      ( k10_relat_1(A_11,k2_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1211,plain,
    ( k1_relat_1('#skF_6') = '#skF_3'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_24])).

tff(c_1218,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_1211])).

tff(c_78,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_305,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_292])).

tff(c_310,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_305])).

tff(c_1347,plain,(
    ! [D_181,C_185,F_184,E_180,A_183,B_182] :
      ( k1_partfun1(A_183,B_182,C_185,D_181,E_180,F_184) = k5_relat_1(E_180,F_184)
      | ~ m1_subset_1(F_184,k1_zfmisc_1(k2_zfmisc_1(C_185,D_181)))
      | ~ v1_funct_1(F_184)
      | ~ m1_subset_1(E_180,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182)))
      | ~ v1_funct_1(E_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1351,plain,(
    ! [A_183,B_182,E_180] :
      ( k1_partfun1(A_183,B_182,'#skF_3','#skF_4',E_180,'#skF_6') = k5_relat_1(E_180,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_180,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182)))
      | ~ v1_funct_1(E_180) ) ),
    inference(resolution,[status(thm)],[c_82,c_1347])).

tff(c_1717,plain,(
    ! [A_203,B_204,E_205] :
      ( k1_partfun1(A_203,B_204,'#skF_3','#skF_4',E_205,'#skF_6') = k5_relat_1(E_205,'#skF_6')
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204)))
      | ~ v1_funct_1(E_205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1351])).

tff(c_1733,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_4','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_1717])).

tff(c_1744,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_4','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1733])).

tff(c_80,plain,(
    v2_funct_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1749,plain,(
    v2_funct_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1744,c_80])).

tff(c_32,plain,(
    ! [B_15,A_13] :
      ( v2_funct_1(B_15)
      | k2_relat_1(B_15) != k1_relat_1(A_13)
      | ~ v2_funct_1(k5_relat_1(B_15,A_13))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1759,plain,
    ( v2_funct_1('#skF_5')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1749,c_32])).

tff(c_1765,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_86,c_154,c_92,c_1218,c_310,c_1759])).

tff(c_1767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1765])).

tff(c_1769,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1768,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1775,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1769,c_1768])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1770,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1768,c_2])).

tff(c_1780,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_1770])).

tff(c_1801,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_88])).

tff(c_1825,plain,(
    ! [C_212,A_213,B_214] :
      ( v1_relat_1(C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1837,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1801,c_1825])).

tff(c_26,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) = k1_xboole_0
      | k2_relat_1(A_12) != k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1856,plain,(
    ! [A_218] :
      ( k1_relat_1(A_218) = '#skF_4'
      | k2_relat_1(A_218) != '#skF_4'
      | ~ v1_relat_1(A_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1769,c_1769,c_26])).

tff(c_1868,plain,
    ( k1_relat_1('#skF_5') = '#skF_4'
    | k2_relat_1('#skF_5') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1837,c_1856])).

tff(c_2607,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1868])).

tff(c_2973,plain,(
    ! [C_348,B_349,A_350] :
      ( v5_relat_1(C_348,B_349)
      | ~ m1_subset_1(C_348,k1_zfmisc_1(k2_zfmisc_1(A_350,B_349))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2985,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1801,c_2973])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_5] : v1_xboole_0('#skF_1'(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1794,plain,(
    ! [B_207,A_208] :
      ( ~ v1_xboole_0(B_207)
      | B_207 = A_208
      | ~ v1_xboole_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1802,plain,(
    ! [A_209] :
      ( A_209 = '#skF_4'
      | ~ v1_xboole_0(A_209) ) ),
    inference(resolution,[status(thm)],[c_1780,c_1794])).

tff(c_1811,plain,(
    ! [A_5] : '#skF_1'(A_5) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_1802])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1812,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1811,c_14])).

tff(c_2984,plain,(
    ! [B_349] : v5_relat_1('#skF_4',B_349) ),
    inference(resolution,[status(thm)],[c_1812,c_2973])).

tff(c_1836,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1812,c_1825])).

tff(c_28,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) = k1_xboole_0
      | k1_relat_1(A_12) != k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2588,plain,(
    ! [A_305] :
      ( k2_relat_1(A_305) = '#skF_4'
      | k1_relat_1(A_305) != '#skF_4'
      | ~ v1_relat_1(A_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1769,c_1769,c_28])).

tff(c_2598,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1836,c_2588])).

tff(c_2609,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2598])).

tff(c_1866,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | k2_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1836,c_1856])).

tff(c_2610,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2609,c_1866])).

tff(c_1793,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_82])).

tff(c_2749,plain,(
    ! [C_329,A_330,B_331] :
      ( v1_xboole_0(C_329)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331)))
      | ~ v1_xboole_0(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2759,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1793,c_2749])).

tff(c_2765,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_2759])).

tff(c_1799,plain,(
    ! [A_208] :
      ( A_208 = '#skF_4'
      | ~ v1_xboole_0(A_208) ) ),
    inference(resolution,[status(thm)],[c_1780,c_1794])).

tff(c_2771,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2765,c_1799])).

tff(c_1838,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1793,c_1825])).

tff(c_1867,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | k2_relat_1('#skF_6') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1838,c_1856])).

tff(c_1869,plain,(
    k2_relat_1('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1867])).

tff(c_2036,plain,(
    ! [A_247] :
      ( k2_relat_1(A_247) = '#skF_4'
      | k1_relat_1(A_247) != '#skF_4'
      | ~ v1_relat_1(A_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1769,c_1769,c_28])).

tff(c_2047,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | k1_relat_1('#skF_6') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1838,c_2036])).

tff(c_2069,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1869,c_2047])).

tff(c_2433,plain,(
    ! [C_289,A_290,B_291] :
      ( v4_relat_1(C_289,A_290)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2446,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1793,c_2433])).

tff(c_18,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2444,plain,(
    ! [A_290] : v4_relat_1('#skF_4',A_290) ),
    inference(resolution,[status(thm)],[c_1812,c_2433])).

tff(c_2070,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1866])).

tff(c_2046,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1836,c_2036])).

tff(c_2071,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2070,c_2046])).

tff(c_1870,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1868])).

tff(c_1787,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_1775,c_78])).

tff(c_2016,plain,(
    ! [A_244,B_245,C_246] :
      ( k2_relset_1(A_244,B_245,C_246) = k2_relat_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2026,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1801,c_2016])).

tff(c_2030,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_2026])).

tff(c_2032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1870,c_2030])).

tff(c_2034,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1868])).

tff(c_2033,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1868])).

tff(c_2284,plain,(
    ! [A_280] :
      ( m1_subset_1(A_280,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_280),k2_relat_1(A_280))))
      | ~ v1_funct_1(A_280)
      | ~ v1_relat_1(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2302,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1('#skF_5'))))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2033,c_2284])).

tff(c_2312,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1837,c_92,c_2034,c_2302])).

tff(c_40,plain,(
    ! [C_25,A_22,B_23] :
      ( v1_xboole_0(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2320,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2312,c_40])).

tff(c_2334,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_2320])).

tff(c_2346,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2334,c_1799])).

tff(c_2374,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2346,c_2033])).

tff(c_2395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2071,c_2374])).

tff(c_2396,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1866])).

tff(c_2411,plain,(
    ! [B_285,A_286] :
      ( r1_tarski(k1_relat_1(B_285),A_286)
      | ~ v4_relat_1(B_285,A_286)
      | ~ v1_relat_1(B_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2416,plain,(
    ! [A_286] :
      ( r1_tarski('#skF_4',A_286)
      | ~ v4_relat_1('#skF_4',A_286)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2396,c_2411])).

tff(c_2422,plain,(
    ! [A_286] :
      ( r1_tarski('#skF_4',A_286)
      | ~ v4_relat_1('#skF_4',A_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1836,c_2416])).

tff(c_2479,plain,(
    ! [A_295] : r1_tarski('#skF_4',A_295) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2444,c_2422])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2484,plain,(
    ! [A_296] :
      ( A_296 = '#skF_4'
      | ~ r1_tarski(A_296,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2479,c_4])).

tff(c_2549,plain,(
    ! [B_304] :
      ( k1_relat_1(B_304) = '#skF_4'
      | ~ v4_relat_1(B_304,'#skF_4')
      | ~ v1_relat_1(B_304) ) ),
    inference(resolution,[status(thm)],[c_18,c_2484])).

tff(c_2560,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2446,c_2549])).

tff(c_2569,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1838,c_2560])).

tff(c_2571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2069,c_2569])).

tff(c_2573,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1867])).

tff(c_2781,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2771,c_2573])).

tff(c_2798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2610,c_2781])).

tff(c_2799,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2598])).

tff(c_2837,plain,(
    ! [B_336,A_337] :
      ( r1_tarski(k2_relat_1(B_336),A_337)
      | ~ v5_relat_1(B_336,A_337)
      | ~ v1_relat_1(B_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2842,plain,(
    ! [A_337] :
      ( r1_tarski('#skF_4',A_337)
      | ~ v5_relat_1('#skF_4',A_337)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2799,c_2837])).

tff(c_2848,plain,(
    ! [A_337] :
      ( r1_tarski('#skF_4',A_337)
      | ~ v5_relat_1('#skF_4',A_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1836,c_2842])).

tff(c_2998,plain,(
    ! [A_352] : r1_tarski('#skF_4',A_352) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2984,c_2848])).

tff(c_3008,plain,(
    ! [A_355] :
      ( A_355 = '#skF_4'
      | ~ r1_tarski(A_355,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2998,c_4])).

tff(c_3035,plain,(
    ! [B_357] :
      ( k2_relat_1(B_357) = '#skF_4'
      | ~ v5_relat_1(B_357,'#skF_4')
      | ~ v1_relat_1(B_357) ) ),
    inference(resolution,[status(thm)],[c_22,c_3008])).

tff(c_3046,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2985,c_3035])).

tff(c_3055,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1837,c_3046])).

tff(c_3057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2607,c_3055])).

tff(c_3058,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1868])).

tff(c_3059,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1868])).

tff(c_3717,plain,(
    ! [A_424] :
      ( m1_subset_1(A_424,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_424),k2_relat_1(A_424))))
      | ~ v1_funct_1(A_424)
      | ~ v1_relat_1(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_3741,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3059,c_3717])).

tff(c_3755,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1837,c_92,c_3058,c_3741])).

tff(c_3763,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3755,c_40])).

tff(c_3777,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_3763])).

tff(c_3789,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3777,c_1799])).

tff(c_3804,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3789,c_96])).

tff(c_3610,plain,(
    ! [C_414,A_415,B_416] :
      ( v1_xboole_0(C_414)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416)))
      | ~ v1_xboole_0(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3620,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1793,c_3610])).

tff(c_3626,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_3620])).

tff(c_3663,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3626,c_1799])).

tff(c_3675,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3663,c_86])).

tff(c_3094,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2598])).

tff(c_3095,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3094,c_1866])).

tff(c_3304,plain,(
    ! [C_385,A_386,B_387] :
      ( v1_xboole_0(C_385)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387)))
      | ~ v1_xboole_0(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3314,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1793,c_3304])).

tff(c_3320,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_3314])).

tff(c_3326,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3320,c_1799])).

tff(c_3336,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3326,c_2573])).

tff(c_3353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3095,c_3336])).

tff(c_3355,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2598])).

tff(c_3354,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2598])).

tff(c_4369,plain,(
    ! [E_494,C_499,A_497,D_495,B_496,F_498] :
      ( k1_partfun1(A_497,B_496,C_499,D_495,E_494,F_498) = k5_relat_1(E_494,F_498)
      | ~ m1_subset_1(F_498,k1_zfmisc_1(k2_zfmisc_1(C_499,D_495)))
      | ~ v1_funct_1(F_498)
      | ~ m1_subset_1(E_494,k1_zfmisc_1(k2_zfmisc_1(A_497,B_496)))
      | ~ v1_funct_1(E_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4374,plain,(
    ! [E_494,C_499,A_497,D_495,B_496] :
      ( k1_partfun1(A_497,B_496,C_499,D_495,E_494,'#skF_4') = k5_relat_1(E_494,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_494,k1_zfmisc_1(k2_zfmisc_1(A_497,B_496)))
      | ~ v1_funct_1(E_494) ) ),
    inference(resolution,[status(thm)],[c_1812,c_4369])).

tff(c_4455,plain,(
    ! [C_511,E_509,D_510,B_512,A_513] :
      ( k1_partfun1(A_513,B_512,C_511,D_510,E_509,'#skF_4') = k5_relat_1(E_509,'#skF_4')
      | ~ m1_subset_1(E_509,k1_zfmisc_1(k2_zfmisc_1(A_513,B_512)))
      | ~ v1_funct_1(E_509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3675,c_4374])).

tff(c_4460,plain,(
    ! [A_513,B_512,C_511,D_510] :
      ( k1_partfun1(A_513,B_512,C_511,D_510,'#skF_4','#skF_4') = k5_relat_1('#skF_4','#skF_4')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1812,c_4455])).

tff(c_4464,plain,(
    ! [A_513,B_512,C_511,D_510] : k1_partfun1(A_513,B_512,C_511,D_510,'#skF_4','#skF_4') = k5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3675,c_4460])).

tff(c_1823,plain,(
    v2_funct_1(k1_partfun1('#skF_2','#skF_4','#skF_4','#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_1775,c_80])).

tff(c_3672,plain,(
    v2_funct_1(k1_partfun1('#skF_2','#skF_4','#skF_4','#skF_4','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3663,c_1823])).

tff(c_3793,plain,(
    v2_funct_1(k1_partfun1('#skF_2','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3789,c_3672])).

tff(c_4487,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4464,c_3793])).

tff(c_4497,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4487,c_32])).

tff(c_4503,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1836,c_3675,c_3355,c_3354,c_4497])).

tff(c_4505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3804,c_4503])).

tff(c_4506,plain,(
    ~ v2_funct_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_4544,plain,(
    ! [C_526,A_527,B_528] :
      ( v1_relat_1(C_526)
      | ~ m1_subset_1(C_526,k1_zfmisc_1(k2_zfmisc_1(A_527,B_528))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4555,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_4544])).

tff(c_4557,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_4544])).

tff(c_4508,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_4761,plain,(
    ! [A_561,B_562,C_563,D_564] :
      ( k8_relset_1(A_561,B_562,C_563,D_564) = k10_relat_1(C_563,D_564)
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(A_561,B_562))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4772,plain,(
    ! [D_564] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_564) = k10_relat_1('#skF_6',D_564) ),
    inference(resolution,[status(thm)],[c_82,c_4761])).

tff(c_5043,plain,(
    ! [A_593,B_594,C_595] :
      ( k8_relset_1(A_593,B_594,C_595,B_594) = k1_relset_1(A_593,B_594,C_595)
      | ~ m1_subset_1(C_595,k1_zfmisc_1(k2_zfmisc_1(A_593,B_594))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_5049,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_4') = k1_relset_1('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_5043])).

tff(c_5059,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k10_relat_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4772,c_5049])).

tff(c_5157,plain,(
    ! [B_609,A_610,C_611] :
      ( k1_xboole_0 = B_609
      | k1_relset_1(A_610,B_609,C_611) = A_610
      | ~ v1_funct_2(C_611,A_610,B_609)
      | ~ m1_subset_1(C_611,k1_zfmisc_1(k2_zfmisc_1(A_610,B_609))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_5166,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_5157])).

tff(c_5181,plain,
    ( k1_xboole_0 = '#skF_4'
    | k10_relat_1('#skF_6','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5059,c_5166])).

tff(c_5182,plain,(
    k10_relat_1('#skF_6','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4508,c_5181])).

tff(c_5260,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5182,c_5059])).

tff(c_4707,plain,(
    ! [A_558,B_559,C_560] :
      ( k2_relset_1(A_558,B_559,C_560) = k2_relat_1(C_560)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(A_558,B_559))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4722,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_4707])).

tff(c_4949,plain,(
    ! [A_582,B_583,C_584] :
      ( k7_relset_1(A_582,B_583,C_584,A_582) = k2_relset_1(A_582,B_583,C_584)
      | ~ m1_subset_1(C_584,k1_zfmisc_1(k2_zfmisc_1(A_582,B_583))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4955,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_3') = k2_relset_1('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_4949])).

tff(c_4965,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4722,c_4955])).

tff(c_5504,plain,(
    ! [B_629,A_630,C_631] :
      ( k8_relset_1(B_629,A_630,C_631,k7_relset_1(B_629,A_630,C_631,B_629)) = k1_relset_1(B_629,A_630,C_631)
      | ~ m1_subset_1(C_631,k1_zfmisc_1(k2_zfmisc_1(B_629,A_630))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5508,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_6',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_3')) = k1_relset_1('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_5504])).

tff(c_5516,plain,(
    k10_relat_1('#skF_6',k2_relat_1('#skF_6')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5260,c_4772,c_4965,c_5508])).

tff(c_5528,plain,
    ( k1_relat_1('#skF_6') = '#skF_3'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5516,c_24])).

tff(c_5535,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4555,c_5528])).

tff(c_4720,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_4707])).

tff(c_4725,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4720])).

tff(c_5776,plain,(
    ! [F_649,A_648,E_645,C_650,B_647,D_646] :
      ( k1_partfun1(A_648,B_647,C_650,D_646,E_645,F_649) = k5_relat_1(E_645,F_649)
      | ~ m1_subset_1(F_649,k1_zfmisc_1(k2_zfmisc_1(C_650,D_646)))
      | ~ v1_funct_1(F_649)
      | ~ m1_subset_1(E_645,k1_zfmisc_1(k2_zfmisc_1(A_648,B_647)))
      | ~ v1_funct_1(E_645) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5782,plain,(
    ! [A_648,B_647,E_645] :
      ( k1_partfun1(A_648,B_647,'#skF_3','#skF_4',E_645,'#skF_6') = k5_relat_1(E_645,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_645,k1_zfmisc_1(k2_zfmisc_1(A_648,B_647)))
      | ~ v1_funct_1(E_645) ) ),
    inference(resolution,[status(thm)],[c_82,c_5776])).

tff(c_5974,plain,(
    ! [A_662,B_663,E_664] :
      ( k1_partfun1(A_662,B_663,'#skF_3','#skF_4',E_664,'#skF_6') = k5_relat_1(E_664,'#skF_6')
      | ~ m1_subset_1(E_664,k1_zfmisc_1(k2_zfmisc_1(A_662,B_663)))
      | ~ v1_funct_1(E_664) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_5782])).

tff(c_5990,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_4','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_5974])).

tff(c_6001,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_4','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_5990])).

tff(c_6006,plain,(
    v2_funct_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6001,c_80])).

tff(c_30,plain,(
    ! [A_13,B_15] :
      ( v2_funct_1(A_13)
      | k2_relat_1(B_15) != k1_relat_1(A_13)
      | ~ v2_funct_1(k5_relat_1(B_15,A_13))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6016,plain,
    ( v2_funct_1('#skF_6')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6006,c_30])).

tff(c_6022,plain,(
    v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4555,c_86,c_4557,c_92,c_5535,c_4725,c_6016])).

tff(c_6024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4506,c_6022])).

tff(c_6026,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_6025,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_6032,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6026,c_6025])).

tff(c_6027,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6025,c_2])).

tff(c_6037,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6032,c_6027])).

tff(c_6050,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6032,c_82])).

tff(c_7908,plain,(
    ! [C_875,A_876,B_877] :
      ( v1_xboole_0(C_875)
      | ~ m1_subset_1(C_875,k1_zfmisc_1(k2_zfmisc_1(A_876,B_877)))
      | ~ v1_xboole_0(A_876) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7918,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6050,c_7908])).

tff(c_7924,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6037,c_7918])).

tff(c_6051,plain,(
    ! [B_666,A_667] :
      ( ~ v1_xboole_0(B_666)
      | B_666 = A_667
      | ~ v1_xboole_0(A_667) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6056,plain,(
    ! [A_667] :
      ( A_667 = '#skF_4'
      | ~ v1_xboole_0(A_667) ) ),
    inference(resolution,[status(thm)],[c_6037,c_6051])).

tff(c_7930,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7924,c_6056])).

tff(c_7942,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7930,c_4506])).

tff(c_6058,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6032,c_88])).

tff(c_6082,plain,(
    ! [C_671,A_672,B_673] :
      ( v1_relat_1(C_671)
      | ~ m1_subset_1(C_671,k1_zfmisc_1(k2_zfmisc_1(A_672,B_673))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6094,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6058,c_6082])).

tff(c_6113,plain,(
    ! [A_677] :
      ( k1_relat_1(A_677) = '#skF_4'
      | k2_relat_1(A_677) != '#skF_4'
      | ~ v1_relat_1(A_677) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6026,c_6026,c_26])).

tff(c_6125,plain,
    ( k1_relat_1('#skF_5') = '#skF_4'
    | k2_relat_1('#skF_5') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_6094,c_6113])).

tff(c_6860,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6125])).

tff(c_7089,plain,(
    ! [C_796,B_797,A_798] :
      ( v5_relat_1(C_796,B_797)
      | ~ m1_subset_1(C_796,k1_zfmisc_1(k2_zfmisc_1(A_798,B_797))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_7101,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_6058,c_7089])).

tff(c_6059,plain,(
    ! [A_668] :
      ( A_668 = '#skF_4'
      | ~ v1_xboole_0(A_668) ) ),
    inference(resolution,[status(thm)],[c_6037,c_6051])).

tff(c_6068,plain,(
    ! [A_5] : '#skF_1'(A_5) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_6059])).

tff(c_6069,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6068,c_14])).

tff(c_6093,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6069,c_6082])).

tff(c_7100,plain,(
    ! [B_797] : v5_relat_1('#skF_4',B_797) ),
    inference(resolution,[status(thm)],[c_6069,c_7089])).

tff(c_6123,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | k2_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_6093,c_6113])).

tff(c_6862,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6123])).

tff(c_6990,plain,(
    ! [C_788,A_789,B_790] :
      ( v1_xboole_0(C_788)
      | ~ m1_subset_1(C_788,k1_zfmisc_1(k2_zfmisc_1(A_789,B_790)))
      | ~ v1_xboole_0(A_789) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7000,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6050,c_6990])).

tff(c_7006,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6037,c_7000])).

tff(c_7012,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7006,c_6056])).

tff(c_6095,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6050,c_6082])).

tff(c_6124,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | k2_relat_1('#skF_6') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_6095,c_6113])).

tff(c_6126,plain,(
    k2_relat_1('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6124])).

tff(c_6696,plain,(
    ! [C_745,B_746,A_747] :
      ( v5_relat_1(C_745,B_746)
      | ~ m1_subset_1(C_745,k1_zfmisc_1(k2_zfmisc_1(A_747,B_746))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6709,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_6050,c_6696])).

tff(c_6707,plain,(
    ! [B_746] : v5_relat_1('#skF_4',B_746) ),
    inference(resolution,[status(thm)],[c_6069,c_6696])).

tff(c_6310,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6123])).

tff(c_6127,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6125])).

tff(c_6044,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6032,c_6032,c_78])).

tff(c_6274,plain,(
    ! [A_703,B_704,C_705] :
      ( k2_relset_1(A_703,B_704,C_705) = k2_relat_1(C_705)
      | ~ m1_subset_1(C_705,k1_zfmisc_1(k2_zfmisc_1(A_703,B_704))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6284,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6058,c_6274])).

tff(c_6288,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6044,c_6284])).

tff(c_6290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6127,c_6288])).

tff(c_6291,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6125])).

tff(c_6292,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6125])).

tff(c_6544,plain,(
    ! [A_739] :
      ( m1_subset_1(A_739,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_739),k2_relat_1(A_739))))
      | ~ v1_funct_1(A_739)
      | ~ v1_relat_1(A_739) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_6562,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6292,c_6544])).

tff(c_6572,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6094,c_92,c_6291,c_6562])).

tff(c_6580,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6572,c_40])).

tff(c_6594,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6037,c_6580])).

tff(c_6620,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6594,c_6056])).

tff(c_6634,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6620,c_6292])).

tff(c_6655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6310,c_6634])).

tff(c_6657,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6123])).

tff(c_6740,plain,(
    ! [B_754,A_755] :
      ( r1_tarski(k2_relat_1(B_754),A_755)
      | ~ v5_relat_1(B_754,A_755)
      | ~ v1_relat_1(B_754) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6745,plain,(
    ! [A_755] :
      ( r1_tarski('#skF_4',A_755)
      | ~ v5_relat_1('#skF_4',A_755)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6657,c_6740])).

tff(c_6780,plain,(
    ! [A_761] : r1_tarski('#skF_4',A_761) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6093,c_6707,c_6745])).

tff(c_6787,plain,(
    ! [A_763] :
      ( A_763 = '#skF_4'
      | ~ r1_tarski(A_763,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6780,c_4])).

tff(c_6805,plain,(
    ! [B_764] :
      ( k2_relat_1(B_764) = '#skF_4'
      | ~ v5_relat_1(B_764,'#skF_4')
      | ~ v1_relat_1(B_764) ) ),
    inference(resolution,[status(thm)],[c_22,c_6787])).

tff(c_6812,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6709,c_6805])).

tff(c_6821,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6095,c_6812])).

tff(c_6823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6126,c_6821])).

tff(c_6825,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6124])).

tff(c_7033,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7012,c_6825])).

tff(c_7051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6862,c_7033])).

tff(c_7053,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6123])).

tff(c_7169,plain,(
    ! [B_805,A_806] :
      ( r1_tarski(k2_relat_1(B_805),A_806)
      | ~ v5_relat_1(B_805,A_806)
      | ~ v1_relat_1(B_805) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7174,plain,(
    ! [A_806] :
      ( r1_tarski('#skF_4',A_806)
      | ~ v5_relat_1('#skF_4',A_806)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7053,c_7169])).

tff(c_7206,plain,(
    ! [A_811] : r1_tarski('#skF_4',A_811) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6093,c_7100,c_7174])).

tff(c_7214,plain,(
    ! [A_813] :
      ( A_813 = '#skF_4'
      | ~ r1_tarski(A_813,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7206,c_4])).

tff(c_7237,plain,(
    ! [B_814] :
      ( k2_relat_1(B_814) = '#skF_4'
      | ~ v5_relat_1(B_814,'#skF_4')
      | ~ v1_relat_1(B_814) ) ),
    inference(resolution,[status(thm)],[c_22,c_7214])).

tff(c_7247,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_7101,c_7237])).

tff(c_7256,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6094,c_7247])).

tff(c_7258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6860,c_7256])).

tff(c_7259,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6125])).

tff(c_7260,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6125])).

tff(c_7984,plain,(
    ! [A_884] :
      ( m1_subset_1(A_884,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_884),k2_relat_1(A_884))))
      | ~ v1_funct_1(A_884)
      | ~ v1_relat_1(A_884) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_8008,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7260,c_7984])).

tff(c_8022,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6094,c_92,c_7259,c_8008])).

tff(c_8030,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8022,c_40])).

tff(c_8044,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6037,c_8030])).

tff(c_8077,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8044,c_6056])).

tff(c_4507,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_8092,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8077,c_4507])).

tff(c_8106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7942,c_8092])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:16:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.06/2.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.52  
% 7.42/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.53  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 7.42/2.53  
% 7.42/2.53  %Foreground sorts:
% 7.42/2.53  
% 7.42/2.53  
% 7.42/2.53  %Background operators:
% 7.42/2.53  
% 7.42/2.53  
% 7.42/2.53  %Foreground operators:
% 7.42/2.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.42/2.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.42/2.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.42/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.42/2.53  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 7.42/2.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.42/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.42/2.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.42/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.42/2.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.42/2.53  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.42/2.53  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.42/2.53  tff('#skF_5', type, '#skF_5': $i).
% 7.42/2.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.42/2.53  tff('#skF_6', type, '#skF_6': $i).
% 7.42/2.53  tff('#skF_2', type, '#skF_2': $i).
% 7.42/2.53  tff('#skF_3', type, '#skF_3': $i).
% 7.42/2.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.42/2.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.42/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.42/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.42/2.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.42/2.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.42/2.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.42/2.53  tff('#skF_4', type, '#skF_4': $i).
% 7.42/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.42/2.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.42/2.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.42/2.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.42/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.42/2.53  
% 7.42/2.57  tff(f_186, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 7.42/2.57  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.42/2.57  tff(f_109, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 7.42/2.57  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 7.42/2.57  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.42/2.57  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.42/2.57  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 7.42/2.57  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 7.42/2.57  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.42/2.57  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 7.42/2.57  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.42/2.57  tff(f_67, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 7.42/2.57  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.42/2.57  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.42/2.57  tff(f_45, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 7.42/2.57  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 7.42/2.57  tff(f_101, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.42/2.57  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.42/2.57  tff(f_159, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 7.42/2.57  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.42/2.57  tff(c_74, plain, (~v2_funct_1('#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.42/2.57  tff(c_96, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 7.42/2.57  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.42/2.57  tff(c_141, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.42/2.57  tff(c_152, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_141])).
% 7.42/2.57  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.42/2.57  tff(c_88, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.42/2.57  tff(c_154, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_141])).
% 7.42/2.57  tff(c_92, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.42/2.57  tff(c_76, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.42/2.57  tff(c_97, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_76])).
% 7.42/2.57  tff(c_84, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.42/2.57  tff(c_476, plain, (![A_105, B_106, C_107, D_108]: (k8_relset_1(A_105, B_106, C_107, D_108)=k10_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.42/2.57  tff(c_490, plain, (![D_108]: (k8_relset_1('#skF_3', '#skF_4', '#skF_6', D_108)=k10_relat_1('#skF_6', D_108))), inference(resolution, [status(thm)], [c_82, c_476])).
% 7.42/2.57  tff(c_649, plain, (![A_129, B_130, C_131]: (k8_relset_1(A_129, B_130, C_131, B_130)=k1_relset_1(A_129, B_130, C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.42/2.57  tff(c_655, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_4')=k1_relset_1('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_82, c_649])).
% 7.42/2.57  tff(c_665, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k10_relat_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_490, c_655])).
% 7.42/2.57  tff(c_781, plain, (![B_139, A_140, C_141]: (k1_xboole_0=B_139 | k1_relset_1(A_140, B_139, C_141)=A_140 | ~v1_funct_2(C_141, A_140, B_139) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.42/2.57  tff(c_790, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_781])).
% 7.42/2.57  tff(c_805, plain, (k1_xboole_0='#skF_4' | k10_relat_1('#skF_6', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_665, c_790])).
% 7.42/2.57  tff(c_806, plain, (k10_relat_1('#skF_6', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_97, c_805])).
% 7.42/2.57  tff(c_884, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_806, c_665])).
% 7.42/2.57  tff(c_292, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.42/2.57  tff(c_307, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_292])).
% 7.42/2.57  tff(c_598, plain, (![A_121, B_122, C_123]: (k7_relset_1(A_121, B_122, C_123, A_121)=k2_relset_1(A_121, B_122, C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.42/2.57  tff(c_604, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_3')=k2_relset_1('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_82, c_598])).
% 7.42/2.57  tff(c_614, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_307, c_604])).
% 7.42/2.57  tff(c_1191, plain, (![B_171, A_172, C_173]: (k8_relset_1(B_171, A_172, C_173, k7_relset_1(B_171, A_172, C_173, B_171))=k1_relset_1(B_171, A_172, C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(B_171, A_172))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.42/2.57  tff(c_1195, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_6', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_3'))=k1_relset_1('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_82, c_1191])).
% 7.42/2.57  tff(c_1203, plain, (k10_relat_1('#skF_6', k2_relat_1('#skF_6'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_884, c_490, c_614, c_1195])).
% 7.42/2.57  tff(c_24, plain, (![A_11]: (k10_relat_1(A_11, k2_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.42/2.57  tff(c_1211, plain, (k1_relat_1('#skF_6')='#skF_3' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1203, c_24])).
% 7.42/2.57  tff(c_1218, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_1211])).
% 7.42/2.57  tff(c_78, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.42/2.57  tff(c_305, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_292])).
% 7.42/2.57  tff(c_310, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_305])).
% 7.42/2.57  tff(c_1347, plain, (![D_181, C_185, F_184, E_180, A_183, B_182]: (k1_partfun1(A_183, B_182, C_185, D_181, E_180, F_184)=k5_relat_1(E_180, F_184) | ~m1_subset_1(F_184, k1_zfmisc_1(k2_zfmisc_1(C_185, D_181))) | ~v1_funct_1(F_184) | ~m1_subset_1(E_180, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))) | ~v1_funct_1(E_180))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.42/2.57  tff(c_1351, plain, (![A_183, B_182, E_180]: (k1_partfun1(A_183, B_182, '#skF_3', '#skF_4', E_180, '#skF_6')=k5_relat_1(E_180, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_180, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))) | ~v1_funct_1(E_180))), inference(resolution, [status(thm)], [c_82, c_1347])).
% 7.42/2.57  tff(c_1717, plain, (![A_203, B_204, E_205]: (k1_partfun1(A_203, B_204, '#skF_3', '#skF_4', E_205, '#skF_6')=k5_relat_1(E_205, '#skF_6') | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))) | ~v1_funct_1(E_205))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1351])).
% 7.42/2.57  tff(c_1733, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_4', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_1717])).
% 7.42/2.57  tff(c_1744, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_4', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1733])).
% 7.42/2.57  tff(c_80, plain, (v2_funct_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.42/2.57  tff(c_1749, plain, (v2_funct_1(k5_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1744, c_80])).
% 7.42/2.57  tff(c_32, plain, (![B_15, A_13]: (v2_funct_1(B_15) | k2_relat_1(B_15)!=k1_relat_1(A_13) | ~v2_funct_1(k5_relat_1(B_15, A_13)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.42/2.57  tff(c_1759, plain, (v2_funct_1('#skF_5') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1749, c_32])).
% 7.42/2.57  tff(c_1765, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_86, c_154, c_92, c_1218, c_310, c_1759])).
% 7.42/2.57  tff(c_1767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_1765])).
% 7.42/2.57  tff(c_1769, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_76])).
% 7.42/2.57  tff(c_1768, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_76])).
% 7.42/2.57  tff(c_1775, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1769, c_1768])).
% 7.42/2.57  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.42/2.57  tff(c_1770, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1768, c_2])).
% 7.42/2.57  tff(c_1780, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1775, c_1770])).
% 7.42/2.57  tff(c_1801, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1775, c_88])).
% 7.42/2.57  tff(c_1825, plain, (![C_212, A_213, B_214]: (v1_relat_1(C_212) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.42/2.57  tff(c_1837, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1801, c_1825])).
% 7.42/2.57  tff(c_26, plain, (![A_12]: (k1_relat_1(A_12)=k1_xboole_0 | k2_relat_1(A_12)!=k1_xboole_0 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.42/2.57  tff(c_1856, plain, (![A_218]: (k1_relat_1(A_218)='#skF_4' | k2_relat_1(A_218)!='#skF_4' | ~v1_relat_1(A_218))), inference(demodulation, [status(thm), theory('equality')], [c_1769, c_1769, c_26])).
% 7.42/2.57  tff(c_1868, plain, (k1_relat_1('#skF_5')='#skF_4' | k2_relat_1('#skF_5')!='#skF_4'), inference(resolution, [status(thm)], [c_1837, c_1856])).
% 7.42/2.57  tff(c_2607, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_1868])).
% 7.42/2.57  tff(c_2973, plain, (![C_348, B_349, A_350]: (v5_relat_1(C_348, B_349) | ~m1_subset_1(C_348, k1_zfmisc_1(k2_zfmisc_1(A_350, B_349))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.42/2.57  tff(c_2985, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1801, c_2973])).
% 7.42/2.57  tff(c_22, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.42/2.57  tff(c_12, plain, (![A_5]: (v1_xboole_0('#skF_1'(A_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.42/2.57  tff(c_1794, plain, (![B_207, A_208]: (~v1_xboole_0(B_207) | B_207=A_208 | ~v1_xboole_0(A_208))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.42/2.57  tff(c_1802, plain, (![A_209]: (A_209='#skF_4' | ~v1_xboole_0(A_209))), inference(resolution, [status(thm)], [c_1780, c_1794])).
% 7.42/2.57  tff(c_1811, plain, (![A_5]: ('#skF_1'(A_5)='#skF_4')), inference(resolution, [status(thm)], [c_12, c_1802])).
% 7.42/2.57  tff(c_14, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.42/2.57  tff(c_1812, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_1811, c_14])).
% 7.42/2.57  tff(c_2984, plain, (![B_349]: (v5_relat_1('#skF_4', B_349))), inference(resolution, [status(thm)], [c_1812, c_2973])).
% 7.42/2.57  tff(c_1836, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1812, c_1825])).
% 7.42/2.57  tff(c_28, plain, (![A_12]: (k2_relat_1(A_12)=k1_xboole_0 | k1_relat_1(A_12)!=k1_xboole_0 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.42/2.57  tff(c_2588, plain, (![A_305]: (k2_relat_1(A_305)='#skF_4' | k1_relat_1(A_305)!='#skF_4' | ~v1_relat_1(A_305))), inference(demodulation, [status(thm), theory('equality')], [c_1769, c_1769, c_28])).
% 7.42/2.57  tff(c_2598, plain, (k2_relat_1('#skF_4')='#skF_4' | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_1836, c_2588])).
% 7.42/2.57  tff(c_2609, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_2598])).
% 7.42/2.57  tff(c_1866, plain, (k1_relat_1('#skF_4')='#skF_4' | k2_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_1836, c_1856])).
% 7.42/2.57  tff(c_2610, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2609, c_1866])).
% 7.42/2.57  tff(c_1793, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1775, c_82])).
% 7.42/2.57  tff(c_2749, plain, (![C_329, A_330, B_331]: (v1_xboole_0(C_329) | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))) | ~v1_xboole_0(A_330))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.42/2.57  tff(c_2759, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1793, c_2749])).
% 7.42/2.57  tff(c_2765, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_2759])).
% 7.42/2.57  tff(c_1799, plain, (![A_208]: (A_208='#skF_4' | ~v1_xboole_0(A_208))), inference(resolution, [status(thm)], [c_1780, c_1794])).
% 7.42/2.57  tff(c_2771, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_2765, c_1799])).
% 7.42/2.57  tff(c_1838, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1793, c_1825])).
% 7.42/2.57  tff(c_1867, plain, (k1_relat_1('#skF_6')='#skF_4' | k2_relat_1('#skF_6')!='#skF_4'), inference(resolution, [status(thm)], [c_1838, c_1856])).
% 7.42/2.57  tff(c_1869, plain, (k2_relat_1('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_1867])).
% 7.42/2.57  tff(c_2036, plain, (![A_247]: (k2_relat_1(A_247)='#skF_4' | k1_relat_1(A_247)!='#skF_4' | ~v1_relat_1(A_247))), inference(demodulation, [status(thm), theory('equality')], [c_1769, c_1769, c_28])).
% 7.42/2.57  tff(c_2047, plain, (k2_relat_1('#skF_6')='#skF_4' | k1_relat_1('#skF_6')!='#skF_4'), inference(resolution, [status(thm)], [c_1838, c_2036])).
% 7.42/2.57  tff(c_2069, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1869, c_2047])).
% 7.42/2.57  tff(c_2433, plain, (![C_289, A_290, B_291]: (v4_relat_1(C_289, A_290) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.42/2.57  tff(c_2446, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1793, c_2433])).
% 7.42/2.57  tff(c_18, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.42/2.57  tff(c_2444, plain, (![A_290]: (v4_relat_1('#skF_4', A_290))), inference(resolution, [status(thm)], [c_1812, c_2433])).
% 7.42/2.57  tff(c_2070, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_1866])).
% 7.42/2.57  tff(c_2046, plain, (k2_relat_1('#skF_4')='#skF_4' | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_1836, c_2036])).
% 7.42/2.57  tff(c_2071, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2070, c_2046])).
% 7.42/2.57  tff(c_1870, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_1868])).
% 7.42/2.57  tff(c_1787, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1775, c_1775, c_78])).
% 7.42/2.57  tff(c_2016, plain, (![A_244, B_245, C_246]: (k2_relset_1(A_244, B_245, C_246)=k2_relat_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.42/2.57  tff(c_2026, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1801, c_2016])).
% 7.42/2.57  tff(c_2030, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_2026])).
% 7.42/2.57  tff(c_2032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1870, c_2030])).
% 7.42/2.57  tff(c_2034, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_1868])).
% 7.42/2.57  tff(c_2033, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_1868])).
% 7.42/2.57  tff(c_2284, plain, (![A_280]: (m1_subset_1(A_280, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_280), k2_relat_1(A_280)))) | ~v1_funct_1(A_280) | ~v1_relat_1(A_280))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.42/2.57  tff(c_2302, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1('#skF_5')))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2033, c_2284])).
% 7.42/2.57  tff(c_2312, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1837, c_92, c_2034, c_2302])).
% 7.42/2.57  tff(c_40, plain, (![C_25, A_22, B_23]: (v1_xboole_0(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.42/2.57  tff(c_2320, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2312, c_40])).
% 7.42/2.57  tff(c_2334, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_2320])).
% 7.42/2.57  tff(c_2346, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_2334, c_1799])).
% 7.42/2.57  tff(c_2374, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2346, c_2033])).
% 7.42/2.57  tff(c_2395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2071, c_2374])).
% 7.42/2.57  tff(c_2396, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_1866])).
% 7.42/2.57  tff(c_2411, plain, (![B_285, A_286]: (r1_tarski(k1_relat_1(B_285), A_286) | ~v4_relat_1(B_285, A_286) | ~v1_relat_1(B_285))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.42/2.57  tff(c_2416, plain, (![A_286]: (r1_tarski('#skF_4', A_286) | ~v4_relat_1('#skF_4', A_286) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2396, c_2411])).
% 7.42/2.57  tff(c_2422, plain, (![A_286]: (r1_tarski('#skF_4', A_286) | ~v4_relat_1('#skF_4', A_286))), inference(demodulation, [status(thm), theory('equality')], [c_1836, c_2416])).
% 7.42/2.57  tff(c_2479, plain, (![A_295]: (r1_tarski('#skF_4', A_295))), inference(demodulation, [status(thm), theory('equality')], [c_2444, c_2422])).
% 7.42/2.57  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.42/2.57  tff(c_2484, plain, (![A_296]: (A_296='#skF_4' | ~r1_tarski(A_296, '#skF_4'))), inference(resolution, [status(thm)], [c_2479, c_4])).
% 7.42/2.57  tff(c_2549, plain, (![B_304]: (k1_relat_1(B_304)='#skF_4' | ~v4_relat_1(B_304, '#skF_4') | ~v1_relat_1(B_304))), inference(resolution, [status(thm)], [c_18, c_2484])).
% 7.42/2.57  tff(c_2560, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2446, c_2549])).
% 7.42/2.57  tff(c_2569, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1838, c_2560])).
% 7.42/2.57  tff(c_2571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2069, c_2569])).
% 7.42/2.57  tff(c_2573, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1867])).
% 7.42/2.57  tff(c_2781, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2771, c_2573])).
% 7.42/2.57  tff(c_2798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2610, c_2781])).
% 7.42/2.57  tff(c_2799, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_2598])).
% 7.42/2.57  tff(c_2837, plain, (![B_336, A_337]: (r1_tarski(k2_relat_1(B_336), A_337) | ~v5_relat_1(B_336, A_337) | ~v1_relat_1(B_336))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.42/2.57  tff(c_2842, plain, (![A_337]: (r1_tarski('#skF_4', A_337) | ~v5_relat_1('#skF_4', A_337) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2799, c_2837])).
% 7.42/2.57  tff(c_2848, plain, (![A_337]: (r1_tarski('#skF_4', A_337) | ~v5_relat_1('#skF_4', A_337))), inference(demodulation, [status(thm), theory('equality')], [c_1836, c_2842])).
% 7.42/2.57  tff(c_2998, plain, (![A_352]: (r1_tarski('#skF_4', A_352))), inference(demodulation, [status(thm), theory('equality')], [c_2984, c_2848])).
% 7.42/2.57  tff(c_3008, plain, (![A_355]: (A_355='#skF_4' | ~r1_tarski(A_355, '#skF_4'))), inference(resolution, [status(thm)], [c_2998, c_4])).
% 7.42/2.57  tff(c_3035, plain, (![B_357]: (k2_relat_1(B_357)='#skF_4' | ~v5_relat_1(B_357, '#skF_4') | ~v1_relat_1(B_357))), inference(resolution, [status(thm)], [c_22, c_3008])).
% 7.42/2.57  tff(c_3046, plain, (k2_relat_1('#skF_5')='#skF_4' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2985, c_3035])).
% 7.42/2.57  tff(c_3055, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1837, c_3046])).
% 7.42/2.57  tff(c_3057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2607, c_3055])).
% 7.42/2.57  tff(c_3058, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_1868])).
% 7.42/2.57  tff(c_3059, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_1868])).
% 7.42/2.57  tff(c_3717, plain, (![A_424]: (m1_subset_1(A_424, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_424), k2_relat_1(A_424)))) | ~v1_funct_1(A_424) | ~v1_relat_1(A_424))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.42/2.57  tff(c_3741, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3059, c_3717])).
% 7.42/2.57  tff(c_3755, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1837, c_92, c_3058, c_3741])).
% 7.42/2.57  tff(c_3763, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_3755, c_40])).
% 7.42/2.57  tff(c_3777, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_3763])).
% 7.42/2.57  tff(c_3789, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3777, c_1799])).
% 7.42/2.57  tff(c_3804, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3789, c_96])).
% 7.42/2.57  tff(c_3610, plain, (![C_414, A_415, B_416]: (v1_xboole_0(C_414) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))) | ~v1_xboole_0(A_415))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.42/2.57  tff(c_3620, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1793, c_3610])).
% 7.42/2.57  tff(c_3626, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_3620])).
% 7.42/2.57  tff(c_3663, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_3626, c_1799])).
% 7.42/2.57  tff(c_3675, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3663, c_86])).
% 7.42/2.57  tff(c_3094, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_2598])).
% 7.42/2.57  tff(c_3095, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3094, c_1866])).
% 7.42/2.57  tff(c_3304, plain, (![C_385, A_386, B_387]: (v1_xboole_0(C_385) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))) | ~v1_xboole_0(A_386))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.42/2.57  tff(c_3314, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1793, c_3304])).
% 7.42/2.57  tff(c_3320, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_3314])).
% 7.42/2.57  tff(c_3326, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_3320, c_1799])).
% 7.42/2.57  tff(c_3336, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3326, c_2573])).
% 7.42/2.57  tff(c_3353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3095, c_3336])).
% 7.42/2.57  tff(c_3355, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_2598])).
% 7.42/2.57  tff(c_3354, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_2598])).
% 7.42/2.57  tff(c_4369, plain, (![E_494, C_499, A_497, D_495, B_496, F_498]: (k1_partfun1(A_497, B_496, C_499, D_495, E_494, F_498)=k5_relat_1(E_494, F_498) | ~m1_subset_1(F_498, k1_zfmisc_1(k2_zfmisc_1(C_499, D_495))) | ~v1_funct_1(F_498) | ~m1_subset_1(E_494, k1_zfmisc_1(k2_zfmisc_1(A_497, B_496))) | ~v1_funct_1(E_494))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.42/2.57  tff(c_4374, plain, (![E_494, C_499, A_497, D_495, B_496]: (k1_partfun1(A_497, B_496, C_499, D_495, E_494, '#skF_4')=k5_relat_1(E_494, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_494, k1_zfmisc_1(k2_zfmisc_1(A_497, B_496))) | ~v1_funct_1(E_494))), inference(resolution, [status(thm)], [c_1812, c_4369])).
% 7.42/2.57  tff(c_4455, plain, (![C_511, E_509, D_510, B_512, A_513]: (k1_partfun1(A_513, B_512, C_511, D_510, E_509, '#skF_4')=k5_relat_1(E_509, '#skF_4') | ~m1_subset_1(E_509, k1_zfmisc_1(k2_zfmisc_1(A_513, B_512))) | ~v1_funct_1(E_509))), inference(demodulation, [status(thm), theory('equality')], [c_3675, c_4374])).
% 7.42/2.57  tff(c_4460, plain, (![A_513, B_512, C_511, D_510]: (k1_partfun1(A_513, B_512, C_511, D_510, '#skF_4', '#skF_4')=k5_relat_1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1812, c_4455])).
% 7.42/2.57  tff(c_4464, plain, (![A_513, B_512, C_511, D_510]: (k1_partfun1(A_513, B_512, C_511, D_510, '#skF_4', '#skF_4')=k5_relat_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3675, c_4460])).
% 7.42/2.57  tff(c_1823, plain, (v2_funct_1(k1_partfun1('#skF_2', '#skF_4', '#skF_4', '#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1775, c_1775, c_80])).
% 7.42/2.57  tff(c_3672, plain, (v2_funct_1(k1_partfun1('#skF_2', '#skF_4', '#skF_4', '#skF_4', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3663, c_1823])).
% 7.42/2.57  tff(c_3793, plain, (v2_funct_1(k1_partfun1('#skF_2', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3789, c_3672])).
% 7.42/2.57  tff(c_4487, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4464, c_3793])).
% 7.42/2.57  tff(c_4497, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4487, c_32])).
% 7.42/2.57  tff(c_4503, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1836, c_3675, c_3355, c_3354, c_4497])).
% 7.42/2.57  tff(c_4505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3804, c_4503])).
% 7.42/2.57  tff(c_4506, plain, (~v2_funct_1('#skF_6')), inference(splitRight, [status(thm)], [c_74])).
% 7.42/2.57  tff(c_4544, plain, (![C_526, A_527, B_528]: (v1_relat_1(C_526) | ~m1_subset_1(C_526, k1_zfmisc_1(k2_zfmisc_1(A_527, B_528))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.42/2.57  tff(c_4555, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_4544])).
% 7.42/2.57  tff(c_4557, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_4544])).
% 7.42/2.57  tff(c_4508, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_76])).
% 7.42/2.57  tff(c_4761, plain, (![A_561, B_562, C_563, D_564]: (k8_relset_1(A_561, B_562, C_563, D_564)=k10_relat_1(C_563, D_564) | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(A_561, B_562))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.42/2.57  tff(c_4772, plain, (![D_564]: (k8_relset_1('#skF_3', '#skF_4', '#skF_6', D_564)=k10_relat_1('#skF_6', D_564))), inference(resolution, [status(thm)], [c_82, c_4761])).
% 7.42/2.57  tff(c_5043, plain, (![A_593, B_594, C_595]: (k8_relset_1(A_593, B_594, C_595, B_594)=k1_relset_1(A_593, B_594, C_595) | ~m1_subset_1(C_595, k1_zfmisc_1(k2_zfmisc_1(A_593, B_594))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.42/2.57  tff(c_5049, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_4')=k1_relset_1('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_82, c_5043])).
% 7.42/2.57  tff(c_5059, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k10_relat_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4772, c_5049])).
% 7.42/2.57  tff(c_5157, plain, (![B_609, A_610, C_611]: (k1_xboole_0=B_609 | k1_relset_1(A_610, B_609, C_611)=A_610 | ~v1_funct_2(C_611, A_610, B_609) | ~m1_subset_1(C_611, k1_zfmisc_1(k2_zfmisc_1(A_610, B_609))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.42/2.57  tff(c_5166, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_5157])).
% 7.42/2.57  tff(c_5181, plain, (k1_xboole_0='#skF_4' | k10_relat_1('#skF_6', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5059, c_5166])).
% 7.42/2.57  tff(c_5182, plain, (k10_relat_1('#skF_6', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4508, c_5181])).
% 7.42/2.57  tff(c_5260, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5182, c_5059])).
% 7.42/2.57  tff(c_4707, plain, (![A_558, B_559, C_560]: (k2_relset_1(A_558, B_559, C_560)=k2_relat_1(C_560) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(A_558, B_559))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.42/2.57  tff(c_4722, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_4707])).
% 7.42/2.57  tff(c_4949, plain, (![A_582, B_583, C_584]: (k7_relset_1(A_582, B_583, C_584, A_582)=k2_relset_1(A_582, B_583, C_584) | ~m1_subset_1(C_584, k1_zfmisc_1(k2_zfmisc_1(A_582, B_583))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.42/2.57  tff(c_4955, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_3')=k2_relset_1('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_82, c_4949])).
% 7.42/2.57  tff(c_4965, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4722, c_4955])).
% 7.42/2.57  tff(c_5504, plain, (![B_629, A_630, C_631]: (k8_relset_1(B_629, A_630, C_631, k7_relset_1(B_629, A_630, C_631, B_629))=k1_relset_1(B_629, A_630, C_631) | ~m1_subset_1(C_631, k1_zfmisc_1(k2_zfmisc_1(B_629, A_630))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.42/2.57  tff(c_5508, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_6', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_3'))=k1_relset_1('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_82, c_5504])).
% 7.42/2.57  tff(c_5516, plain, (k10_relat_1('#skF_6', k2_relat_1('#skF_6'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5260, c_4772, c_4965, c_5508])).
% 7.42/2.57  tff(c_5528, plain, (k1_relat_1('#skF_6')='#skF_3' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5516, c_24])).
% 7.42/2.57  tff(c_5535, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4555, c_5528])).
% 7.42/2.57  tff(c_4720, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_4707])).
% 7.42/2.57  tff(c_4725, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4720])).
% 7.42/2.57  tff(c_5776, plain, (![F_649, A_648, E_645, C_650, B_647, D_646]: (k1_partfun1(A_648, B_647, C_650, D_646, E_645, F_649)=k5_relat_1(E_645, F_649) | ~m1_subset_1(F_649, k1_zfmisc_1(k2_zfmisc_1(C_650, D_646))) | ~v1_funct_1(F_649) | ~m1_subset_1(E_645, k1_zfmisc_1(k2_zfmisc_1(A_648, B_647))) | ~v1_funct_1(E_645))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.42/2.57  tff(c_5782, plain, (![A_648, B_647, E_645]: (k1_partfun1(A_648, B_647, '#skF_3', '#skF_4', E_645, '#skF_6')=k5_relat_1(E_645, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_645, k1_zfmisc_1(k2_zfmisc_1(A_648, B_647))) | ~v1_funct_1(E_645))), inference(resolution, [status(thm)], [c_82, c_5776])).
% 7.42/2.57  tff(c_5974, plain, (![A_662, B_663, E_664]: (k1_partfun1(A_662, B_663, '#skF_3', '#skF_4', E_664, '#skF_6')=k5_relat_1(E_664, '#skF_6') | ~m1_subset_1(E_664, k1_zfmisc_1(k2_zfmisc_1(A_662, B_663))) | ~v1_funct_1(E_664))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_5782])).
% 7.42/2.57  tff(c_5990, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_4', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_5974])).
% 7.42/2.57  tff(c_6001, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_4', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_5990])).
% 7.42/2.57  tff(c_6006, plain, (v2_funct_1(k5_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6001, c_80])).
% 7.42/2.57  tff(c_30, plain, (![A_13, B_15]: (v2_funct_1(A_13) | k2_relat_1(B_15)!=k1_relat_1(A_13) | ~v2_funct_1(k5_relat_1(B_15, A_13)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.42/2.57  tff(c_6016, plain, (v2_funct_1('#skF_6') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6006, c_30])).
% 7.42/2.57  tff(c_6022, plain, (v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4555, c_86, c_4557, c_92, c_5535, c_4725, c_6016])).
% 7.42/2.57  tff(c_6024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4506, c_6022])).
% 7.42/2.57  tff(c_6026, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_76])).
% 7.42/2.57  tff(c_6025, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_76])).
% 7.42/2.57  tff(c_6032, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6026, c_6025])).
% 7.42/2.57  tff(c_6027, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6025, c_2])).
% 7.42/2.57  tff(c_6037, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6032, c_6027])).
% 7.42/2.57  tff(c_6050, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6032, c_82])).
% 7.42/2.57  tff(c_7908, plain, (![C_875, A_876, B_877]: (v1_xboole_0(C_875) | ~m1_subset_1(C_875, k1_zfmisc_1(k2_zfmisc_1(A_876, B_877))) | ~v1_xboole_0(A_876))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.42/2.57  tff(c_7918, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_6050, c_7908])).
% 7.42/2.57  tff(c_7924, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6037, c_7918])).
% 7.42/2.57  tff(c_6051, plain, (![B_666, A_667]: (~v1_xboole_0(B_666) | B_666=A_667 | ~v1_xboole_0(A_667))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.42/2.57  tff(c_6056, plain, (![A_667]: (A_667='#skF_4' | ~v1_xboole_0(A_667))), inference(resolution, [status(thm)], [c_6037, c_6051])).
% 7.42/2.57  tff(c_7930, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_7924, c_6056])).
% 7.42/2.57  tff(c_7942, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7930, c_4506])).
% 7.42/2.57  tff(c_6058, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6032, c_88])).
% 7.42/2.57  tff(c_6082, plain, (![C_671, A_672, B_673]: (v1_relat_1(C_671) | ~m1_subset_1(C_671, k1_zfmisc_1(k2_zfmisc_1(A_672, B_673))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.42/2.57  tff(c_6094, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6058, c_6082])).
% 7.42/2.57  tff(c_6113, plain, (![A_677]: (k1_relat_1(A_677)='#skF_4' | k2_relat_1(A_677)!='#skF_4' | ~v1_relat_1(A_677))), inference(demodulation, [status(thm), theory('equality')], [c_6026, c_6026, c_26])).
% 7.42/2.57  tff(c_6125, plain, (k1_relat_1('#skF_5')='#skF_4' | k2_relat_1('#skF_5')!='#skF_4'), inference(resolution, [status(thm)], [c_6094, c_6113])).
% 7.42/2.57  tff(c_6860, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_6125])).
% 7.42/2.57  tff(c_7089, plain, (![C_796, B_797, A_798]: (v5_relat_1(C_796, B_797) | ~m1_subset_1(C_796, k1_zfmisc_1(k2_zfmisc_1(A_798, B_797))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.42/2.57  tff(c_7101, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_6058, c_7089])).
% 7.42/2.57  tff(c_6059, plain, (![A_668]: (A_668='#skF_4' | ~v1_xboole_0(A_668))), inference(resolution, [status(thm)], [c_6037, c_6051])).
% 7.42/2.57  tff(c_6068, plain, (![A_5]: ('#skF_1'(A_5)='#skF_4')), inference(resolution, [status(thm)], [c_12, c_6059])).
% 7.42/2.57  tff(c_6069, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_6068, c_14])).
% 7.42/2.57  tff(c_6093, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6069, c_6082])).
% 7.42/2.57  tff(c_7100, plain, (![B_797]: (v5_relat_1('#skF_4', B_797))), inference(resolution, [status(thm)], [c_6069, c_7089])).
% 7.42/2.57  tff(c_6123, plain, (k1_relat_1('#skF_4')='#skF_4' | k2_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_6093, c_6113])).
% 7.42/2.57  tff(c_6862, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_6123])).
% 7.42/2.57  tff(c_6990, plain, (![C_788, A_789, B_790]: (v1_xboole_0(C_788) | ~m1_subset_1(C_788, k1_zfmisc_1(k2_zfmisc_1(A_789, B_790))) | ~v1_xboole_0(A_789))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.42/2.57  tff(c_7000, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_6050, c_6990])).
% 7.42/2.57  tff(c_7006, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6037, c_7000])).
% 7.42/2.57  tff(c_7012, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_7006, c_6056])).
% 7.42/2.57  tff(c_6095, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6050, c_6082])).
% 7.42/2.57  tff(c_6124, plain, (k1_relat_1('#skF_6')='#skF_4' | k2_relat_1('#skF_6')!='#skF_4'), inference(resolution, [status(thm)], [c_6095, c_6113])).
% 7.42/2.57  tff(c_6126, plain, (k2_relat_1('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_6124])).
% 7.42/2.57  tff(c_6696, plain, (![C_745, B_746, A_747]: (v5_relat_1(C_745, B_746) | ~m1_subset_1(C_745, k1_zfmisc_1(k2_zfmisc_1(A_747, B_746))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.42/2.57  tff(c_6709, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_6050, c_6696])).
% 7.42/2.57  tff(c_6707, plain, (![B_746]: (v5_relat_1('#skF_4', B_746))), inference(resolution, [status(thm)], [c_6069, c_6696])).
% 7.42/2.57  tff(c_6310, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_6123])).
% 7.42/2.57  tff(c_6127, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_6125])).
% 7.42/2.57  tff(c_6044, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6032, c_6032, c_78])).
% 7.42/2.57  tff(c_6274, plain, (![A_703, B_704, C_705]: (k2_relset_1(A_703, B_704, C_705)=k2_relat_1(C_705) | ~m1_subset_1(C_705, k1_zfmisc_1(k2_zfmisc_1(A_703, B_704))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.42/2.57  tff(c_6284, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6058, c_6274])).
% 7.42/2.57  tff(c_6288, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6044, c_6284])).
% 7.42/2.57  tff(c_6290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6127, c_6288])).
% 7.42/2.57  tff(c_6291, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_6125])).
% 7.42/2.57  tff(c_6292, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_6125])).
% 7.42/2.57  tff(c_6544, plain, (![A_739]: (m1_subset_1(A_739, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_739), k2_relat_1(A_739)))) | ~v1_funct_1(A_739) | ~v1_relat_1(A_739))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.42/2.57  tff(c_6562, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6292, c_6544])).
% 7.42/2.57  tff(c_6572, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6094, c_92, c_6291, c_6562])).
% 7.42/2.57  tff(c_6580, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_6572, c_40])).
% 7.42/2.57  tff(c_6594, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6037, c_6580])).
% 7.42/2.57  tff(c_6620, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_6594, c_6056])).
% 7.42/2.57  tff(c_6634, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6620, c_6292])).
% 7.42/2.57  tff(c_6655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6310, c_6634])).
% 7.42/2.57  tff(c_6657, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_6123])).
% 7.42/2.57  tff(c_6740, plain, (![B_754, A_755]: (r1_tarski(k2_relat_1(B_754), A_755) | ~v5_relat_1(B_754, A_755) | ~v1_relat_1(B_754))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.42/2.57  tff(c_6745, plain, (![A_755]: (r1_tarski('#skF_4', A_755) | ~v5_relat_1('#skF_4', A_755) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6657, c_6740])).
% 7.42/2.57  tff(c_6780, plain, (![A_761]: (r1_tarski('#skF_4', A_761))), inference(demodulation, [status(thm), theory('equality')], [c_6093, c_6707, c_6745])).
% 7.42/2.57  tff(c_6787, plain, (![A_763]: (A_763='#skF_4' | ~r1_tarski(A_763, '#skF_4'))), inference(resolution, [status(thm)], [c_6780, c_4])).
% 7.42/2.57  tff(c_6805, plain, (![B_764]: (k2_relat_1(B_764)='#skF_4' | ~v5_relat_1(B_764, '#skF_4') | ~v1_relat_1(B_764))), inference(resolution, [status(thm)], [c_22, c_6787])).
% 7.42/2.57  tff(c_6812, plain, (k2_relat_1('#skF_6')='#skF_4' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6709, c_6805])).
% 7.42/2.57  tff(c_6821, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6095, c_6812])).
% 7.42/2.57  tff(c_6823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6126, c_6821])).
% 7.42/2.57  tff(c_6825, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_6124])).
% 7.42/2.57  tff(c_7033, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7012, c_6825])).
% 7.42/2.57  tff(c_7051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6862, c_7033])).
% 7.42/2.57  tff(c_7053, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_6123])).
% 7.42/2.57  tff(c_7169, plain, (![B_805, A_806]: (r1_tarski(k2_relat_1(B_805), A_806) | ~v5_relat_1(B_805, A_806) | ~v1_relat_1(B_805))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.42/2.57  tff(c_7174, plain, (![A_806]: (r1_tarski('#skF_4', A_806) | ~v5_relat_1('#skF_4', A_806) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7053, c_7169])).
% 7.42/2.57  tff(c_7206, plain, (![A_811]: (r1_tarski('#skF_4', A_811))), inference(demodulation, [status(thm), theory('equality')], [c_6093, c_7100, c_7174])).
% 7.42/2.57  tff(c_7214, plain, (![A_813]: (A_813='#skF_4' | ~r1_tarski(A_813, '#skF_4'))), inference(resolution, [status(thm)], [c_7206, c_4])).
% 7.42/2.57  tff(c_7237, plain, (![B_814]: (k2_relat_1(B_814)='#skF_4' | ~v5_relat_1(B_814, '#skF_4') | ~v1_relat_1(B_814))), inference(resolution, [status(thm)], [c_22, c_7214])).
% 7.42/2.57  tff(c_7247, plain, (k2_relat_1('#skF_5')='#skF_4' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_7101, c_7237])).
% 7.42/2.57  tff(c_7256, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6094, c_7247])).
% 7.42/2.57  tff(c_7258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6860, c_7256])).
% 7.42/2.57  tff(c_7259, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_6125])).
% 7.42/2.57  tff(c_7260, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_6125])).
% 7.42/2.57  tff(c_7984, plain, (![A_884]: (m1_subset_1(A_884, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_884), k2_relat_1(A_884)))) | ~v1_funct_1(A_884) | ~v1_relat_1(A_884))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.42/2.57  tff(c_8008, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7260, c_7984])).
% 7.42/2.57  tff(c_8022, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6094, c_92, c_7259, c_8008])).
% 7.42/2.57  tff(c_8030, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_8022, c_40])).
% 7.42/2.57  tff(c_8044, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6037, c_8030])).
% 7.42/2.57  tff(c_8077, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_8044, c_6056])).
% 7.42/2.57  tff(c_4507, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 7.42/2.57  tff(c_8092, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8077, c_4507])).
% 7.42/2.57  tff(c_8106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7942, c_8092])).
% 7.42/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.57  
% 7.42/2.57  Inference rules
% 7.42/2.57  ----------------------
% 7.42/2.57  #Ref     : 0
% 7.42/2.57  #Sup     : 1547
% 7.42/2.57  #Fact    : 0
% 7.42/2.57  #Define  : 0
% 7.42/2.57  #Split   : 49
% 7.42/2.57  #Chain   : 0
% 7.42/2.57  #Close   : 0
% 7.42/2.57  
% 7.42/2.57  Ordering : KBO
% 7.42/2.57  
% 7.42/2.57  Simplification rules
% 7.42/2.57  ----------------------
% 7.42/2.57  #Subsume      : 126
% 7.42/2.57  #Demod        : 2019
% 7.42/2.57  #Tautology    : 981
% 7.42/2.57  #SimpNegUnit  : 61
% 7.42/2.57  #BackRed      : 298
% 7.42/2.57  
% 7.42/2.57  #Partial instantiations: 0
% 7.42/2.57  #Strategies tried      : 1
% 7.42/2.57  
% 7.42/2.57  Timing (in seconds)
% 7.42/2.57  ----------------------
% 7.42/2.58  Preprocessing        : 0.40
% 7.42/2.58  Parsing              : 0.22
% 7.42/2.58  CNF conversion       : 0.03
% 7.42/2.58  Main loop            : 1.24
% 7.42/2.58  Inferencing          : 0.43
% 7.42/2.58  Reduction            : 0.45
% 7.42/2.58  Demodulation         : 0.31
% 7.42/2.58  BG Simplification    : 0.05
% 7.42/2.58  Subsumption          : 0.19
% 7.42/2.58  Abstraction          : 0.05
% 7.42/2.58  MUC search           : 0.00
% 7.42/2.58  Cooper               : 0.00
% 7.42/2.58  Total                : 1.79
% 7.42/2.58  Index Insertion      : 0.00
% 7.42/2.58  Index Deletion       : 0.00
% 7.42/2.58  Index Matching       : 0.00
% 7.42/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
