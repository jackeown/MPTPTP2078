%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:13 EST 2020

% Result     : Theorem 7.60s
% Output     : CNFRefutation 8.15s
% Verified   : 
% Statistics : Number of formulae       :  186 (1098 expanded)
%              Number of leaves         :   31 ( 369 expanded)
%              Depth                    :   16
%              Number of atoms          :  404 (3405 expanded)
%              Number of equality atoms :  100 ( 808 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_91,axiom,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_59,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_59])).

tff(c_196,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_200,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_196])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [B_36,A_37] :
      ( v5_relat_1(B_36,A_37)
      | ~ r1_tarski(k2_relat_1(B_36),A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_109,plain,(
    ! [B_36] :
      ( v5_relat_1(B_36,k2_relat_1(B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_112,plain,(
    ! [C_40,B_41,A_42] :
      ( v5_relat_1(C_40,B_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_42,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_116,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_112])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_117,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6177,plain,(
    ! [A_465,A_466,B_467] :
      ( r1_tarski(A_465,A_466)
      | ~ r1_tarski(A_465,k2_relat_1(B_467))
      | ~ v5_relat_1(B_467,A_466)
      | ~ v1_relat_1(B_467) ) ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_6454,plain,(
    ! [B_499,A_500,B_501] :
      ( r1_tarski(k2_relat_1(B_499),A_500)
      | ~ v5_relat_1(B_501,A_500)
      | ~ v1_relat_1(B_501)
      | ~ v5_relat_1(B_499,k2_relat_1(B_501))
      | ~ v1_relat_1(B_499) ) ),
    inference(resolution,[status(thm)],[c_18,c_6177])).

tff(c_6458,plain,(
    ! [B_499] :
      ( r1_tarski(k2_relat_1(B_499),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v5_relat_1(B_499,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_499) ) ),
    inference(resolution,[status(thm)],[c_116,c_6454])).

tff(c_6468,plain,(
    ! [B_502] :
      ( r1_tarski(k2_relat_1(B_502),'#skF_2')
      | ~ v5_relat_1(B_502,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_502) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_6458])).

tff(c_6472,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_109,c_6468])).

tff(c_6475,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_6472])).

tff(c_46,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_129,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,'#skF_3')
      | ~ r1_tarski(A_43,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_117])).

tff(c_6486,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6475,c_129])).

tff(c_6538,plain,(
    ! [C_504,A_505,B_506] :
      ( m1_subset_1(C_504,k1_zfmisc_1(k2_zfmisc_1(A_505,B_506)))
      | ~ r1_tarski(k2_relat_1(C_504),B_506)
      | ~ r1_tarski(k1_relat_1(C_504),A_505)
      | ~ v1_relat_1(C_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_145,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,'#skF_3')
      | ~ r1_tarski(A_48,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_117])).

tff(c_158,plain,(
    ! [B_10] :
      ( r1_tarski(k2_relat_1(B_10),'#skF_3')
      | ~ v5_relat_1(B_10,'#skF_2')
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_145])).

tff(c_28,plain,(
    ! [C_22,A_20,B_21] :
      ( m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ r1_tarski(k2_relat_1(C_22),B_21)
      | ~ r1_tarski(k1_relat_1(C_22),A_20)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2039,plain,(
    ! [B_203,C_204,A_205] :
      ( k1_xboole_0 = B_203
      | v1_funct_2(C_204,A_205,B_203)
      | k1_relset_1(A_205,B_203,C_204) != A_205
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_205,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3402,plain,(
    ! [B_275,C_276,A_277] :
      ( k1_xboole_0 = B_275
      | v1_funct_2(C_276,A_277,B_275)
      | k1_relset_1(A_277,B_275,C_276) != A_277
      | ~ r1_tarski(k2_relat_1(C_276),B_275)
      | ~ r1_tarski(k1_relat_1(C_276),A_277)
      | ~ v1_relat_1(C_276) ) ),
    inference(resolution,[status(thm)],[c_28,c_2039])).

tff(c_3429,plain,(
    ! [B_10,A_277] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(B_10,A_277,'#skF_3')
      | k1_relset_1(A_277,'#skF_3',B_10) != A_277
      | ~ r1_tarski(k1_relat_1(B_10),A_277)
      | ~ v5_relat_1(B_10,'#skF_2')
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_158,c_3402])).

tff(c_3495,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3429])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_286,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_290,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_286])).

tff(c_832,plain,(
    ! [B_140,A_141,C_142] :
      ( k1_xboole_0 = B_140
      | k1_relset_1(A_141,B_140,C_142) = A_141
      | ~ v1_funct_2(C_142,A_141,B_140)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_838,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_832])).

tff(c_842,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_290,c_838])).

tff(c_843,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_842])).

tff(c_613,plain,(
    ! [C_118,A_119,B_120] :
      ( m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ r1_tarski(k2_relat_1(C_118),B_120)
      | ~ r1_tarski(k1_relat_1(C_118),A_119)
      | ~ v1_relat_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_relset_1(A_17,B_18,C_19) = k1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1006,plain,(
    ! [A_145,B_146,C_147] :
      ( k1_relset_1(A_145,B_146,C_147) = k1_relat_1(C_147)
      | ~ r1_tarski(k2_relat_1(C_147),B_146)
      | ~ r1_tarski(k1_relat_1(C_147),A_145)
      | ~ v1_relat_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_613,c_26])).

tff(c_1030,plain,(
    ! [A_148,B_149] :
      ( k1_relset_1(A_148,'#skF_3',B_149) = k1_relat_1(B_149)
      | ~ r1_tarski(k1_relat_1(B_149),A_148)
      | ~ v5_relat_1(B_149,'#skF_2')
      | ~ v1_relat_1(B_149) ) ),
    inference(resolution,[status(thm)],[c_158,c_1006])).

tff(c_1033,plain,(
    ! [A_148] :
      ( k1_relset_1(A_148,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_148)
      | ~ v5_relat_1('#skF_4','#skF_2')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_1030])).

tff(c_1076,plain,(
    ! [A_151] :
      ( k1_relset_1(A_151,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_116,c_843,c_1033])).

tff(c_1081,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_1076])).

tff(c_354,plain,(
    ! [A_82,A_83,B_84] :
      ( r1_tarski(A_82,A_83)
      | ~ r1_tarski(A_82,k2_relat_1(B_84))
      | ~ v5_relat_1(B_84,A_83)
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_650,plain,(
    ! [B_121,A_122,B_123] :
      ( r1_tarski(k2_relat_1(B_121),A_122)
      | ~ v5_relat_1(B_123,A_122)
      | ~ v1_relat_1(B_123)
      | ~ v5_relat_1(B_121,k2_relat_1(B_123))
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_18,c_354])).

tff(c_654,plain,(
    ! [B_121] :
      ( r1_tarski(k2_relat_1(B_121),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v5_relat_1(B_121,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_116,c_650])).

tff(c_664,plain,(
    ! [B_124] :
      ( r1_tarski(k2_relat_1(B_124),'#skF_2')
      | ~ v5_relat_1(B_124,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_654])).

tff(c_668,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_109,c_664])).

tff(c_671,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_668])).

tff(c_682,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_671,c_129])).

tff(c_768,plain,(
    ! [B_127,C_128,A_129] :
      ( k1_xboole_0 = B_127
      | v1_funct_2(C_128,A_129,B_127)
      | k1_relset_1(A_129,B_127,C_128) != A_129
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1923,plain,(
    ! [B_198,C_199,A_200] :
      ( k1_xboole_0 = B_198
      | v1_funct_2(C_199,A_200,B_198)
      | k1_relset_1(A_200,B_198,C_199) != A_200
      | ~ r1_tarski(k2_relat_1(C_199),B_198)
      | ~ r1_tarski(k1_relat_1(C_199),A_200)
      | ~ v1_relat_1(C_199) ) ),
    inference(resolution,[status(thm)],[c_28,c_768])).

tff(c_1929,plain,(
    ! [A_200] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_200,'#skF_3')
      | k1_relset_1(A_200,'#skF_3','#skF_4') != A_200
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_200)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_682,c_1923])).

tff(c_1945,plain,(
    ! [A_200] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_200,'#skF_3')
      | k1_relset_1(A_200,'#skF_3','#skF_4') != A_200
      | ~ r1_tarski('#skF_1',A_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_843,c_1929])).

tff(c_1961,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1945])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1996,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1961,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_699,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_682,c_2])).

tff(c_767,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_699])).

tff(c_2009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1996,c_767])).

tff(c_2012,plain,(
    ! [A_202] :
      ( v1_funct_2('#skF_4',A_202,'#skF_3')
      | k1_relset_1(A_202,'#skF_3','#skF_4') != A_202
      | ~ r1_tarski('#skF_1',A_202) ) ),
    inference(splitRight,[status(thm)],[c_1945])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_42])).

tff(c_201,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_2017,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2012,c_201])).

tff(c_2025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1081,c_2017])).

tff(c_2026,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_699])).

tff(c_687,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_671,c_2])).

tff(c_733,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_687])).

tff(c_2029,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2026,c_733])).

tff(c_2036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2029])).

tff(c_2037,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( v5_relat_1(B_10,A_9)
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2084,plain,(
    ! [A_9] :
      ( v5_relat_1('#skF_4',A_9)
      | ~ r1_tarski('#skF_2',A_9)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2037,c_16])).

tff(c_2116,plain,(
    ! [A_206] :
      ( v5_relat_1('#skF_4',A_206)
      | ~ r1_tarski('#skF_2',A_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_2084])).

tff(c_91,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(k2_relat_1(B_34),A_35)
      | ~ v5_relat_1(B_34,A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_64])).

tff(c_98,plain,(
    ! [B_34] :
      ( k2_relat_1(B_34) = k1_xboole_0
      | ~ v5_relat_1(B_34,k1_xboole_0)
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_91,c_75])).

tff(c_2139,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2116,c_98])).

tff(c_2158,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_2037,c_2139])).

tff(c_2159,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2158])).

tff(c_3507,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3495,c_2159])).

tff(c_3533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3507])).

tff(c_3535,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3429])).

tff(c_2182,plain,(
    ! [B_208,A_209,C_210] :
      ( k1_xboole_0 = B_208
      | k1_relset_1(A_209,B_208,C_210) = A_209
      | ~ v1_funct_2(C_210,A_209,B_208)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_209,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2188,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2182])).

tff(c_2192,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_290,c_2188])).

tff(c_2193,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2192])).

tff(c_2331,plain,(
    ! [A_213,B_214,C_215] :
      ( k1_relset_1(A_213,B_214,C_215) = k1_relat_1(C_215)
      | ~ r1_tarski(k2_relat_1(C_215),B_214)
      | ~ r1_tarski(k1_relat_1(C_215),A_213)
      | ~ v1_relat_1(C_215) ) ),
    inference(resolution,[status(thm)],[c_613,c_26])).

tff(c_2353,plain,(
    ! [A_216,B_217] :
      ( k1_relset_1(A_216,'#skF_3',B_217) = k1_relat_1(B_217)
      | ~ r1_tarski(k1_relat_1(B_217),A_216)
      | ~ v5_relat_1(B_217,'#skF_2')
      | ~ v1_relat_1(B_217) ) ),
    inference(resolution,[status(thm)],[c_158,c_2331])).

tff(c_2356,plain,(
    ! [A_216] :
      ( k1_relset_1(A_216,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_216)
      | ~ v5_relat_1('#skF_4','#skF_2')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2193,c_2353])).

tff(c_2397,plain,(
    ! [A_219] :
      ( k1_relset_1(A_219,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_116,c_2193,c_2356])).

tff(c_2402,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_2397])).

tff(c_3412,plain,(
    ! [B_275,A_277] :
      ( k1_xboole_0 = B_275
      | v1_funct_2('#skF_4',A_277,B_275)
      | k1_relset_1(A_277,B_275,'#skF_4') != A_277
      | ~ r1_tarski('#skF_2',B_275)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_277)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2037,c_3402])).

tff(c_5992,plain,(
    ! [B_443,A_444] :
      ( k1_xboole_0 = B_443
      | v1_funct_2('#skF_4',A_444,B_443)
      | k1_relset_1(A_444,B_443,'#skF_4') != A_444
      | ~ r1_tarski('#skF_2',B_443)
      | ~ r1_tarski('#skF_1',A_444) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_2193,c_3412])).

tff(c_6024,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_5992,c_201])).

tff(c_6053,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_46,c_2402,c_6024])).

tff(c_6055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3535,c_6053])).

tff(c_6056,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6560,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6538,c_6056])).

tff(c_6577,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_6486,c_6560])).

tff(c_6586,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_6577])).

tff(c_6593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_200,c_6586])).

tff(c_6594,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6595,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6601,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6594,c_6595])).

tff(c_6608,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6601,c_48])).

tff(c_6611,plain,(
    ! [C_508,A_509,B_510] :
      ( v1_relat_1(C_508)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(A_509,B_510))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6615,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6608,c_6611])).

tff(c_6596,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6594,c_10])).

tff(c_8018,plain,(
    ! [C_697,A_698,B_699] :
      ( v4_relat_1(C_697,A_698)
      | ~ m1_subset_1(C_697,k1_zfmisc_1(k2_zfmisc_1(A_698,B_699))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8022,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_6608,c_8018])).

tff(c_7997,plain,(
    ! [B_694,A_695] :
      ( r1_tarski(k1_relat_1(B_694),A_695)
      | ~ v4_relat_1(B_694,A_695)
      | ~ v1_relat_1(B_694) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6616,plain,(
    ! [B_511,A_512] :
      ( B_511 = A_512
      | ~ r1_tarski(B_511,A_512)
      | ~ r1_tarski(A_512,B_511) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6621,plain,(
    ! [A_6] :
      ( A_6 = '#skF_1'
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6596,c_6616])).

tff(c_8015,plain,(
    ! [B_694] :
      ( k1_relat_1(B_694) = '#skF_1'
      | ~ v4_relat_1(B_694,'#skF_1')
      | ~ v1_relat_1(B_694) ) ),
    inference(resolution,[status(thm)],[c_7997,c_6621])).

tff(c_8025,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8022,c_8015])).

tff(c_8028,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6615,c_8025])).

tff(c_6639,plain,(
    ! [C_514,B_515,A_516] :
      ( v5_relat_1(C_514,B_515)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(A_516,B_515))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6643,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_6608,c_6639])).

tff(c_7947,plain,(
    ! [B_686,A_687] :
      ( r1_tarski(k2_relat_1(B_686),A_687)
      | ~ v5_relat_1(B_686,A_687)
      | ~ v1_relat_1(B_686) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7981,plain,(
    ! [B_693] :
      ( k2_relat_1(B_693) = '#skF_1'
      | ~ v5_relat_1(B_693,'#skF_1')
      | ~ v1_relat_1(B_693) ) ),
    inference(resolution,[status(thm)],[c_7947,c_6621])).

tff(c_7984,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6643,c_7981])).

tff(c_7987,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6615,c_7984])).

tff(c_8486,plain,(
    ! [C_752,A_753,B_754] :
      ( m1_subset_1(C_752,k1_zfmisc_1(k2_zfmisc_1(A_753,B_754)))
      | ~ r1_tarski(k2_relat_1(C_752),B_754)
      | ~ r1_tarski(k1_relat_1(C_752),A_753)
      | ~ v1_relat_1(C_752) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6680,plain,(
    ! [C_523,A_524,B_525] :
      ( v4_relat_1(C_523,A_524)
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(A_524,B_525))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6684,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_6608,c_6680])).

tff(c_6737,plain,(
    ! [B_535,A_536] :
      ( r1_tarski(k1_relat_1(B_535),A_536)
      | ~ v4_relat_1(B_535,A_536)
      | ~ v1_relat_1(B_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6757,plain,(
    ! [B_537] :
      ( k1_relat_1(B_537) = '#skF_1'
      | ~ v4_relat_1(B_537,'#skF_1')
      | ~ v1_relat_1(B_537) ) ),
    inference(resolution,[status(thm)],[c_6737,c_6621])).

tff(c_6760,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6684,c_6757])).

tff(c_6763,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6615,c_6760])).

tff(c_6645,plain,(
    ! [B_517,A_518] :
      ( r1_tarski(k2_relat_1(B_517),A_518)
      | ~ v5_relat_1(B_517,A_518)
      | ~ v1_relat_1(B_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6654,plain,(
    ! [B_519] :
      ( k2_relat_1(B_519) = '#skF_1'
      | ~ v5_relat_1(B_519,'#skF_1')
      | ~ v1_relat_1(B_519) ) ),
    inference(resolution,[status(thm)],[c_6645,c_6621])).

tff(c_6657,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6643,c_6654])).

tff(c_6660,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6615,c_6657])).

tff(c_7182,plain,(
    ! [C_583,A_584,B_585] :
      ( m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(A_584,B_585)))
      | ~ r1_tarski(k2_relat_1(C_583),B_585)
      | ~ r1_tarski(k1_relat_1(C_583),A_584)
      | ~ v1_relat_1(C_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7357,plain,(
    ! [A_615,B_616,C_617] :
      ( k1_relset_1(A_615,B_616,C_617) = k1_relat_1(C_617)
      | ~ r1_tarski(k2_relat_1(C_617),B_616)
      | ~ r1_tarski(k1_relat_1(C_617),A_615)
      | ~ v1_relat_1(C_617) ) ),
    inference(resolution,[status(thm)],[c_7182,c_26])).

tff(c_7361,plain,(
    ! [A_615,B_616] :
      ( k1_relset_1(A_615,B_616,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',B_616)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_615)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6660,c_7357])).

tff(c_7369,plain,(
    ! [A_615,B_616] : k1_relset_1(A_615,B_616,'#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6615,c_6596,c_6763,c_6596,c_6763,c_7361])).

tff(c_34,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7011,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,'#skF_1',B_24)
      | k1_relset_1('#skF_1',B_24,C_25) != '#skF_1'
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_24))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6594,c_6594,c_6594,c_6594,c_34])).

tff(c_7915,plain,(
    ! [C_681,B_682] :
      ( v1_funct_2(C_681,'#skF_1',B_682)
      | k1_relset_1('#skF_1',B_682,C_681) != '#skF_1'
      | ~ r1_tarski(k2_relat_1(C_681),B_682)
      | ~ r1_tarski(k1_relat_1(C_681),'#skF_1')
      | ~ v1_relat_1(C_681) ) ),
    inference(resolution,[status(thm)],[c_7182,c_7011])).

tff(c_7921,plain,(
    ! [B_682] :
      ( v1_funct_2('#skF_4','#skF_1',B_682)
      | k1_relset_1('#skF_1',B_682,'#skF_4') != '#skF_1'
      | ~ r1_tarski('#skF_1',B_682)
      | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6660,c_7915])).

tff(c_7931,plain,(
    ! [B_682] : v1_funct_2('#skF_4','#skF_1',B_682) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6615,c_6596,c_6763,c_6596,c_7369,c_7921])).

tff(c_6644,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_7937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7931,c_6644])).

tff(c_7938,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_8511,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8486,c_7938])).

tff(c_8527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6615,c_6596,c_8028,c_6596,c_7987,c_8511])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:04:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.60/2.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.60/2.68  
% 7.60/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.60/2.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.60/2.68  
% 7.60/2.68  %Foreground sorts:
% 7.60/2.68  
% 7.60/2.68  
% 7.60/2.68  %Background operators:
% 7.60/2.68  
% 7.60/2.68  
% 7.60/2.68  %Foreground operators:
% 7.60/2.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.60/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.60/2.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.60/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.60/2.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.60/2.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.60/2.68  tff('#skF_2', type, '#skF_2': $i).
% 7.60/2.68  tff('#skF_3', type, '#skF_3': $i).
% 7.60/2.68  tff('#skF_1', type, '#skF_1': $i).
% 7.60/2.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.60/2.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.60/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.60/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.60/2.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.60/2.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.60/2.68  tff('#skF_4', type, '#skF_4': $i).
% 7.60/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.60/2.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.60/2.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.60/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.60/2.68  
% 8.15/2.71  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 8.15/2.71  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.15/2.71  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.15/2.71  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.15/2.71  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.15/2.71  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.15/2.71  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.15/2.71  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 8.15/2.71  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.15/2.71  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.15/2.71  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.15/2.71  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.15/2.71  tff(c_59, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.15/2.71  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_59])).
% 8.15/2.71  tff(c_196, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.15/2.71  tff(c_200, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_196])).
% 8.15/2.71  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.15/2.71  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.15/2.71  tff(c_100, plain, (![B_36, A_37]: (v5_relat_1(B_36, A_37) | ~r1_tarski(k2_relat_1(B_36), A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.15/2.71  tff(c_109, plain, (![B_36]: (v5_relat_1(B_36, k2_relat_1(B_36)) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_6, c_100])).
% 8.15/2.71  tff(c_112, plain, (![C_40, B_41, A_42]: (v5_relat_1(C_40, B_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_42, B_41))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.15/2.71  tff(c_116, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_112])).
% 8.15/2.71  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.15/2.71  tff(c_117, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.15/2.71  tff(c_6177, plain, (![A_465, A_466, B_467]: (r1_tarski(A_465, A_466) | ~r1_tarski(A_465, k2_relat_1(B_467)) | ~v5_relat_1(B_467, A_466) | ~v1_relat_1(B_467))), inference(resolution, [status(thm)], [c_18, c_117])).
% 8.15/2.71  tff(c_6454, plain, (![B_499, A_500, B_501]: (r1_tarski(k2_relat_1(B_499), A_500) | ~v5_relat_1(B_501, A_500) | ~v1_relat_1(B_501) | ~v5_relat_1(B_499, k2_relat_1(B_501)) | ~v1_relat_1(B_499))), inference(resolution, [status(thm)], [c_18, c_6177])).
% 8.15/2.71  tff(c_6458, plain, (![B_499]: (r1_tarski(k2_relat_1(B_499), '#skF_2') | ~v1_relat_1('#skF_4') | ~v5_relat_1(B_499, k2_relat_1('#skF_4')) | ~v1_relat_1(B_499))), inference(resolution, [status(thm)], [c_116, c_6454])).
% 8.15/2.71  tff(c_6468, plain, (![B_502]: (r1_tarski(k2_relat_1(B_502), '#skF_2') | ~v5_relat_1(B_502, k2_relat_1('#skF_4')) | ~v1_relat_1(B_502))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_6458])).
% 8.15/2.71  tff(c_6472, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_109, c_6468])).
% 8.15/2.71  tff(c_6475, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_6472])).
% 8.15/2.71  tff(c_46, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.15/2.71  tff(c_129, plain, (![A_43]: (r1_tarski(A_43, '#skF_3') | ~r1_tarski(A_43, '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_117])).
% 8.15/2.71  tff(c_6486, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_6475, c_129])).
% 8.15/2.71  tff(c_6538, plain, (![C_504, A_505, B_506]: (m1_subset_1(C_504, k1_zfmisc_1(k2_zfmisc_1(A_505, B_506))) | ~r1_tarski(k2_relat_1(C_504), B_506) | ~r1_tarski(k1_relat_1(C_504), A_505) | ~v1_relat_1(C_504))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.15/2.71  tff(c_145, plain, (![A_48]: (r1_tarski(A_48, '#skF_3') | ~r1_tarski(A_48, '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_117])).
% 8.15/2.71  tff(c_158, plain, (![B_10]: (r1_tarski(k2_relat_1(B_10), '#skF_3') | ~v5_relat_1(B_10, '#skF_2') | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_18, c_145])).
% 8.15/2.71  tff(c_28, plain, (![C_22, A_20, B_21]: (m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~r1_tarski(k2_relat_1(C_22), B_21) | ~r1_tarski(k1_relat_1(C_22), A_20) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.15/2.71  tff(c_2039, plain, (![B_203, C_204, A_205]: (k1_xboole_0=B_203 | v1_funct_2(C_204, A_205, B_203) | k1_relset_1(A_205, B_203, C_204)!=A_205 | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_205, B_203))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.15/2.71  tff(c_3402, plain, (![B_275, C_276, A_277]: (k1_xboole_0=B_275 | v1_funct_2(C_276, A_277, B_275) | k1_relset_1(A_277, B_275, C_276)!=A_277 | ~r1_tarski(k2_relat_1(C_276), B_275) | ~r1_tarski(k1_relat_1(C_276), A_277) | ~v1_relat_1(C_276))), inference(resolution, [status(thm)], [c_28, c_2039])).
% 8.15/2.71  tff(c_3429, plain, (![B_10, A_277]: (k1_xboole_0='#skF_3' | v1_funct_2(B_10, A_277, '#skF_3') | k1_relset_1(A_277, '#skF_3', B_10)!=A_277 | ~r1_tarski(k1_relat_1(B_10), A_277) | ~v5_relat_1(B_10, '#skF_2') | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_158, c_3402])).
% 8.15/2.71  tff(c_3495, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3429])).
% 8.15/2.71  tff(c_44, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.15/2.71  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_44])).
% 8.15/2.71  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.15/2.71  tff(c_286, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.15/2.71  tff(c_290, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_286])).
% 8.15/2.71  tff(c_832, plain, (![B_140, A_141, C_142]: (k1_xboole_0=B_140 | k1_relset_1(A_141, B_140, C_142)=A_141 | ~v1_funct_2(C_142, A_141, B_140) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.15/2.71  tff(c_838, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_832])).
% 8.15/2.71  tff(c_842, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_290, c_838])).
% 8.15/2.71  tff(c_843, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_842])).
% 8.15/2.71  tff(c_613, plain, (![C_118, A_119, B_120]: (m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~r1_tarski(k2_relat_1(C_118), B_120) | ~r1_tarski(k1_relat_1(C_118), A_119) | ~v1_relat_1(C_118))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.15/2.71  tff(c_26, plain, (![A_17, B_18, C_19]: (k1_relset_1(A_17, B_18, C_19)=k1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.15/2.71  tff(c_1006, plain, (![A_145, B_146, C_147]: (k1_relset_1(A_145, B_146, C_147)=k1_relat_1(C_147) | ~r1_tarski(k2_relat_1(C_147), B_146) | ~r1_tarski(k1_relat_1(C_147), A_145) | ~v1_relat_1(C_147))), inference(resolution, [status(thm)], [c_613, c_26])).
% 8.15/2.71  tff(c_1030, plain, (![A_148, B_149]: (k1_relset_1(A_148, '#skF_3', B_149)=k1_relat_1(B_149) | ~r1_tarski(k1_relat_1(B_149), A_148) | ~v5_relat_1(B_149, '#skF_2') | ~v1_relat_1(B_149))), inference(resolution, [status(thm)], [c_158, c_1006])).
% 8.15/2.71  tff(c_1033, plain, (![A_148]: (k1_relset_1(A_148, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_148) | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_843, c_1030])).
% 8.15/2.71  tff(c_1076, plain, (![A_151]: (k1_relset_1(A_151, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_151))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_116, c_843, c_1033])).
% 8.15/2.71  tff(c_1081, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_1076])).
% 8.15/2.71  tff(c_354, plain, (![A_82, A_83, B_84]: (r1_tarski(A_82, A_83) | ~r1_tarski(A_82, k2_relat_1(B_84)) | ~v5_relat_1(B_84, A_83) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_18, c_117])).
% 8.15/2.71  tff(c_650, plain, (![B_121, A_122, B_123]: (r1_tarski(k2_relat_1(B_121), A_122) | ~v5_relat_1(B_123, A_122) | ~v1_relat_1(B_123) | ~v5_relat_1(B_121, k2_relat_1(B_123)) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_18, c_354])).
% 8.15/2.71  tff(c_654, plain, (![B_121]: (r1_tarski(k2_relat_1(B_121), '#skF_2') | ~v1_relat_1('#skF_4') | ~v5_relat_1(B_121, k2_relat_1('#skF_4')) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_116, c_650])).
% 8.15/2.71  tff(c_664, plain, (![B_124]: (r1_tarski(k2_relat_1(B_124), '#skF_2') | ~v5_relat_1(B_124, k2_relat_1('#skF_4')) | ~v1_relat_1(B_124))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_654])).
% 8.15/2.71  tff(c_668, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_109, c_664])).
% 8.15/2.71  tff(c_671, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_668])).
% 8.15/2.71  tff(c_682, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_671, c_129])).
% 8.15/2.71  tff(c_768, plain, (![B_127, C_128, A_129]: (k1_xboole_0=B_127 | v1_funct_2(C_128, A_129, B_127) | k1_relset_1(A_129, B_127, C_128)!=A_129 | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_127))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.15/2.71  tff(c_1923, plain, (![B_198, C_199, A_200]: (k1_xboole_0=B_198 | v1_funct_2(C_199, A_200, B_198) | k1_relset_1(A_200, B_198, C_199)!=A_200 | ~r1_tarski(k2_relat_1(C_199), B_198) | ~r1_tarski(k1_relat_1(C_199), A_200) | ~v1_relat_1(C_199))), inference(resolution, [status(thm)], [c_28, c_768])).
% 8.15/2.71  tff(c_1929, plain, (![A_200]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_200, '#skF_3') | k1_relset_1(A_200, '#skF_3', '#skF_4')!=A_200 | ~r1_tarski(k1_relat_1('#skF_4'), A_200) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_682, c_1923])).
% 8.15/2.71  tff(c_1945, plain, (![A_200]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_200, '#skF_3') | k1_relset_1(A_200, '#skF_3', '#skF_4')!=A_200 | ~r1_tarski('#skF_1', A_200))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_843, c_1929])).
% 8.15/2.71  tff(c_1961, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1945])).
% 8.15/2.71  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.15/2.71  tff(c_1996, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1961, c_10])).
% 8.15/2.71  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.15/2.71  tff(c_699, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_682, c_2])).
% 8.15/2.71  tff(c_767, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_699])).
% 8.15/2.71  tff(c_2009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1996, c_767])).
% 8.15/2.71  tff(c_2012, plain, (![A_202]: (v1_funct_2('#skF_4', A_202, '#skF_3') | k1_relset_1(A_202, '#skF_3', '#skF_4')!=A_202 | ~r1_tarski('#skF_1', A_202))), inference(splitRight, [status(thm)], [c_1945])).
% 8.15/2.71  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.15/2.71  tff(c_42, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.15/2.71  tff(c_54, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_42])).
% 8.15/2.71  tff(c_201, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 8.15/2.71  tff(c_2017, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2012, c_201])).
% 8.15/2.71  tff(c_2025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1081, c_2017])).
% 8.15/2.71  tff(c_2026, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_699])).
% 8.15/2.71  tff(c_687, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_671, c_2])).
% 8.15/2.71  tff(c_733, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_687])).
% 8.15/2.71  tff(c_2029, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2026, c_733])).
% 8.15/2.71  tff(c_2036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2029])).
% 8.15/2.71  tff(c_2037, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_687])).
% 8.15/2.71  tff(c_16, plain, (![B_10, A_9]: (v5_relat_1(B_10, A_9) | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.15/2.71  tff(c_2084, plain, (![A_9]: (v5_relat_1('#skF_4', A_9) | ~r1_tarski('#skF_2', A_9) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2037, c_16])).
% 8.15/2.71  tff(c_2116, plain, (![A_206]: (v5_relat_1('#skF_4', A_206) | ~r1_tarski('#skF_2', A_206))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_2084])).
% 8.15/2.71  tff(c_91, plain, (![B_34, A_35]: (r1_tarski(k2_relat_1(B_34), A_35) | ~v5_relat_1(B_34, A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.15/2.71  tff(c_64, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.15/2.71  tff(c_75, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_64])).
% 8.15/2.71  tff(c_98, plain, (![B_34]: (k2_relat_1(B_34)=k1_xboole_0 | ~v5_relat_1(B_34, k1_xboole_0) | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_91, c_75])).
% 8.15/2.71  tff(c_2139, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_2116, c_98])).
% 8.15/2.71  tff(c_2158, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_2037, c_2139])).
% 8.15/2.71  tff(c_2159, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_58, c_2158])).
% 8.15/2.71  tff(c_3507, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3495, c_2159])).
% 8.15/2.71  tff(c_3533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_3507])).
% 8.15/2.71  tff(c_3535, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3429])).
% 8.15/2.71  tff(c_2182, plain, (![B_208, A_209, C_210]: (k1_xboole_0=B_208 | k1_relset_1(A_209, B_208, C_210)=A_209 | ~v1_funct_2(C_210, A_209, B_208) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_209, B_208))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.15/2.71  tff(c_2188, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_2182])).
% 8.15/2.71  tff(c_2192, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_290, c_2188])).
% 8.15/2.71  tff(c_2193, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_2192])).
% 8.15/2.71  tff(c_2331, plain, (![A_213, B_214, C_215]: (k1_relset_1(A_213, B_214, C_215)=k1_relat_1(C_215) | ~r1_tarski(k2_relat_1(C_215), B_214) | ~r1_tarski(k1_relat_1(C_215), A_213) | ~v1_relat_1(C_215))), inference(resolution, [status(thm)], [c_613, c_26])).
% 8.15/2.71  tff(c_2353, plain, (![A_216, B_217]: (k1_relset_1(A_216, '#skF_3', B_217)=k1_relat_1(B_217) | ~r1_tarski(k1_relat_1(B_217), A_216) | ~v5_relat_1(B_217, '#skF_2') | ~v1_relat_1(B_217))), inference(resolution, [status(thm)], [c_158, c_2331])).
% 8.15/2.71  tff(c_2356, plain, (![A_216]: (k1_relset_1(A_216, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_216) | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2193, c_2353])).
% 8.15/2.71  tff(c_2397, plain, (![A_219]: (k1_relset_1(A_219, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_219))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_116, c_2193, c_2356])).
% 8.15/2.71  tff(c_2402, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_2397])).
% 8.15/2.71  tff(c_3412, plain, (![B_275, A_277]: (k1_xboole_0=B_275 | v1_funct_2('#skF_4', A_277, B_275) | k1_relset_1(A_277, B_275, '#skF_4')!=A_277 | ~r1_tarski('#skF_2', B_275) | ~r1_tarski(k1_relat_1('#skF_4'), A_277) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2037, c_3402])).
% 8.15/2.71  tff(c_5992, plain, (![B_443, A_444]: (k1_xboole_0=B_443 | v1_funct_2('#skF_4', A_444, B_443) | k1_relset_1(A_444, B_443, '#skF_4')!=A_444 | ~r1_tarski('#skF_2', B_443) | ~r1_tarski('#skF_1', A_444))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_2193, c_3412])).
% 8.15/2.71  tff(c_6024, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_2', '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_5992, c_201])).
% 8.15/2.71  tff(c_6053, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_46, c_2402, c_6024])).
% 8.15/2.71  tff(c_6055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3535, c_6053])).
% 8.15/2.71  tff(c_6056, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_54])).
% 8.15/2.71  tff(c_6560, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6538, c_6056])).
% 8.15/2.71  tff(c_6577, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_6486, c_6560])).
% 8.15/2.71  tff(c_6586, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_6577])).
% 8.15/2.71  tff(c_6593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_200, c_6586])).
% 8.15/2.71  tff(c_6594, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_44])).
% 8.15/2.71  tff(c_6595, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_44])).
% 8.15/2.71  tff(c_6601, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6594, c_6595])).
% 8.15/2.71  tff(c_6608, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6601, c_48])).
% 8.15/2.71  tff(c_6611, plain, (![C_508, A_509, B_510]: (v1_relat_1(C_508) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(A_509, B_510))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.15/2.71  tff(c_6615, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6608, c_6611])).
% 8.15/2.71  tff(c_6596, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_6594, c_10])).
% 8.15/2.71  tff(c_8018, plain, (![C_697, A_698, B_699]: (v4_relat_1(C_697, A_698) | ~m1_subset_1(C_697, k1_zfmisc_1(k2_zfmisc_1(A_698, B_699))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.15/2.71  tff(c_8022, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_6608, c_8018])).
% 8.15/2.71  tff(c_7997, plain, (![B_694, A_695]: (r1_tarski(k1_relat_1(B_694), A_695) | ~v4_relat_1(B_694, A_695) | ~v1_relat_1(B_694))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.15/2.71  tff(c_6616, plain, (![B_511, A_512]: (B_511=A_512 | ~r1_tarski(B_511, A_512) | ~r1_tarski(A_512, B_511))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.15/2.71  tff(c_6621, plain, (![A_6]: (A_6='#skF_1' | ~r1_tarski(A_6, '#skF_1'))), inference(resolution, [status(thm)], [c_6596, c_6616])).
% 8.15/2.71  tff(c_8015, plain, (![B_694]: (k1_relat_1(B_694)='#skF_1' | ~v4_relat_1(B_694, '#skF_1') | ~v1_relat_1(B_694))), inference(resolution, [status(thm)], [c_7997, c_6621])).
% 8.15/2.71  tff(c_8025, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8022, c_8015])).
% 8.15/2.71  tff(c_8028, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6615, c_8025])).
% 8.15/2.71  tff(c_6639, plain, (![C_514, B_515, A_516]: (v5_relat_1(C_514, B_515) | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(A_516, B_515))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.15/2.71  tff(c_6643, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_6608, c_6639])).
% 8.15/2.71  tff(c_7947, plain, (![B_686, A_687]: (r1_tarski(k2_relat_1(B_686), A_687) | ~v5_relat_1(B_686, A_687) | ~v1_relat_1(B_686))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.15/2.71  tff(c_7981, plain, (![B_693]: (k2_relat_1(B_693)='#skF_1' | ~v5_relat_1(B_693, '#skF_1') | ~v1_relat_1(B_693))), inference(resolution, [status(thm)], [c_7947, c_6621])).
% 8.15/2.71  tff(c_7984, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6643, c_7981])).
% 8.15/2.71  tff(c_7987, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6615, c_7984])).
% 8.15/2.71  tff(c_8486, plain, (![C_752, A_753, B_754]: (m1_subset_1(C_752, k1_zfmisc_1(k2_zfmisc_1(A_753, B_754))) | ~r1_tarski(k2_relat_1(C_752), B_754) | ~r1_tarski(k1_relat_1(C_752), A_753) | ~v1_relat_1(C_752))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.15/2.71  tff(c_6680, plain, (![C_523, A_524, B_525]: (v4_relat_1(C_523, A_524) | ~m1_subset_1(C_523, k1_zfmisc_1(k2_zfmisc_1(A_524, B_525))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.15/2.71  tff(c_6684, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_6608, c_6680])).
% 8.15/2.71  tff(c_6737, plain, (![B_535, A_536]: (r1_tarski(k1_relat_1(B_535), A_536) | ~v4_relat_1(B_535, A_536) | ~v1_relat_1(B_535))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.15/2.71  tff(c_6757, plain, (![B_537]: (k1_relat_1(B_537)='#skF_1' | ~v4_relat_1(B_537, '#skF_1') | ~v1_relat_1(B_537))), inference(resolution, [status(thm)], [c_6737, c_6621])).
% 8.15/2.71  tff(c_6760, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6684, c_6757])).
% 8.15/2.71  tff(c_6763, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6615, c_6760])).
% 8.15/2.71  tff(c_6645, plain, (![B_517, A_518]: (r1_tarski(k2_relat_1(B_517), A_518) | ~v5_relat_1(B_517, A_518) | ~v1_relat_1(B_517))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.15/2.71  tff(c_6654, plain, (![B_519]: (k2_relat_1(B_519)='#skF_1' | ~v5_relat_1(B_519, '#skF_1') | ~v1_relat_1(B_519))), inference(resolution, [status(thm)], [c_6645, c_6621])).
% 8.15/2.71  tff(c_6657, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6643, c_6654])).
% 8.15/2.71  tff(c_6660, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6615, c_6657])).
% 8.15/2.71  tff(c_7182, plain, (![C_583, A_584, B_585]: (m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(A_584, B_585))) | ~r1_tarski(k2_relat_1(C_583), B_585) | ~r1_tarski(k1_relat_1(C_583), A_584) | ~v1_relat_1(C_583))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.15/2.71  tff(c_7357, plain, (![A_615, B_616, C_617]: (k1_relset_1(A_615, B_616, C_617)=k1_relat_1(C_617) | ~r1_tarski(k2_relat_1(C_617), B_616) | ~r1_tarski(k1_relat_1(C_617), A_615) | ~v1_relat_1(C_617))), inference(resolution, [status(thm)], [c_7182, c_26])).
% 8.15/2.71  tff(c_7361, plain, (![A_615, B_616]: (k1_relset_1(A_615, B_616, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', B_616) | ~r1_tarski(k1_relat_1('#skF_4'), A_615) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6660, c_7357])).
% 8.15/2.71  tff(c_7369, plain, (![A_615, B_616]: (k1_relset_1(A_615, B_616, '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6615, c_6596, c_6763, c_6596, c_6763, c_7361])).
% 8.15/2.71  tff(c_34, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.15/2.71  tff(c_7011, plain, (![C_25, B_24]: (v1_funct_2(C_25, '#skF_1', B_24) | k1_relset_1('#skF_1', B_24, C_25)!='#skF_1' | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_24))))), inference(demodulation, [status(thm), theory('equality')], [c_6594, c_6594, c_6594, c_6594, c_34])).
% 8.15/2.71  tff(c_7915, plain, (![C_681, B_682]: (v1_funct_2(C_681, '#skF_1', B_682) | k1_relset_1('#skF_1', B_682, C_681)!='#skF_1' | ~r1_tarski(k2_relat_1(C_681), B_682) | ~r1_tarski(k1_relat_1(C_681), '#skF_1') | ~v1_relat_1(C_681))), inference(resolution, [status(thm)], [c_7182, c_7011])).
% 8.15/2.71  tff(c_7921, plain, (![B_682]: (v1_funct_2('#skF_4', '#skF_1', B_682) | k1_relset_1('#skF_1', B_682, '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', B_682) | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6660, c_7915])).
% 8.15/2.71  tff(c_7931, plain, (![B_682]: (v1_funct_2('#skF_4', '#skF_1', B_682))), inference(demodulation, [status(thm), theory('equality')], [c_6615, c_6596, c_6763, c_6596, c_7369, c_7921])).
% 8.15/2.71  tff(c_6644, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 8.15/2.71  tff(c_7937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7931, c_6644])).
% 8.15/2.71  tff(c_7938, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_54])).
% 8.15/2.71  tff(c_8511, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8486, c_7938])).
% 8.15/2.71  tff(c_8527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6615, c_6596, c_8028, c_6596, c_7987, c_8511])).
% 8.15/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.15/2.71  
% 8.15/2.71  Inference rules
% 8.15/2.71  ----------------------
% 8.15/2.71  #Ref     : 0
% 8.15/2.71  #Sup     : 1728
% 8.15/2.71  #Fact    : 0
% 8.15/2.71  #Define  : 0
% 8.15/2.71  #Split   : 20
% 8.15/2.71  #Chain   : 0
% 8.15/2.71  #Close   : 0
% 8.15/2.71  
% 8.15/2.71  Ordering : KBO
% 8.15/2.71  
% 8.15/2.71  Simplification rules
% 8.15/2.71  ----------------------
% 8.15/2.71  #Subsume      : 559
% 8.15/2.71  #Demod        : 1290
% 8.15/2.71  #Tautology    : 453
% 8.15/2.71  #SimpNegUnit  : 19
% 8.15/2.71  #BackRed      : 138
% 8.15/2.71  
% 8.15/2.71  #Partial instantiations: 0
% 8.15/2.71  #Strategies tried      : 1
% 8.15/2.71  
% 8.15/2.71  Timing (in seconds)
% 8.15/2.71  ----------------------
% 8.15/2.71  Preprocessing        : 0.34
% 8.15/2.71  Parsing              : 0.18
% 8.15/2.71  CNF conversion       : 0.02
% 8.15/2.71  Main loop            : 1.50
% 8.15/2.71  Inferencing          : 0.45
% 8.15/2.71  Reduction            : 0.44
% 8.15/2.71  Demodulation         : 0.29
% 8.15/2.71  BG Simplification    : 0.05
% 8.15/2.71  Subsumption          : 0.44
% 8.15/2.71  Abstraction          : 0.06
% 8.15/2.71  MUC search           : 0.00
% 8.15/2.71  Cooper               : 0.00
% 8.15/2.71  Total                : 1.91
% 8.15/2.71  Index Insertion      : 0.00
% 8.15/2.71  Index Deletion       : 0.00
% 8.15/2.71  Index Matching       : 0.00
% 8.15/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
