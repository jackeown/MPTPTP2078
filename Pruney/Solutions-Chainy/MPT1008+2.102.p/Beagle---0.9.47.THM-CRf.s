%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:40 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 284 expanded)
%              Number of leaves         :   41 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 ( 675 expanded)
%              Number of equality atoms :   59 ( 303 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_24,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_89,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_89])).

tff(c_95,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_92])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_125,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_129,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_125])).

tff(c_197,plain,(
    ! [B_82,A_83,C_84] :
      ( k1_xboole_0 = B_82
      | k1_relset_1(A_83,B_82,C_84) = A_83
      | ~ v1_funct_2(C_84,A_83,B_82)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_200,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_197])).

tff(c_203,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_129,c_200])).

tff(c_204,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_203])).

tff(c_22,plain,(
    ! [A_15,B_17] :
      ( k9_relat_1(A_15,k1_tarski(B_17)) = k11_relat_1(A_15,B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_310,plain,(
    ! [A_90] :
      ( k9_relat_1(A_90,k1_relat_1('#skF_5')) = k11_relat_1(A_90,'#skF_3')
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_22])).

tff(c_26,plain,(
    ! [A_20] :
      ( k9_relat_1(A_20,k1_relat_1(A_20)) = k2_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_317,plain,
    ( k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_26])).

tff(c_327,plain,(
    k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_95,c_317])).

tff(c_216,plain,(
    ! [A_15] :
      ( k9_relat_1(A_15,k1_relat_1('#skF_5')) = k11_relat_1(A_15,'#skF_3')
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_22])).

tff(c_147,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( k7_relset_1(A_67,B_68,C_69,D_70) = k9_relat_1(C_69,D_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_150,plain,(
    ! [D_70] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5',D_70) = k9_relat_1('#skF_5',D_70) ),
    inference(resolution,[status(thm)],[c_58,c_147])).

tff(c_205,plain,(
    ! [D_70] : k7_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5',D_70) = k9_relat_1('#skF_5',D_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_150])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_209,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_60])).

tff(c_208,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_58])).

tff(c_532,plain,(
    ! [B_109,A_110,C_111] :
      ( k1_xboole_0 = B_109
      | k8_relset_1(A_110,B_109,C_111,B_109) = A_110
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109)))
      | ~ v1_funct_2(C_111,A_110,B_109)
      | ~ v1_funct_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_534,plain,
    ( k1_xboole_0 = '#skF_4'
    | k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4') = k1_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_208,c_532])).

tff(c_537,plain,
    ( k1_xboole_0 = '#skF_4'
    | k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_209,c_534])).

tff(c_538,plain,(
    k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_537])).

tff(c_405,plain,(
    ! [B_96,A_97,C_98] :
      ( k7_relset_1(B_96,A_97,C_98,k8_relset_1(B_96,A_97,C_98,A_97)) = k2_relset_1(B_96,A_97,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(B_96,A_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_408,plain,(
    k7_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5',k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4')) = k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_208,c_405])).

tff(c_540,plain,(
    k7_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5',k1_relat_1('#skF_5')) = k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_408])).

tff(c_541,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') = k9_relat_1('#skF_5',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_540])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_222,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_4])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( k1_tarski(k1_funct_1(B_22,A_21)) = k11_relat_1(B_22,A_21)
      | ~ r2_hidden(A_21,k1_relat_1(B_22))
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_229,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_222,c_28])).

tff(c_232,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_62,c_229])).

tff(c_54,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_207,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_54])).

tff(c_299,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') != k11_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_207])).

tff(c_331,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_299])).

tff(c_546,plain,(
    k9_relat_1('#skF_5',k1_relat_1('#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_331])).

tff(c_553,plain,
    ( k11_relat_1('#skF_5','#skF_3') != k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_546])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_327,c_553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.41  
% 2.70/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.41  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.70/1.41  
% 2.70/1.41  %Foreground sorts:
% 2.70/1.41  
% 2.70/1.41  
% 2.70/1.41  %Background operators:
% 2.70/1.41  
% 2.70/1.41  
% 2.70/1.41  %Foreground operators:
% 2.70/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.70/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.41  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.70/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.41  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.70/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.70/1.41  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.70/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.70/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.70/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.70/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.41  
% 2.70/1.42  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.70/1.42  tff(f_120, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.70/1.42  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.70/1.42  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.70/1.42  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.70/1.42  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.70/1.42  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.70/1.42  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.70/1.42  tff(f_108, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 2.70/1.42  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 2.70/1.42  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.70/1.42  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 2.70/1.42  tff(c_24, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.70/1.42  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.70/1.42  tff(c_89, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.42  tff(c_92, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_89])).
% 2.70/1.42  tff(c_95, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_92])).
% 2.70/1.42  tff(c_56, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.70/1.42  tff(c_60, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.70/1.42  tff(c_125, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.70/1.42  tff(c_129, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_125])).
% 2.70/1.42  tff(c_197, plain, (![B_82, A_83, C_84]: (k1_xboole_0=B_82 | k1_relset_1(A_83, B_82, C_84)=A_83 | ~v1_funct_2(C_84, A_83, B_82) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.70/1.42  tff(c_200, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_58, c_197])).
% 2.70/1.42  tff(c_203, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_129, c_200])).
% 2.70/1.42  tff(c_204, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_203])).
% 2.70/1.42  tff(c_22, plain, (![A_15, B_17]: (k9_relat_1(A_15, k1_tarski(B_17))=k11_relat_1(A_15, B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.70/1.42  tff(c_310, plain, (![A_90]: (k9_relat_1(A_90, k1_relat_1('#skF_5'))=k11_relat_1(A_90, '#skF_3') | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_204, c_22])).
% 2.70/1.42  tff(c_26, plain, (![A_20]: (k9_relat_1(A_20, k1_relat_1(A_20))=k2_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.42  tff(c_317, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_310, c_26])).
% 2.70/1.42  tff(c_327, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_95, c_317])).
% 2.70/1.42  tff(c_216, plain, (![A_15]: (k9_relat_1(A_15, k1_relat_1('#skF_5'))=k11_relat_1(A_15, '#skF_3') | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_204, c_22])).
% 2.70/1.42  tff(c_147, plain, (![A_67, B_68, C_69, D_70]: (k7_relset_1(A_67, B_68, C_69, D_70)=k9_relat_1(C_69, D_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.70/1.42  tff(c_150, plain, (![D_70]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5', D_70)=k9_relat_1('#skF_5', D_70))), inference(resolution, [status(thm)], [c_58, c_147])).
% 2.70/1.42  tff(c_205, plain, (![D_70]: (k7_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', D_70)=k9_relat_1('#skF_5', D_70))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_150])).
% 2.70/1.42  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.70/1.42  tff(c_209, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_60])).
% 2.70/1.42  tff(c_208, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_58])).
% 2.70/1.42  tff(c_532, plain, (![B_109, A_110, C_111]: (k1_xboole_0=B_109 | k8_relset_1(A_110, B_109, C_111, B_109)=A_110 | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))) | ~v1_funct_2(C_111, A_110, B_109) | ~v1_funct_1(C_111))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.70/1.42  tff(c_534, plain, (k1_xboole_0='#skF_4' | k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4')=k1_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_208, c_532])).
% 2.70/1.42  tff(c_537, plain, (k1_xboole_0='#skF_4' | k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_209, c_534])).
% 2.70/1.42  tff(c_538, plain, (k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_537])).
% 2.70/1.42  tff(c_405, plain, (![B_96, A_97, C_98]: (k7_relset_1(B_96, A_97, C_98, k8_relset_1(B_96, A_97, C_98, A_97))=k2_relset_1(B_96, A_97, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(B_96, A_97))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.70/1.42  tff(c_408, plain, (k7_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4'))=k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_208, c_405])).
% 2.70/1.42  tff(c_540, plain, (k7_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', k1_relat_1('#skF_5'))=k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_408])).
% 2.70/1.42  tff(c_541, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')=k9_relat_1('#skF_5', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_540])).
% 2.70/1.42  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.70/1.42  tff(c_222, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_4])).
% 2.70/1.42  tff(c_28, plain, (![B_22, A_21]: (k1_tarski(k1_funct_1(B_22, A_21))=k11_relat_1(B_22, A_21) | ~r2_hidden(A_21, k1_relat_1(B_22)) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.42  tff(c_229, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_222, c_28])).
% 2.70/1.42  tff(c_232, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_62, c_229])).
% 2.70/1.42  tff(c_54, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.70/1.42  tff(c_207, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_54])).
% 2.70/1.42  tff(c_299, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')!=k11_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_207])).
% 2.70/1.42  tff(c_331, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_327, c_299])).
% 2.70/1.42  tff(c_546, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_541, c_331])).
% 2.70/1.42  tff(c_553, plain, (k11_relat_1('#skF_5', '#skF_3')!=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_216, c_546])).
% 2.70/1.42  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_327, c_553])).
% 2.70/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.42  
% 2.70/1.42  Inference rules
% 2.70/1.42  ----------------------
% 2.70/1.42  #Ref     : 0
% 2.70/1.42  #Sup     : 109
% 2.70/1.42  #Fact    : 2
% 2.70/1.42  #Define  : 0
% 2.70/1.42  #Split   : 0
% 2.70/1.42  #Chain   : 0
% 2.70/1.42  #Close   : 0
% 2.70/1.42  
% 2.70/1.42  Ordering : KBO
% 2.70/1.42  
% 2.70/1.42  Simplification rules
% 2.70/1.42  ----------------------
% 2.70/1.42  #Subsume      : 9
% 2.70/1.42  #Demod        : 69
% 2.70/1.42  #Tautology    : 69
% 2.70/1.42  #SimpNegUnit  : 4
% 2.70/1.42  #BackRed      : 11
% 2.70/1.42  
% 2.70/1.42  #Partial instantiations: 0
% 2.70/1.42  #Strategies tried      : 1
% 2.70/1.42  
% 2.70/1.42  Timing (in seconds)
% 2.70/1.42  ----------------------
% 2.70/1.43  Preprocessing        : 0.35
% 2.70/1.43  Parsing              : 0.19
% 2.70/1.43  CNF conversion       : 0.02
% 2.70/1.43  Main loop            : 0.31
% 2.70/1.43  Inferencing          : 0.12
% 2.70/1.43  Reduction            : 0.10
% 2.70/1.43  Demodulation         : 0.07
% 2.70/1.43  BG Simplification    : 0.02
% 2.70/1.43  Subsumption          : 0.06
% 2.70/1.43  Abstraction          : 0.02
% 2.70/1.43  MUC search           : 0.00
% 2.70/1.43  Cooper               : 0.00
% 2.70/1.43  Total                : 0.70
% 2.70/1.43  Index Insertion      : 0.00
% 2.70/1.43  Index Deletion       : 0.00
% 2.70/1.43  Index Matching       : 0.00
% 2.70/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
