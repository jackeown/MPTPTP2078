%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:29 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 590 expanded)
%              Number of leaves         :   34 ( 235 expanded)
%              Depth                    :   13
%              Number of atoms          :  142 (2058 expanded)
%              Number of equality atoms :   27 ( 347 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( B != k1_xboole_0
            & ? [D] :
                ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A)) )
            & ~ v2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_88,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(c_46,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_40,plain,(
    ! [A_21] : k6_relat_1(A_21) = k6_partfun1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_64,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28])).

tff(c_421,plain,(
    ! [F_84,C_81,B_83,E_85,D_82,A_86] :
      ( m1_subset_1(k1_partfun1(A_86,B_83,C_81,D_82,E_85,F_84),k1_zfmisc_1(k2_zfmisc_1(A_86,D_82)))
      | ~ m1_subset_1(F_84,k1_zfmisc_1(k2_zfmisc_1(C_81,D_82)))
      | ~ v1_funct_1(F_84)
      | ~ m1_subset_1(E_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_83)))
      | ~ v1_funct_1(E_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    ! [A_14] : m1_subset_1(k6_relat_1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_63,plain,(
    ! [A_14] : m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34])).

tff(c_48,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_244,plain,(
    ! [D_52,C_53,A_54,B_55] :
      ( D_52 = C_53
      | ~ r2_relset_1(A_54,B_55,C_53,D_52)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_254,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_244])).

tff(c_273,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_254])).

tff(c_296,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_432,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_421,c_296])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_50,c_432])).

tff(c_451,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_666,plain,(
    ! [C_137,D_138,E_136,B_139,A_135] :
      ( k1_xboole_0 = C_137
      | v2_funct_1(D_138)
      | ~ v2_funct_1(k1_partfun1(A_135,B_139,B_139,C_137,D_138,E_136))
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(B_139,C_137)))
      | ~ v1_funct_2(E_136,B_139,C_137)
      | ~ v1_funct_1(E_136)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(A_135,B_139)))
      | ~ v1_funct_2(D_138,A_135,B_139)
      | ~ v1_funct_1(D_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_668,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_666])).

tff(c_673,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_52,c_50,c_64,c_668])).

tff(c_674,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_673])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_702,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_674,c_8])).

tff(c_112,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_120,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_112])).

tff(c_816,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_120])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_894,plain,(
    ! [A_151] :
      ( A_151 = '#skF_1'
      | ~ r1_tarski(A_151,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_674,c_4])).

tff(c_904,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_816,c_894])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_705,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_2])).

tff(c_920,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_705])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_704,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_674,c_10])).

tff(c_119,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_112])).

tff(c_758,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_119])).

tff(c_905,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_758,c_894])).

tff(c_941,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_905])).

tff(c_162,plain,(
    ! [A_42] :
      ( v2_funct_1(A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_165,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_46])).

tff(c_168,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_165])).

tff(c_174,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_942,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_174])).

tff(c_971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_942])).

tff(c_972,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_973,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_16,plain,(
    ! [A_6] :
      ( v1_relat_1(A_6)
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_990,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_973,c_16])).

tff(c_996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_972,c_990])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:57:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.67  
% 3.16/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.67  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.16/1.67  
% 3.16/1.67  %Foreground sorts:
% 3.16/1.67  
% 3.16/1.67  
% 3.16/1.67  %Background operators:
% 3.16/1.67  
% 3.16/1.67  
% 3.16/1.67  %Foreground operators:
% 3.16/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.16/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.67  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.16/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.67  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.16/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.67  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.16/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.16/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.67  
% 3.39/1.69  tff(f_133, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_2)).
% 3.39/1.69  tff(f_88, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.39/1.69  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.39/1.69  tff(f_86, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.39/1.69  tff(f_74, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.39/1.69  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.39/1.69  tff(f_110, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 3.39/1.69  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.39/1.69  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.39/1.69  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.39/1.69  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.39/1.69  tff(f_60, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 3.39/1.69  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.39/1.69  tff(c_46, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.39/1.69  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.39/1.69  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.39/1.69  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.39/1.69  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.39/1.69  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.39/1.69  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.39/1.69  tff(c_40, plain, (![A_21]: (k6_relat_1(A_21)=k6_partfun1(A_21))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.39/1.69  tff(c_28, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.39/1.69  tff(c_64, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28])).
% 3.39/1.69  tff(c_421, plain, (![F_84, C_81, B_83, E_85, D_82, A_86]: (m1_subset_1(k1_partfun1(A_86, B_83, C_81, D_82, E_85, F_84), k1_zfmisc_1(k2_zfmisc_1(A_86, D_82))) | ~m1_subset_1(F_84, k1_zfmisc_1(k2_zfmisc_1(C_81, D_82))) | ~v1_funct_1(F_84) | ~m1_subset_1(E_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_83))) | ~v1_funct_1(E_85))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.39/1.69  tff(c_34, plain, (![A_14]: (m1_subset_1(k6_relat_1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.69  tff(c_63, plain, (![A_14]: (m1_subset_1(k6_partfun1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34])).
% 3.39/1.69  tff(c_48, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.39/1.69  tff(c_244, plain, (![D_52, C_53, A_54, B_55]: (D_52=C_53 | ~r2_relset_1(A_54, B_55, C_53, D_52) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.39/1.69  tff(c_254, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_244])).
% 3.39/1.69  tff(c_273, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_254])).
% 3.39/1.69  tff(c_296, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_273])).
% 3.39/1.69  tff(c_432, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_421, c_296])).
% 3.39/1.69  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_50, c_432])).
% 3.39/1.69  tff(c_451, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_273])).
% 3.39/1.69  tff(c_666, plain, (![C_137, D_138, E_136, B_139, A_135]: (k1_xboole_0=C_137 | v2_funct_1(D_138) | ~v2_funct_1(k1_partfun1(A_135, B_139, B_139, C_137, D_138, E_136)) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(B_139, C_137))) | ~v1_funct_2(E_136, B_139, C_137) | ~v1_funct_1(E_136) | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(A_135, B_139))) | ~v1_funct_2(D_138, A_135, B_139) | ~v1_funct_1(D_138))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.39/1.69  tff(c_668, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_451, c_666])).
% 3.39/1.69  tff(c_673, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_52, c_50, c_64, c_668])).
% 3.39/1.69  tff(c_674, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_46, c_673])).
% 3.39/1.69  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.39/1.69  tff(c_702, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_674, c_674, c_8])).
% 3.39/1.69  tff(c_112, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.39/1.69  tff(c_120, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_112])).
% 3.39/1.69  tff(c_816, plain, (r1_tarski('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_702, c_120])).
% 3.39/1.69  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.39/1.69  tff(c_894, plain, (![A_151]: (A_151='#skF_1' | ~r1_tarski(A_151, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_674, c_674, c_4])).
% 3.39/1.69  tff(c_904, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_816, c_894])).
% 3.39/1.69  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.39/1.69  tff(c_705, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_674, c_2])).
% 3.39/1.69  tff(c_920, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_904, c_705])).
% 3.39/1.69  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.39/1.69  tff(c_704, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_674, c_674, c_10])).
% 3.39/1.69  tff(c_119, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_112])).
% 3.39/1.69  tff(c_758, plain, (r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_704, c_119])).
% 3.39/1.69  tff(c_905, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_758, c_894])).
% 3.39/1.69  tff(c_941, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_904, c_905])).
% 3.39/1.69  tff(c_162, plain, (![A_42]: (v2_funct_1(A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.39/1.69  tff(c_165, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_162, c_46])).
% 3.39/1.69  tff(c_168, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_165])).
% 3.39/1.69  tff(c_174, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_168])).
% 3.39/1.69  tff(c_942, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_941, c_174])).
% 3.39/1.69  tff(c_971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_920, c_942])).
% 3.39/1.69  tff(c_972, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_168])).
% 3.39/1.69  tff(c_973, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_168])).
% 3.39/1.69  tff(c_16, plain, (![A_6]: (v1_relat_1(A_6) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.39/1.69  tff(c_990, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_973, c_16])).
% 3.39/1.69  tff(c_996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_972, c_990])).
% 3.39/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.69  
% 3.39/1.69  Inference rules
% 3.39/1.69  ----------------------
% 3.39/1.69  #Ref     : 0
% 3.39/1.69  #Sup     : 199
% 3.39/1.69  #Fact    : 0
% 3.39/1.69  #Define  : 0
% 3.39/1.69  #Split   : 2
% 3.39/1.69  #Chain   : 0
% 3.39/1.69  #Close   : 0
% 3.39/1.69  
% 3.39/1.69  Ordering : KBO
% 3.39/1.69  
% 3.39/1.69  Simplification rules
% 3.39/1.69  ----------------------
% 3.39/1.69  #Subsume      : 4
% 3.39/1.69  #Demod        : 242
% 3.39/1.69  #Tautology    : 84
% 3.39/1.69  #SimpNegUnit  : 2
% 3.39/1.69  #BackRed      : 71
% 3.39/1.69  
% 3.39/1.69  #Partial instantiations: 0
% 3.39/1.69  #Strategies tried      : 1
% 3.39/1.69  
% 3.39/1.69  Timing (in seconds)
% 3.39/1.69  ----------------------
% 3.39/1.69  Preprocessing        : 0.37
% 3.39/1.69  Parsing              : 0.19
% 3.39/1.69  CNF conversion       : 0.02
% 3.39/1.69  Main loop            : 0.43
% 3.39/1.69  Inferencing          : 0.15
% 3.39/1.69  Reduction            : 0.15
% 3.39/1.69  Demodulation         : 0.11
% 3.39/1.69  BG Simplification    : 0.02
% 3.39/1.69  Subsumption          : 0.07
% 3.39/1.69  Abstraction          : 0.02
% 3.39/1.69  MUC search           : 0.00
% 3.39/1.69  Cooper               : 0.00
% 3.39/1.69  Total                : 0.83
% 3.39/1.69  Index Insertion      : 0.00
% 3.39/1.69  Index Deletion       : 0.00
% 3.39/1.69  Index Matching       : 0.00
% 3.39/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
