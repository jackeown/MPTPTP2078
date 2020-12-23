%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:53 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 180 expanded)
%              Number of leaves         :   38 (  79 expanded)
%              Depth                    :    8
%              Number of atoms          :  150 ( 486 expanded)
%              Number of equality atoms :   34 (  95 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
             => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_101,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_77,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_226,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_239,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_226])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_244,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_42])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_98,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_104,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_98])).

tff(c_113,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_104])).

tff(c_107,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_98])).

tff(c_116,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_107])).

tff(c_132,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_144,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_132])).

tff(c_40,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_20])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_478,plain,(
    ! [A_121,B_119,D_118,C_123,F_122,E_120] :
      ( k1_partfun1(A_121,B_119,C_123,D_118,E_120,F_122) = k5_relat_1(E_120,F_122)
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_123,D_118)))
      | ~ v1_funct_1(F_122)
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_119)))
      | ~ v1_funct_1(E_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_484,plain,(
    ! [A_121,B_119,E_120] :
      ( k1_partfun1(A_121,B_119,'#skF_1','#skF_2',E_120,'#skF_3') = k5_relat_1(E_120,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_119)))
      | ~ v1_funct_1(E_120) ) ),
    inference(resolution,[status(thm)],[c_52,c_478])).

tff(c_520,plain,(
    ! [A_128,B_129,E_130] :
      ( k1_partfun1(A_128,B_129,'#skF_1','#skF_2',E_130,'#skF_3') = k5_relat_1(E_130,'#skF_3')
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_484])).

tff(c_526,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_520])).

tff(c_533,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_526])).

tff(c_32,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_57,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32])).

tff(c_44,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_303,plain,(
    ! [D_84,C_85,A_86,B_87] :
      ( D_84 = C_85
      | ~ r2_relset_1(A_86,B_87,C_85,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_311,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_44,c_303])).

tff(c_326,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_311])).

tff(c_340,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_326])).

tff(c_538,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_340])).

tff(c_544,plain,(
    ! [F_134,A_132,C_133,D_131,E_136,B_135] :
      ( m1_subset_1(k1_partfun1(A_132,B_135,C_133,D_131,E_136,F_134),k1_zfmisc_1(k2_zfmisc_1(A_132,D_131)))
      | ~ m1_subset_1(F_134,k1_zfmisc_1(k2_zfmisc_1(C_133,D_131)))
      | ~ v1_funct_1(F_134)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_132,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_577,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_544])).

tff(c_598,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_56,c_52,c_577])).

tff(c_608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_538,c_598])).

tff(c_609,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_326])).

tff(c_755,plain,(
    ! [D_161,C_166,E_163,F_165,A_164,B_162] :
      ( k1_partfun1(A_164,B_162,C_166,D_161,E_163,F_165) = k5_relat_1(E_163,F_165)
      | ~ m1_subset_1(F_165,k1_zfmisc_1(k2_zfmisc_1(C_166,D_161)))
      | ~ v1_funct_1(F_165)
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_162)))
      | ~ v1_funct_1(E_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_761,plain,(
    ! [A_164,B_162,E_163] :
      ( k1_partfun1(A_164,B_162,'#skF_1','#skF_2',E_163,'#skF_3') = k5_relat_1(E_163,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_162)))
      | ~ v1_funct_1(E_163) ) ),
    inference(resolution,[status(thm)],[c_52,c_755])).

tff(c_809,plain,(
    ! [A_171,B_172,E_173] :
      ( k1_partfun1(A_171,B_172,'#skF_1','#skF_2',E_173,'#skF_3') = k5_relat_1(E_173,'#skF_3')
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_1(E_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_761])).

tff(c_815,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_809])).

tff(c_822,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_609,c_815])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_10,B_12)),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_145,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k2_relat_1(B_58),A_59)
      | ~ v5_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_258,plain,(
    ! [B_80,A_81] :
      ( k2_relat_1(B_80) = A_81
      | ~ r1_tarski(A_81,k2_relat_1(B_80))
      | ~ v5_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_145,c_2])).

tff(c_278,plain,(
    ! [A_10,B_12] :
      ( k2_relat_1(k5_relat_1(A_10,B_12)) = k2_relat_1(B_12)
      | ~ v5_relat_1(B_12,k2_relat_1(k5_relat_1(A_10,B_12)))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_258])).

tff(c_896,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_3')) = k2_relat_1('#skF_3')
    | ~ v5_relat_1('#skF_3',k2_relat_1(k6_partfun1('#skF_2')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_278])).

tff(c_909,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_116,c_144,c_58,c_58,c_822,c_896])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:23:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.52  
% 3.08/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.52  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.08/1.52  
% 3.08/1.52  %Foreground sorts:
% 3.08/1.52  
% 3.08/1.52  
% 3.08/1.52  %Background operators:
% 3.08/1.52  
% 3.08/1.52  
% 3.08/1.52  %Foreground operators:
% 3.08/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.08/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.08/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.52  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.08/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.08/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.08/1.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.08/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.08/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.08/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.52  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.08/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.08/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.08/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.52  
% 3.08/1.54  tff(f_119, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 3.08/1.54  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.08/1.54  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.08/1.54  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.08/1.54  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.08/1.54  tff(f_101, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.08/1.54  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.08/1.54  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.08/1.54  tff(f_77, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.08/1.54  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.08/1.54  tff(f_89, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.08/1.54  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.08/1.54  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.08/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.08/1.54  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.08/1.54  tff(c_226, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.08/1.54  tff(c_239, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_226])).
% 3.08/1.54  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.08/1.54  tff(c_244, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_42])).
% 3.08/1.54  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.08/1.54  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.08/1.54  tff(c_98, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.08/1.54  tff(c_104, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_98])).
% 3.08/1.54  tff(c_113, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_104])).
% 3.08/1.54  tff(c_107, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_98])).
% 3.08/1.54  tff(c_116, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_107])).
% 3.08/1.54  tff(c_132, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.08/1.54  tff(c_144, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_132])).
% 3.08/1.54  tff(c_40, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.08/1.54  tff(c_20, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.08/1.54  tff(c_58, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_20])).
% 3.08/1.54  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.08/1.54  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.08/1.54  tff(c_478, plain, (![A_121, B_119, D_118, C_123, F_122, E_120]: (k1_partfun1(A_121, B_119, C_123, D_118, E_120, F_122)=k5_relat_1(E_120, F_122) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_123, D_118))) | ~v1_funct_1(F_122) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_119))) | ~v1_funct_1(E_120))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.08/1.54  tff(c_484, plain, (![A_121, B_119, E_120]: (k1_partfun1(A_121, B_119, '#skF_1', '#skF_2', E_120, '#skF_3')=k5_relat_1(E_120, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_119))) | ~v1_funct_1(E_120))), inference(resolution, [status(thm)], [c_52, c_478])).
% 3.08/1.54  tff(c_520, plain, (![A_128, B_129, E_130]: (k1_partfun1(A_128, B_129, '#skF_1', '#skF_2', E_130, '#skF_3')=k5_relat_1(E_130, '#skF_3') | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_1(E_130))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_484])).
% 3.08/1.54  tff(c_526, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_520])).
% 3.08/1.54  tff(c_533, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_526])).
% 3.08/1.54  tff(c_32, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.08/1.54  tff(c_57, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32])).
% 3.08/1.54  tff(c_44, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.08/1.54  tff(c_303, plain, (![D_84, C_85, A_86, B_87]: (D_84=C_85 | ~r2_relset_1(A_86, B_87, C_85, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.08/1.54  tff(c_311, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_44, c_303])).
% 3.08/1.54  tff(c_326, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_311])).
% 3.08/1.54  tff(c_340, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_326])).
% 3.08/1.54  tff(c_538, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_340])).
% 3.08/1.54  tff(c_544, plain, (![F_134, A_132, C_133, D_131, E_136, B_135]: (m1_subset_1(k1_partfun1(A_132, B_135, C_133, D_131, E_136, F_134), k1_zfmisc_1(k2_zfmisc_1(A_132, D_131))) | ~m1_subset_1(F_134, k1_zfmisc_1(k2_zfmisc_1(C_133, D_131))) | ~v1_funct_1(F_134) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_132, B_135))) | ~v1_funct_1(E_136))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.08/1.54  tff(c_577, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_533, c_544])).
% 3.08/1.54  tff(c_598, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_56, c_52, c_577])).
% 3.08/1.54  tff(c_608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_538, c_598])).
% 3.08/1.54  tff(c_609, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_326])).
% 3.08/1.54  tff(c_755, plain, (![D_161, C_166, E_163, F_165, A_164, B_162]: (k1_partfun1(A_164, B_162, C_166, D_161, E_163, F_165)=k5_relat_1(E_163, F_165) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(C_166, D_161))) | ~v1_funct_1(F_165) | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_162))) | ~v1_funct_1(E_163))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.08/1.54  tff(c_761, plain, (![A_164, B_162, E_163]: (k1_partfun1(A_164, B_162, '#skF_1', '#skF_2', E_163, '#skF_3')=k5_relat_1(E_163, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_162))) | ~v1_funct_1(E_163))), inference(resolution, [status(thm)], [c_52, c_755])).
% 3.08/1.54  tff(c_809, plain, (![A_171, B_172, E_173]: (k1_partfun1(A_171, B_172, '#skF_1', '#skF_2', E_173, '#skF_3')=k5_relat_1(E_173, '#skF_3') | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_1(E_173))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_761])).
% 3.08/1.54  tff(c_815, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_809])).
% 3.08/1.54  tff(c_822, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_609, c_815])).
% 3.08/1.54  tff(c_16, plain, (![A_10, B_12]: (r1_tarski(k2_relat_1(k5_relat_1(A_10, B_12)), k2_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.08/1.54  tff(c_145, plain, (![B_58, A_59]: (r1_tarski(k2_relat_1(B_58), A_59) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.08/1.54  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.54  tff(c_258, plain, (![B_80, A_81]: (k2_relat_1(B_80)=A_81 | ~r1_tarski(A_81, k2_relat_1(B_80)) | ~v5_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_145, c_2])).
% 3.08/1.54  tff(c_278, plain, (![A_10, B_12]: (k2_relat_1(k5_relat_1(A_10, B_12))=k2_relat_1(B_12) | ~v5_relat_1(B_12, k2_relat_1(k5_relat_1(A_10, B_12))) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_16, c_258])).
% 3.08/1.54  tff(c_896, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', k2_relat_1(k6_partfun1('#skF_2'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_822, c_278])).
% 3.08/1.54  tff(c_909, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_116, c_144, c_58, c_58, c_822, c_896])).
% 3.08/1.54  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_909])).
% 3.08/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.54  
% 3.08/1.54  Inference rules
% 3.08/1.54  ----------------------
% 3.08/1.54  #Ref     : 0
% 3.08/1.54  #Sup     : 176
% 3.08/1.54  #Fact    : 0
% 3.08/1.54  #Define  : 0
% 3.08/1.54  #Split   : 1
% 3.08/1.54  #Chain   : 0
% 3.08/1.54  #Close   : 0
% 3.08/1.54  
% 3.08/1.54  Ordering : KBO
% 3.08/1.54  
% 3.08/1.54  Simplification rules
% 3.08/1.54  ----------------------
% 3.08/1.54  #Subsume      : 14
% 3.08/1.54  #Demod        : 156
% 3.08/1.54  #Tautology    : 55
% 3.08/1.54  #SimpNegUnit  : 3
% 3.08/1.54  #BackRed      : 9
% 3.08/1.54  
% 3.08/1.54  #Partial instantiations: 0
% 3.08/1.54  #Strategies tried      : 1
% 3.08/1.54  
% 3.08/1.54  Timing (in seconds)
% 3.08/1.54  ----------------------
% 3.41/1.54  Preprocessing        : 0.31
% 3.41/1.54  Parsing              : 0.16
% 3.41/1.54  CNF conversion       : 0.02
% 3.41/1.54  Main loop            : 0.40
% 3.41/1.54  Inferencing          : 0.15
% 3.41/1.54  Reduction            : 0.13
% 3.41/1.54  Demodulation         : 0.09
% 3.41/1.54  BG Simplification    : 0.02
% 3.41/1.54  Subsumption          : 0.07
% 3.41/1.54  Abstraction          : 0.02
% 3.41/1.54  MUC search           : 0.00
% 3.41/1.54  Cooper               : 0.00
% 3.41/1.55  Total                : 0.75
% 3.41/1.55  Index Insertion      : 0.00
% 3.41/1.55  Index Deletion       : 0.00
% 3.41/1.55  Index Matching       : 0.00
% 3.41/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
