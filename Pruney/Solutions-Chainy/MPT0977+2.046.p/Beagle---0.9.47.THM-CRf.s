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
% DateTime   : Thu Dec  3 10:11:51 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 138 expanded)
%              Number of leaves         :   38 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 221 expanded)
%              Number of equality atoms :   26 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_943,plain,(
    ! [A_180,B_181,C_182,D_183] :
      ( r2_relset_1(A_180,B_181,C_182,C_182)
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_967,plain,(
    ! [C_188] :
      ( r2_relset_1('#skF_1','#skF_2',C_188,C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_943])).

tff(c_982,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_967])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_592,plain,(
    ! [B_127,A_128] :
      ( v1_relat_1(B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_128))
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_601,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_592])).

tff(c_608,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_601])).

tff(c_794,plain,(
    ! [A_162,B_163,C_164] :
      ( k2_relset_1(A_162,B_163,C_164) = k2_relat_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_807,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_794])).

tff(c_840,plain,(
    ! [A_174,B_175,C_176] :
      ( m1_subset_1(k2_relset_1(A_174,B_175,C_176),k1_zfmisc_1(B_175))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_864,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_840])).

tff(c_873,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_864])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_881,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_873,c_2])).

tff(c_34,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_39,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_partfun1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_884,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_881,c_39])).

tff(c_890,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_884])).

tff(c_32,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1028,plain,(
    ! [F_196,C_195,E_198,A_194,D_193,B_197] :
      ( k4_relset_1(A_194,B_197,C_195,D_193,E_198,F_196) = k5_relat_1(E_198,F_196)
      | ~ m1_subset_1(F_196,k1_zfmisc_1(k2_zfmisc_1(C_195,D_193)))
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_194,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1696,plain,(
    ! [A_296,B_297,A_298,E_299] :
      ( k4_relset_1(A_296,B_297,A_298,A_298,E_299,k6_partfun1(A_298)) = k5_relat_1(E_299,k6_partfun1(A_298))
      | ~ m1_subset_1(E_299,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297))) ) ),
    inference(resolution,[status(thm)],[c_32,c_1028])).

tff(c_1718,plain,(
    ! [A_298] : k4_relset_1('#skF_1','#skF_2',A_298,A_298,'#skF_3',k6_partfun1(A_298)) = k5_relat_1('#skF_3',k6_partfun1(A_298)) ),
    inference(resolution,[status(thm)],[c_38,c_1696])).

tff(c_315,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( r2_relset_1(A_84,B_85,C_86,C_86)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_377,plain,(
    ! [C_90] :
      ( r2_relset_1('#skF_1','#skF_2',C_90,C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_315])).

tff(c_392,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_377])).

tff(c_69,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_78,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_85,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_137,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_150,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_137])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_153,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_10])).

tff(c_156,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_153])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_15,A_14)),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_167,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_16])).

tff(c_171,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_167])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_223,plain,(
    ! [A_77,B_78] :
      ( k5_relat_1(k6_partfun1(A_77),B_78) = B_78
      | ~ r1_tarski(k1_relat_1(B_78),A_77)
      | ~ v1_relat_1(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_229,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_171,c_223])).

tff(c_238,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_229])).

tff(c_400,plain,(
    ! [D_96,B_100,E_101,C_98,F_99,A_97] :
      ( k4_relset_1(A_97,B_100,C_98,D_96,E_101,F_99) = k5_relat_1(E_101,F_99)
      | ~ m1_subset_1(F_99,k1_zfmisc_1(k2_zfmisc_1(C_98,D_96)))
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_97,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_452,plain,(
    ! [A_107,B_108,E_109] :
      ( k4_relset_1(A_107,B_108,'#skF_1','#skF_2',E_109,'#skF_3') = k5_relat_1(E_109,'#skF_3')
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(resolution,[status(thm)],[c_38,c_400])).

tff(c_474,plain,(
    ! [A_35] : k4_relset_1(A_35,A_35,'#skF_1','#skF_2',k6_partfun1(A_35),'#skF_3') = k5_relat_1(k6_partfun1(A_35),'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_452])).

tff(c_36,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_68,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_586,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_68])).

tff(c_589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_238,c_586])).

tff(c_590,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1719,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_590])).

tff(c_1722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_890,c_1719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.58  
% 3.53/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.58  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.53/1.58  
% 3.53/1.58  %Foreground sorts:
% 3.53/1.58  
% 3.53/1.58  
% 3.53/1.58  %Background operators:
% 3.53/1.58  
% 3.53/1.58  
% 3.53/1.58  %Foreground operators:
% 3.53/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.53/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.58  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.53/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.53/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.53/1.58  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.58  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.53/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.53/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.58  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.53/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.53/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.53/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.58  
% 3.53/1.60  tff(f_99, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 3.53/1.60  tff(f_86, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.53/1.60  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.53/1.60  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.53/1.60  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.53/1.60  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.53/1.60  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.53/1.60  tff(f_92, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.53/1.60  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.53/1.60  tff(f_90, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.53/1.60  tff(f_80, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.53/1.60  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.53/1.60  tff(f_44, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.53/1.60  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.53/1.60  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 3.53/1.60  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.53/1.60  tff(c_943, plain, (![A_180, B_181, C_182, D_183]: (r2_relset_1(A_180, B_181, C_182, C_182) | ~m1_subset_1(D_183, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.53/1.60  tff(c_967, plain, (![C_188]: (r2_relset_1('#skF_1', '#skF_2', C_188, C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_38, c_943])).
% 3.53/1.60  tff(c_982, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_967])).
% 3.53/1.60  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.53/1.60  tff(c_592, plain, (![B_127, A_128]: (v1_relat_1(B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(A_128)) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.53/1.60  tff(c_601, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_592])).
% 3.53/1.60  tff(c_608, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_601])).
% 3.53/1.60  tff(c_794, plain, (![A_162, B_163, C_164]: (k2_relset_1(A_162, B_163, C_164)=k2_relat_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.53/1.60  tff(c_807, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_794])).
% 3.53/1.60  tff(c_840, plain, (![A_174, B_175, C_176]: (m1_subset_1(k2_relset_1(A_174, B_175, C_176), k1_zfmisc_1(B_175)) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.53/1.60  tff(c_864, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_807, c_840])).
% 3.53/1.60  tff(c_873, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_864])).
% 3.53/1.60  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.53/1.60  tff(c_881, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_873, c_2])).
% 3.53/1.60  tff(c_34, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.53/1.60  tff(c_14, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.53/1.60  tff(c_39, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_partfun1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 3.53/1.60  tff(c_884, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_881, c_39])).
% 3.53/1.60  tff(c_890, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_608, c_884])).
% 3.53/1.60  tff(c_32, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.53/1.60  tff(c_1028, plain, (![F_196, C_195, E_198, A_194, D_193, B_197]: (k4_relset_1(A_194, B_197, C_195, D_193, E_198, F_196)=k5_relat_1(E_198, F_196) | ~m1_subset_1(F_196, k1_zfmisc_1(k2_zfmisc_1(C_195, D_193))) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_194, B_197))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.53/1.60  tff(c_1696, plain, (![A_296, B_297, A_298, E_299]: (k4_relset_1(A_296, B_297, A_298, A_298, E_299, k6_partfun1(A_298))=k5_relat_1(E_299, k6_partfun1(A_298)) | ~m1_subset_1(E_299, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))))), inference(resolution, [status(thm)], [c_32, c_1028])).
% 3.53/1.60  tff(c_1718, plain, (![A_298]: (k4_relset_1('#skF_1', '#skF_2', A_298, A_298, '#skF_3', k6_partfun1(A_298))=k5_relat_1('#skF_3', k6_partfun1(A_298)))), inference(resolution, [status(thm)], [c_38, c_1696])).
% 3.53/1.60  tff(c_315, plain, (![A_84, B_85, C_86, D_87]: (r2_relset_1(A_84, B_85, C_86, C_86) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.53/1.60  tff(c_377, plain, (![C_90]: (r2_relset_1('#skF_1', '#skF_2', C_90, C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_38, c_315])).
% 3.53/1.60  tff(c_392, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_377])).
% 3.53/1.60  tff(c_69, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.53/1.60  tff(c_78, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_69])).
% 3.53/1.60  tff(c_85, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_78])).
% 3.53/1.60  tff(c_137, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.53/1.60  tff(c_150, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_137])).
% 3.53/1.60  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.53/1.60  tff(c_153, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_150, c_10])).
% 3.53/1.60  tff(c_156, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_153])).
% 3.53/1.60  tff(c_16, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(k7_relat_1(B_15, A_14)), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.53/1.60  tff(c_167, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_156, c_16])).
% 3.53/1.60  tff(c_171, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_167])).
% 3.53/1.60  tff(c_12, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.53/1.60  tff(c_223, plain, (![A_77, B_78]: (k5_relat_1(k6_partfun1(A_77), B_78)=B_78 | ~r1_tarski(k1_relat_1(B_78), A_77) | ~v1_relat_1(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12])).
% 3.53/1.60  tff(c_229, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_171, c_223])).
% 3.53/1.60  tff(c_238, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_229])).
% 3.53/1.60  tff(c_400, plain, (![D_96, B_100, E_101, C_98, F_99, A_97]: (k4_relset_1(A_97, B_100, C_98, D_96, E_101, F_99)=k5_relat_1(E_101, F_99) | ~m1_subset_1(F_99, k1_zfmisc_1(k2_zfmisc_1(C_98, D_96))) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_97, B_100))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.53/1.60  tff(c_452, plain, (![A_107, B_108, E_109]: (k4_relset_1(A_107, B_108, '#skF_1', '#skF_2', E_109, '#skF_3')=k5_relat_1(E_109, '#skF_3') | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(resolution, [status(thm)], [c_38, c_400])).
% 3.53/1.60  tff(c_474, plain, (![A_35]: (k4_relset_1(A_35, A_35, '#skF_1', '#skF_2', k6_partfun1(A_35), '#skF_3')=k5_relat_1(k6_partfun1(A_35), '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_452])).
% 3.53/1.60  tff(c_36, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.53/1.60  tff(c_68, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 3.53/1.60  tff(c_586, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_474, c_68])).
% 3.53/1.60  tff(c_589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_392, c_238, c_586])).
% 3.53/1.60  tff(c_590, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 3.53/1.60  tff(c_1719, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_590])).
% 3.53/1.60  tff(c_1722, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_982, c_890, c_1719])).
% 3.53/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.60  
% 3.53/1.60  Inference rules
% 3.53/1.60  ----------------------
% 3.53/1.60  #Ref     : 0
% 3.53/1.60  #Sup     : 349
% 3.53/1.60  #Fact    : 0
% 3.53/1.60  #Define  : 0
% 3.53/1.60  #Split   : 5
% 3.53/1.60  #Chain   : 0
% 3.53/1.60  #Close   : 0
% 3.53/1.60  
% 3.53/1.60  Ordering : KBO
% 3.53/1.60  
% 3.53/1.60  Simplification rules
% 3.53/1.60  ----------------------
% 3.53/1.60  #Subsume      : 26
% 3.53/1.60  #Demod        : 148
% 3.53/1.60  #Tautology    : 110
% 3.53/1.60  #SimpNegUnit  : 0
% 3.53/1.60  #BackRed      : 6
% 3.53/1.60  
% 3.53/1.60  #Partial instantiations: 0
% 3.53/1.60  #Strategies tried      : 1
% 3.53/1.60  
% 3.53/1.60  Timing (in seconds)
% 3.53/1.60  ----------------------
% 3.53/1.60  Preprocessing        : 0.32
% 3.53/1.60  Parsing              : 0.18
% 3.53/1.60  CNF conversion       : 0.02
% 3.53/1.60  Main loop            : 0.52
% 3.53/1.60  Inferencing          : 0.20
% 3.53/1.60  Reduction            : 0.17
% 3.53/1.60  Demodulation         : 0.12
% 3.53/1.60  BG Simplification    : 0.03
% 3.53/1.60  Subsumption          : 0.07
% 3.53/1.61  Abstraction          : 0.03
% 3.53/1.61  MUC search           : 0.00
% 3.53/1.61  Cooper               : 0.00
% 3.53/1.61  Total                : 0.87
% 3.53/1.61  Index Insertion      : 0.00
% 3.53/1.61  Index Deletion       : 0.00
% 3.53/1.61  Index Matching       : 0.00
% 3.53/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
