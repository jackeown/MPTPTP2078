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
% DateTime   : Thu Dec  3 10:17:39 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 540 expanded)
%              Number of leaves         :   38 ( 191 expanded)
%              Depth                    :   11
%              Number of atoms          :  234 (1726 expanded)
%              Number of equality atoms :   61 ( 243 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( k1_relset_1(A,B,C) = A
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_598,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k2_partfun1(A_132,B_133,C_134,D_135) = k7_relat_1(C_134,D_135)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_602,plain,(
    ! [D_135] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_135) = k7_relat_1('#skF_5',D_135)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_598])).

tff(c_608,plain,(
    ! [D_135] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_135) = k7_relat_1('#skF_5',D_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_602])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_104])).

tff(c_110,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_107])).

tff(c_146,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k7_relset_1(A_74,B_75,C_76,D_77) = k9_relat_1(C_76,D_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_149,plain,(
    ! [D_77] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_77) = k9_relat_1('#skF_5',D_77) ),
    inference(resolution,[status(thm)],[c_50,c_146])).

tff(c_46,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_151,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_46])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_126,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_130,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_126])).

tff(c_229,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_xboole_0 = B_92
      | k1_relset_1(A_93,B_92,C_94) = A_93
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_235,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_229])).

tff(c_239,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_130,c_235])).

tff(c_240,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k1_relat_1(k7_relat_1(B_11,A_10)) = A_10
      | ~ r1_tarski(A_10,k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_245,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_12])).

tff(c_255,plain,(
    ! [A_95] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_95)) = A_95
      | ~ r1_tarski(A_95,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_245])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_264,plain,(
    ! [A_95] :
      ( r1_tarski(A_95,A_95)
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski(A_95,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_10])).

tff(c_272,plain,(
    ! [A_96] :
      ( r1_tarski(A_96,A_96)
      | ~ r1_tarski(A_96,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_264])).

tff(c_279,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_272])).

tff(c_249,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_245])).

tff(c_203,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k2_partfun1(A_86,B_87,C_88,D_89) = k7_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_207,plain,(
    ! [D_89] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_89) = k7_relat_1('#skF_5',D_89)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_203])).

tff(c_211,plain,(
    ! [D_89] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_89) = k7_relat_1('#skF_5',D_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_207])).

tff(c_417,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( m1_subset_1(k2_partfun1(A_110,B_111,C_112,D_113),k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_453,plain,(
    ! [D_89] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_89),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_417])).

tff(c_469,plain,(
    ! [D_114] : m1_subset_1(k7_relat_1('#skF_5',D_114),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_453])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_490,plain,(
    ! [D_114] :
      ( v1_relat_1(k7_relat_1('#skF_5',D_114))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_469,c_4])).

tff(c_506,plain,(
    ! [D_114] : v1_relat_1(k7_relat_1('#skF_5',D_114)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_490])).

tff(c_162,plain,(
    ! [C_83,A_84,B_85] :
      ( m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ r1_tarski(k2_relat_1(C_83),B_85)
      | ~ r1_tarski(k1_relat_1(C_83),A_84)
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_93,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( v1_funct_1(k2_partfun1(A_53,B_54,C_55,D_56))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_95,plain,(
    ! [D_56] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_56))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_93])).

tff(c_98,plain,(
    ! [D_56] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_95])).

tff(c_44,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_59,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_59])).

tff(c_102,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_136,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_197,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_162,c_136])).

tff(c_312,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_211,c_211,c_197])).

tff(c_313,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_313])).

tff(c_511,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_18,plain,(
    ! [C_21,A_19,B_20] :
      ( m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ r1_tarski(k2_relat_1(C_21),B_20)
      | ~ r1_tarski(k1_relat_1(C_21),A_19)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_213,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_136])).

tff(c_227,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_213])).

tff(c_513,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_227])).

tff(c_514,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_517,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_514])).

tff(c_523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_279,c_517])).

tff(c_524,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_533,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_524])).

tff(c_536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_151,c_533])).

tff(c_537,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_545,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_2])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_545])).

tff(c_548,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_614,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_548])).

tff(c_577,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( v1_funct_1(k2_partfun1(A_120,B_121,C_122,D_123))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_581,plain,(
    ! [D_123] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_123))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_577])).

tff(c_587,plain,(
    ! [D_123] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_123)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_581])).

tff(c_611,plain,(
    ! [D_123] : v1_funct_1(k7_relat_1('#skF_5',D_123)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_587])).

tff(c_755,plain,(
    ! [B_154,A_155,C_156] :
      ( k1_xboole_0 = B_154
      | k1_relset_1(A_155,B_154,C_156) = A_155
      | ~ v1_funct_2(C_156,A_155,B_154)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_155,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_764,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_755])).

tff(c_771,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_130,c_764])).

tff(c_772,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_771])).

tff(c_777,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_12])).

tff(c_787,plain,(
    ! [A_157] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_157)) = A_157
      | ~ r1_tarski(A_157,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_777])).

tff(c_549,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] :
      ( k1_relset_1(A_12,B_13,C_14) = k1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_556,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_549,c_14])).

tff(c_609,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_608,c_556])).

tff(c_613,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_549])).

tff(c_720,plain,(
    ! [B_148,C_149,A_150] :
      ( k1_xboole_0 = B_148
      | v1_funct_2(C_149,A_150,B_148)
      | k1_relset_1(A_150,B_148,C_149) != A_150
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_726,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_613,c_720])).

tff(c_732,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_726])).

tff(c_733,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_614,c_732])).

tff(c_736,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_733])).

tff(c_793,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_736])).

tff(c_807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_793])).

tff(c_808,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_817,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_2])).

tff(c_819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_817])).

tff(c_821,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_733])).

tff(c_862,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_609])).

tff(c_885,plain,(
    ! [C_161,A_162,B_163] :
      ( v1_funct_2(C_161,A_162,B_163)
      | k1_relset_1(A_162,B_163,C_161) != A_162
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ v1_funct_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_891,plain,
    ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2'
    | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_613,c_885])).

tff(c_898,plain,(
    v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_862,c_891])).

tff(c_900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_614,c_898])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.44  
% 2.96/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.45  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.96/1.45  
% 2.96/1.45  %Foreground sorts:
% 2.96/1.45  
% 2.96/1.45  
% 2.96/1.45  %Background operators:
% 2.96/1.45  
% 2.96/1.45  
% 2.96/1.45  %Foreground operators:
% 2.96/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.96/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.96/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.96/1.45  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.96/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.96/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.96/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.96/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.96/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.96/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.45  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.96/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.96/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.96/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.45  
% 3.27/1.47  tff(f_130, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 3.27/1.47  tff(f_97, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.27/1.47  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.27/1.47  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.27/1.47  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.27/1.47  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.27/1.47  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.27/1.47  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.27/1.47  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.27/1.47  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.27/1.47  tff(f_91, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 3.27/1.47  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.27/1.47  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.27/1.47  tff(f_109, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 3.27/1.47  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.27/1.47  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.27/1.47  tff(c_598, plain, (![A_132, B_133, C_134, D_135]: (k2_partfun1(A_132, B_133, C_134, D_135)=k7_relat_1(C_134, D_135) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_1(C_134))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.27/1.47  tff(c_602, plain, (![D_135]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_135)=k7_relat_1('#skF_5', D_135) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_598])).
% 3.27/1.47  tff(c_608, plain, (![D_135]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_135)=k7_relat_1('#skF_5', D_135))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_602])).
% 3.27/1.47  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.27/1.47  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.47  tff(c_104, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.47  tff(c_107, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_104])).
% 3.27/1.47  tff(c_110, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_107])).
% 3.27/1.47  tff(c_146, plain, (![A_74, B_75, C_76, D_77]: (k7_relset_1(A_74, B_75, C_76, D_77)=k9_relat_1(C_76, D_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.27/1.47  tff(c_149, plain, (![D_77]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_77)=k9_relat_1('#skF_5', D_77))), inference(resolution, [status(thm)], [c_50, c_146])).
% 3.27/1.47  tff(c_46, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.27/1.47  tff(c_151, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_46])).
% 3.27/1.47  tff(c_8, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.27/1.47  tff(c_48, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.27/1.47  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.27/1.47  tff(c_126, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.27/1.47  tff(c_130, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_126])).
% 3.27/1.47  tff(c_229, plain, (![B_92, A_93, C_94]: (k1_xboole_0=B_92 | k1_relset_1(A_93, B_92, C_94)=A_93 | ~v1_funct_2(C_94, A_93, B_92) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.27/1.47  tff(c_235, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_229])).
% 3.27/1.47  tff(c_239, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_130, c_235])).
% 3.27/1.47  tff(c_240, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_239])).
% 3.27/1.47  tff(c_12, plain, (![B_11, A_10]: (k1_relat_1(k7_relat_1(B_11, A_10))=A_10 | ~r1_tarski(A_10, k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.27/1.47  tff(c_245, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_5', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_240, c_12])).
% 3.27/1.47  tff(c_255, plain, (![A_95]: (k1_relat_1(k7_relat_1('#skF_5', A_95))=A_95 | ~r1_tarski(A_95, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_245])).
% 3.27/1.47  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.47  tff(c_264, plain, (![A_95]: (r1_tarski(A_95, A_95) | ~v1_relat_1('#skF_5') | ~r1_tarski(A_95, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_10])).
% 3.27/1.47  tff(c_272, plain, (![A_96]: (r1_tarski(A_96, A_96) | ~r1_tarski(A_96, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_264])).
% 3.27/1.47  tff(c_279, plain, (r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_272])).
% 3.27/1.47  tff(c_249, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_5', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_245])).
% 3.27/1.47  tff(c_203, plain, (![A_86, B_87, C_88, D_89]: (k2_partfun1(A_86, B_87, C_88, D_89)=k7_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.27/1.47  tff(c_207, plain, (![D_89]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_89)=k7_relat_1('#skF_5', D_89) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_203])).
% 3.27/1.47  tff(c_211, plain, (![D_89]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_89)=k7_relat_1('#skF_5', D_89))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_207])).
% 3.27/1.47  tff(c_417, plain, (![A_110, B_111, C_112, D_113]: (m1_subset_1(k2_partfun1(A_110, B_111, C_112, D_113), k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(C_112))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.27/1.47  tff(c_453, plain, (![D_89]: (m1_subset_1(k7_relat_1('#skF_5', D_89), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_211, c_417])).
% 3.27/1.47  tff(c_469, plain, (![D_114]: (m1_subset_1(k7_relat_1('#skF_5', D_114), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_453])).
% 3.27/1.47  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.47  tff(c_490, plain, (![D_114]: (v1_relat_1(k7_relat_1('#skF_5', D_114)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(resolution, [status(thm)], [c_469, c_4])).
% 3.27/1.47  tff(c_506, plain, (![D_114]: (v1_relat_1(k7_relat_1('#skF_5', D_114)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_490])).
% 3.27/1.47  tff(c_162, plain, (![C_83, A_84, B_85]: (m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~r1_tarski(k2_relat_1(C_83), B_85) | ~r1_tarski(k1_relat_1(C_83), A_84) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.47  tff(c_93, plain, (![A_53, B_54, C_55, D_56]: (v1_funct_1(k2_partfun1(A_53, B_54, C_55, D_56)) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_1(C_55))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.27/1.47  tff(c_95, plain, (![D_56]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_56)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_93])).
% 3.27/1.47  tff(c_98, plain, (![D_56]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_56)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_95])).
% 3.27/1.47  tff(c_44, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.27/1.47  tff(c_59, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.27/1.47  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_59])).
% 3.27/1.47  tff(c_102, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_44])).
% 3.27/1.47  tff(c_136, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_102])).
% 3.27/1.47  tff(c_197, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_162, c_136])).
% 3.27/1.47  tff(c_312, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_211, c_211, c_197])).
% 3.27/1.47  tff(c_313, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_312])).
% 3.27/1.47  tff(c_509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_506, c_313])).
% 3.27/1.47  tff(c_511, plain, (v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitRight, [status(thm)], [c_312])).
% 3.27/1.47  tff(c_18, plain, (![C_21, A_19, B_20]: (m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~r1_tarski(k2_relat_1(C_21), B_20) | ~r1_tarski(k1_relat_1(C_21), A_19) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.47  tff(c_213, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_136])).
% 3.27/1.47  tff(c_227, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_213])).
% 3.27/1.47  tff(c_513, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_511, c_227])).
% 3.27/1.47  tff(c_514, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_513])).
% 3.27/1.47  tff(c_517, plain, (~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_249, c_514])).
% 3.27/1.47  tff(c_523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_279, c_517])).
% 3.27/1.47  tff(c_524, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_513])).
% 3.27/1.47  tff(c_533, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8, c_524])).
% 3.27/1.47  tff(c_536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_151, c_533])).
% 3.27/1.47  tff(c_537, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_239])).
% 3.27/1.47  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.27/1.47  tff(c_545, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_537, c_2])).
% 3.27/1.47  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_545])).
% 3.27/1.47  tff(c_548, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_102])).
% 3.27/1.47  tff(c_614, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_608, c_548])).
% 3.27/1.47  tff(c_577, plain, (![A_120, B_121, C_122, D_123]: (v1_funct_1(k2_partfun1(A_120, B_121, C_122, D_123)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(C_122))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.27/1.47  tff(c_581, plain, (![D_123]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_123)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_577])).
% 3.27/1.47  tff(c_587, plain, (![D_123]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_123)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_581])).
% 3.27/1.47  tff(c_611, plain, (![D_123]: (v1_funct_1(k7_relat_1('#skF_5', D_123)))), inference(demodulation, [status(thm), theory('equality')], [c_608, c_587])).
% 3.27/1.47  tff(c_755, plain, (![B_154, A_155, C_156]: (k1_xboole_0=B_154 | k1_relset_1(A_155, B_154, C_156)=A_155 | ~v1_funct_2(C_156, A_155, B_154) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.27/1.47  tff(c_764, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_755])).
% 3.27/1.47  tff(c_771, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_130, c_764])).
% 3.27/1.47  tff(c_772, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_771])).
% 3.27/1.47  tff(c_777, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_5', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_772, c_12])).
% 3.27/1.47  tff(c_787, plain, (![A_157]: (k1_relat_1(k7_relat_1('#skF_5', A_157))=A_157 | ~r1_tarski(A_157, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_777])).
% 3.27/1.47  tff(c_549, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_102])).
% 3.27/1.47  tff(c_14, plain, (![A_12, B_13, C_14]: (k1_relset_1(A_12, B_13, C_14)=k1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.27/1.47  tff(c_556, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_549, c_14])).
% 3.27/1.47  tff(c_609, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_608, c_608, c_556])).
% 3.27/1.47  tff(c_613, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_608, c_549])).
% 3.27/1.47  tff(c_720, plain, (![B_148, C_149, A_150]: (k1_xboole_0=B_148 | v1_funct_2(C_149, A_150, B_148) | k1_relset_1(A_150, B_148, C_149)!=A_150 | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_148))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.27/1.47  tff(c_726, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_613, c_720])).
% 3.27/1.47  tff(c_732, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_609, c_726])).
% 3.27/1.47  tff(c_733, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_614, c_732])).
% 3.27/1.47  tff(c_736, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_733])).
% 3.27/1.47  tff(c_793, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_787, c_736])).
% 3.27/1.47  tff(c_807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_793])).
% 3.27/1.47  tff(c_808, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_771])).
% 3.27/1.47  tff(c_817, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_2])).
% 3.27/1.47  tff(c_819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_817])).
% 3.27/1.47  tff(c_821, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(splitRight, [status(thm)], [c_733])).
% 3.27/1.47  tff(c_862, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_821, c_609])).
% 3.27/1.47  tff(c_885, plain, (![C_161, A_162, B_163]: (v1_funct_2(C_161, A_162, B_163) | k1_relset_1(A_162, B_163, C_161)!=A_162 | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~v1_funct_1(C_161))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.27/1.47  tff(c_891, plain, (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2' | ~v1_funct_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_613, c_885])).
% 3.27/1.47  tff(c_898, plain, (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_862, c_891])).
% 3.27/1.47  tff(c_900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_614, c_898])).
% 3.27/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.47  
% 3.27/1.47  Inference rules
% 3.27/1.47  ----------------------
% 3.27/1.47  #Ref     : 0
% 3.27/1.47  #Sup     : 173
% 3.27/1.47  #Fact    : 0
% 3.27/1.47  #Define  : 0
% 3.27/1.47  #Split   : 11
% 3.27/1.47  #Chain   : 0
% 3.27/1.47  #Close   : 0
% 3.27/1.47  
% 3.27/1.47  Ordering : KBO
% 3.27/1.47  
% 3.27/1.47  Simplification rules
% 3.27/1.47  ----------------------
% 3.27/1.47  #Subsume      : 7
% 3.27/1.47  #Demod        : 170
% 3.27/1.47  #Tautology    : 69
% 3.27/1.47  #SimpNegUnit  : 6
% 3.27/1.47  #BackRed      : 40
% 3.27/1.47  
% 3.27/1.47  #Partial instantiations: 0
% 3.27/1.47  #Strategies tried      : 1
% 3.27/1.47  
% 3.27/1.47  Timing (in seconds)
% 3.27/1.47  ----------------------
% 3.27/1.47  Preprocessing        : 0.33
% 3.27/1.47  Parsing              : 0.17
% 3.27/1.47  CNF conversion       : 0.02
% 3.27/1.47  Main loop            : 0.36
% 3.27/1.47  Inferencing          : 0.13
% 3.27/1.47  Reduction            : 0.12
% 3.27/1.47  Demodulation         : 0.09
% 3.27/1.47  BG Simplification    : 0.02
% 3.27/1.47  Subsumption          : 0.06
% 3.27/1.47  Abstraction          : 0.02
% 3.27/1.47  MUC search           : 0.00
% 3.27/1.47  Cooper               : 0.00
% 3.27/1.47  Total                : 0.74
% 3.27/1.47  Index Insertion      : 0.00
% 3.27/1.47  Index Deletion       : 0.00
% 3.27/1.47  Index Matching       : 0.00
% 3.27/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
