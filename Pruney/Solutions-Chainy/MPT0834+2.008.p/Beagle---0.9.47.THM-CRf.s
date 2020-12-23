%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:50 EST 2020

% Result     : Theorem 8.63s
% Output     : CNFRefutation 8.63s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 256 expanded)
%              Number of leaves         :   47 ( 104 expanded)
%              Depth                    :   16
%              Number of atoms          :  219 ( 458 expanded)
%              Number of equality atoms :   67 ( 139 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_126,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_100,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3787,plain,(
    ! [A_443,B_444,C_445,D_446] :
      ( k8_relset_1(A_443,B_444,C_445,D_446) = k10_relat_1(C_445,D_446)
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_443,B_444))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3794,plain,(
    ! [D_446] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_446) = k10_relat_1('#skF_3',D_446) ),
    inference(resolution,[status(thm)],[c_64,c_3787])).

tff(c_3127,plain,(
    ! [A_413,B_414,C_415] :
      ( k1_relset_1(A_413,B_414,C_415) = k1_relat_1(C_415)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3136,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_3127])).

tff(c_99,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_108,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_99])).

tff(c_159,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_168,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_159])).

tff(c_191,plain,(
    ! [B_93,A_94] :
      ( k7_relat_1(B_93,A_94) = B_93
      | ~ v4_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_197,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_168,c_191])).

tff(c_206,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_197])).

tff(c_513,plain,(
    ! [B_140,A_141] :
      ( k2_relat_1(k7_relat_1(B_140,A_141)) = k9_relat_1(B_140,A_141)
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_540,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_513])).

tff(c_550,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_540])).

tff(c_1690,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( k7_relset_1(A_244,B_245,C_246,D_247) = k9_relat_1(C_246,D_247)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1697,plain,(
    ! [D_247] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_247) = k9_relat_1('#skF_3',D_247) ),
    inference(resolution,[status(thm)],[c_64,c_1690])).

tff(c_964,plain,(
    ! [A_182,B_183,C_184] :
      ( k2_relset_1(A_182,B_183,C_184) = k2_relat_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_973,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_964])).

tff(c_62,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_93,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_974,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_93])).

tff(c_1698,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1697,c_974])).

tff(c_1701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_1698])).

tff(c_1702,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_3137,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3136,c_1702])).

tff(c_3834,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3794,c_3137])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_88])).

tff(c_1899,plain,(
    ! [A_292,C_293,B_294] :
      ( r1_tarski(A_292,C_293)
      | ~ r1_tarski(B_294,C_293)
      | ~ r1_tarski(A_292,B_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1916,plain,(
    ! [A_292] :
      ( r1_tarski(A_292,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_292,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_92,c_1899])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2176,plain,(
    ! [C_318,B_319,A_320] :
      ( v5_relat_1(C_318,B_319)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_320,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2345,plain,(
    ! [A_336,B_337,A_338] :
      ( v5_relat_1(A_336,B_337)
      | ~ r1_tarski(A_336,k2_zfmisc_1(A_338,B_337)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2176])).

tff(c_2378,plain,(
    ! [A_292] :
      ( v5_relat_1(A_292,'#skF_2')
      | ~ r1_tarski(A_292,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1916,c_2345])).

tff(c_1709,plain,(
    ! [C_250,A_251,B_252] :
      ( v1_relat_1(C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1718,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1709])).

tff(c_4354,plain,(
    ! [D_470,B_471,C_472,A_473] :
      ( m1_subset_1(D_470,k1_zfmisc_1(k2_zfmisc_1(B_471,C_472)))
      | ~ r1_tarski(k1_relat_1(D_470),B_471)
      | ~ m1_subset_1(D_470,k1_zfmisc_1(k2_zfmisc_1(A_473,C_472))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4498,plain,(
    ! [B_480] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_480,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_480) ) ),
    inference(resolution,[status(thm)],[c_64,c_4354])).

tff(c_50,plain,(
    ! [C_37,A_35,B_36] :
      ( v4_relat_1(C_37,A_35)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4534,plain,(
    ! [B_481] :
      ( v4_relat_1('#skF_3',B_481)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_481) ) ),
    inference(resolution,[status(thm)],[c_4498,c_50])).

tff(c_4559,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_4534])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4564,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4559,c_24])).

tff(c_4570,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_4564])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4574,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4570,c_18])).

tff(c_4581,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_4574])).

tff(c_42,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,k10_relat_1(B_29,k9_relat_1(B_29,A_28)))
      | ~ r1_tarski(A_28,k1_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4588,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4581,c_42])).

tff(c_4592,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_6,c_4588])).

tff(c_1741,plain,(
    ! [B_260,A_261] :
      ( r1_tarski(k10_relat_1(B_260,A_261),k1_relat_1(B_260))
      | ~ v1_relat_1(B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9531,plain,(
    ! [B_653,A_654] :
      ( k10_relat_1(B_653,A_654) = k1_relat_1(B_653)
      | ~ r1_tarski(k1_relat_1(B_653),k10_relat_1(B_653,A_654))
      | ~ v1_relat_1(B_653) ) ),
    inference(resolution,[status(thm)],[c_1741,c_2])).

tff(c_9556,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4592,c_9531])).

tff(c_9587,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_9556])).

tff(c_1778,plain,(
    ! [C_271,A_272,B_273] :
      ( v4_relat_1(C_271,A_272)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1787,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_1778])).

tff(c_1826,plain,(
    ! [B_284,A_285] :
      ( k7_relat_1(B_284,A_285) = B_284
      | ~ v4_relat_1(B_284,A_285)
      | ~ v1_relat_1(B_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1835,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1787,c_1826])).

tff(c_1847,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_1835])).

tff(c_2399,plain,(
    ! [B_346,A_347] :
      ( k2_relat_1(k7_relat_1(B_346,A_347)) = k9_relat_1(B_346,A_347)
      | ~ v1_relat_1(B_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2426,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1847,c_2399])).

tff(c_2436,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_2426])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10949,plain,(
    ! [B_706,A_707,A_708] :
      ( r1_tarski(k9_relat_1(B_706,A_707),A_708)
      | ~ v5_relat_1(k7_relat_1(B_706,A_707),A_708)
      | ~ v1_relat_1(k7_relat_1(B_706,A_707))
      | ~ v1_relat_1(B_706) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2399,c_16])).

tff(c_10982,plain,(
    ! [A_708] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_708)
      | ~ v5_relat_1('#skF_3',A_708)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1847,c_10949])).

tff(c_11000,plain,(
    ! [A_709] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_709)
      | ~ v5_relat_1('#skF_3',A_709) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_1718,c_1847,c_2436,c_10982])).

tff(c_28,plain,(
    ! [A_22] : k1_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_27] : v1_relat_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2033,plain,(
    ! [B_305,A_306] : k5_relat_1(k6_relat_1(B_305),k6_relat_1(A_306)) = k6_relat_1(k3_xboole_0(A_306,B_305)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    ! [A_25,B_26] :
      ( k5_relat_1(k6_relat_1(A_25),B_26) = k7_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2039,plain,(
    ! [A_306,B_305] :
      ( k7_relat_1(k6_relat_1(A_306),B_305) = k6_relat_1(k3_xboole_0(A_306,B_305))
      | ~ v1_relat_1(k6_relat_1(A_306)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2033,c_34])).

tff(c_2049,plain,(
    ! [A_306,B_305] : k7_relat_1(k6_relat_1(A_306),B_305) = k6_relat_1(k3_xboole_0(A_306,B_305)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2039])).

tff(c_38,plain,(
    ! [A_27] : v4_relat_1(k6_relat_1(A_27),A_27) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2576,plain,(
    ! [C_363,B_364,A_365] :
      ( v4_relat_1(C_363,B_364)
      | ~ v4_relat_1(C_363,A_365)
      | ~ v1_relat_1(C_363)
      | ~ r1_tarski(A_365,B_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2588,plain,(
    ! [A_27,B_364] :
      ( v4_relat_1(k6_relat_1(A_27),B_364)
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ r1_tarski(A_27,B_364) ) ),
    inference(resolution,[status(thm)],[c_38,c_2576])).

tff(c_2617,plain,(
    ! [A_367,B_368] :
      ( v4_relat_1(k6_relat_1(A_367),B_368)
      | ~ r1_tarski(A_367,B_368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2588])).

tff(c_2622,plain,(
    ! [A_367,B_368] :
      ( k7_relat_1(k6_relat_1(A_367),B_368) = k6_relat_1(A_367)
      | ~ v1_relat_1(k6_relat_1(A_367))
      | ~ r1_tarski(A_367,B_368) ) ),
    inference(resolution,[status(thm)],[c_2617,c_24])).

tff(c_3495,plain,(
    ! [A_439,B_440] :
      ( k6_relat_1(k3_xboole_0(A_439,B_440)) = k6_relat_1(A_439)
      | ~ r1_tarski(A_439,B_440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2049,c_2622])).

tff(c_3562,plain,(
    ! [A_439,B_440] :
      ( k3_xboole_0(A_439,B_440) = k1_relat_1(k6_relat_1(A_439))
      | ~ r1_tarski(A_439,B_440) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3495,c_28])).

tff(c_3581,plain,(
    ! [A_439,B_440] :
      ( k3_xboole_0(A_439,B_440) = A_439
      | ~ r1_tarski(A_439,B_440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3562])).

tff(c_11452,plain,(
    ! [A_721] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_721) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_721) ) ),
    inference(resolution,[status(thm)],[c_11000,c_3581])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( k10_relat_1(B_15,k3_xboole_0(k2_relat_1(B_15),A_14)) = k10_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_11732,plain,(
    ! [A_721] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_721)
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_721) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11452,c_22])).

tff(c_11821,plain,(
    ! [A_722] :
      ( k10_relat_1('#skF_3',A_722) = k1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_722) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_9587,c_11732])).

tff(c_11828,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2378,c_11821])).

tff(c_11844,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11828])).

tff(c_11846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3834,c_11844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.63/3.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.63/3.30  
% 8.63/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.63/3.30  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 8.63/3.30  
% 8.63/3.30  %Foreground sorts:
% 8.63/3.30  
% 8.63/3.30  
% 8.63/3.30  %Background operators:
% 8.63/3.30  
% 8.63/3.30  
% 8.63/3.30  %Foreground operators:
% 8.63/3.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.63/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.63/3.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.63/3.30  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 8.63/3.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.63/3.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.63/3.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.63/3.30  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.63/3.30  tff('#skF_2', type, '#skF_2': $i).
% 8.63/3.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.63/3.30  tff('#skF_3', type, '#skF_3': $i).
% 8.63/3.30  tff('#skF_1', type, '#skF_1': $i).
% 8.63/3.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.63/3.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.63/3.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.63/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.63/3.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.63/3.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.63/3.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.63/3.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.63/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.63/3.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.63/3.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.63/3.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.63/3.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.63/3.30  
% 8.63/3.33  tff(f_139, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 8.63/3.33  tff(f_126, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 8.63/3.33  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.63/3.33  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.63/3.33  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.63/3.33  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 8.63/3.33  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 8.63/3.33  tff(f_122, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.63/3.33  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.63/3.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.63/3.33  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.63/3.33  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.63/3.33  tff(f_132, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 8.63/3.33  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 8.63/3.33  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 8.63/3.33  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.63/3.33  tff(f_78, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.63/3.33  tff(f_92, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 8.63/3.33  tff(f_100, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 8.63/3.33  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 8.63/3.33  tff(f_74, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 8.63/3.33  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 8.63/3.33  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.63/3.33  tff(c_3787, plain, (![A_443, B_444, C_445, D_446]: (k8_relset_1(A_443, B_444, C_445, D_446)=k10_relat_1(C_445, D_446) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_443, B_444))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.63/3.33  tff(c_3794, plain, (![D_446]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_446)=k10_relat_1('#skF_3', D_446))), inference(resolution, [status(thm)], [c_64, c_3787])).
% 8.63/3.33  tff(c_3127, plain, (![A_413, B_414, C_415]: (k1_relset_1(A_413, B_414, C_415)=k1_relat_1(C_415) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.63/3.33  tff(c_3136, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_3127])).
% 8.63/3.33  tff(c_99, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.63/3.33  tff(c_108, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_99])).
% 8.63/3.33  tff(c_159, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.63/3.33  tff(c_168, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_159])).
% 8.63/3.33  tff(c_191, plain, (![B_93, A_94]: (k7_relat_1(B_93, A_94)=B_93 | ~v4_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.63/3.33  tff(c_197, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_168, c_191])).
% 8.63/3.33  tff(c_206, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_197])).
% 8.63/3.33  tff(c_513, plain, (![B_140, A_141]: (k2_relat_1(k7_relat_1(B_140, A_141))=k9_relat_1(B_140, A_141) | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.63/3.33  tff(c_540, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_206, c_513])).
% 8.63/3.33  tff(c_550, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_540])).
% 8.63/3.33  tff(c_1690, plain, (![A_244, B_245, C_246, D_247]: (k7_relset_1(A_244, B_245, C_246, D_247)=k9_relat_1(C_246, D_247) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.63/3.33  tff(c_1697, plain, (![D_247]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_247)=k9_relat_1('#skF_3', D_247))), inference(resolution, [status(thm)], [c_64, c_1690])).
% 8.63/3.33  tff(c_964, plain, (![A_182, B_183, C_184]: (k2_relset_1(A_182, B_183, C_184)=k2_relat_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.63/3.33  tff(c_973, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_964])).
% 8.63/3.33  tff(c_62, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.63/3.33  tff(c_93, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 8.63/3.33  tff(c_974, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_973, c_93])).
% 8.63/3.33  tff(c_1698, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1697, c_974])).
% 8.63/3.33  tff(c_1701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_550, c_1698])).
% 8.63/3.33  tff(c_1702, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 8.63/3.33  tff(c_3137, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3136, c_1702])).
% 8.63/3.33  tff(c_3834, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3794, c_3137])).
% 8.63/3.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.63/3.33  tff(c_88, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~m1_subset_1(A_62, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.63/3.33  tff(c_92, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_88])).
% 8.63/3.33  tff(c_1899, plain, (![A_292, C_293, B_294]: (r1_tarski(A_292, C_293) | ~r1_tarski(B_294, C_293) | ~r1_tarski(A_292, B_294))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.63/3.33  tff(c_1916, plain, (![A_292]: (r1_tarski(A_292, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_292, '#skF_3'))), inference(resolution, [status(thm)], [c_92, c_1899])).
% 8.63/3.33  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.63/3.33  tff(c_2176, plain, (![C_318, B_319, A_320]: (v5_relat_1(C_318, B_319) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_320, B_319))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.63/3.33  tff(c_2345, plain, (![A_336, B_337, A_338]: (v5_relat_1(A_336, B_337) | ~r1_tarski(A_336, k2_zfmisc_1(A_338, B_337)))), inference(resolution, [status(thm)], [c_12, c_2176])).
% 8.63/3.33  tff(c_2378, plain, (![A_292]: (v5_relat_1(A_292, '#skF_2') | ~r1_tarski(A_292, '#skF_3'))), inference(resolution, [status(thm)], [c_1916, c_2345])).
% 8.63/3.33  tff(c_1709, plain, (![C_250, A_251, B_252]: (v1_relat_1(C_250) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.63/3.33  tff(c_1718, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1709])).
% 8.63/3.33  tff(c_4354, plain, (![D_470, B_471, C_472, A_473]: (m1_subset_1(D_470, k1_zfmisc_1(k2_zfmisc_1(B_471, C_472))) | ~r1_tarski(k1_relat_1(D_470), B_471) | ~m1_subset_1(D_470, k1_zfmisc_1(k2_zfmisc_1(A_473, C_472))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.63/3.33  tff(c_4498, plain, (![B_480]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_480, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_480))), inference(resolution, [status(thm)], [c_64, c_4354])).
% 8.63/3.33  tff(c_50, plain, (![C_37, A_35, B_36]: (v4_relat_1(C_37, A_35) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.63/3.33  tff(c_4534, plain, (![B_481]: (v4_relat_1('#skF_3', B_481) | ~r1_tarski(k1_relat_1('#skF_3'), B_481))), inference(resolution, [status(thm)], [c_4498, c_50])).
% 8.63/3.33  tff(c_4559, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_4534])).
% 8.63/3.33  tff(c_24, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.63/3.33  tff(c_4564, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4559, c_24])).
% 8.63/3.33  tff(c_4570, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_4564])).
% 8.63/3.33  tff(c_18, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.63/3.33  tff(c_4574, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4570, c_18])).
% 8.63/3.33  tff(c_4581, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_4574])).
% 8.63/3.33  tff(c_42, plain, (![A_28, B_29]: (r1_tarski(A_28, k10_relat_1(B_29, k9_relat_1(B_29, A_28))) | ~r1_tarski(A_28, k1_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.63/3.33  tff(c_4588, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4581, c_42])).
% 8.63/3.33  tff(c_4592, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_6, c_4588])).
% 8.63/3.33  tff(c_1741, plain, (![B_260, A_261]: (r1_tarski(k10_relat_1(B_260, A_261), k1_relat_1(B_260)) | ~v1_relat_1(B_260))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.63/3.33  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.63/3.33  tff(c_9531, plain, (![B_653, A_654]: (k10_relat_1(B_653, A_654)=k1_relat_1(B_653) | ~r1_tarski(k1_relat_1(B_653), k10_relat_1(B_653, A_654)) | ~v1_relat_1(B_653))), inference(resolution, [status(thm)], [c_1741, c_2])).
% 8.63/3.33  tff(c_9556, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4592, c_9531])).
% 8.63/3.33  tff(c_9587, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_9556])).
% 8.63/3.33  tff(c_1778, plain, (![C_271, A_272, B_273]: (v4_relat_1(C_271, A_272) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.63/3.33  tff(c_1787, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_1778])).
% 8.63/3.33  tff(c_1826, plain, (![B_284, A_285]: (k7_relat_1(B_284, A_285)=B_284 | ~v4_relat_1(B_284, A_285) | ~v1_relat_1(B_284))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.63/3.33  tff(c_1835, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1787, c_1826])).
% 8.63/3.33  tff(c_1847, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_1835])).
% 8.63/3.33  tff(c_2399, plain, (![B_346, A_347]: (k2_relat_1(k7_relat_1(B_346, A_347))=k9_relat_1(B_346, A_347) | ~v1_relat_1(B_346))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.63/3.33  tff(c_2426, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1847, c_2399])).
% 8.63/3.33  tff(c_2436, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_2426])).
% 8.63/3.33  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.63/3.33  tff(c_10949, plain, (![B_706, A_707, A_708]: (r1_tarski(k9_relat_1(B_706, A_707), A_708) | ~v5_relat_1(k7_relat_1(B_706, A_707), A_708) | ~v1_relat_1(k7_relat_1(B_706, A_707)) | ~v1_relat_1(B_706))), inference(superposition, [status(thm), theory('equality')], [c_2399, c_16])).
% 8.63/3.33  tff(c_10982, plain, (![A_708]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_708) | ~v5_relat_1('#skF_3', A_708) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1847, c_10949])).
% 8.63/3.33  tff(c_11000, plain, (![A_709]: (r1_tarski(k2_relat_1('#skF_3'), A_709) | ~v5_relat_1('#skF_3', A_709))), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_1718, c_1847, c_2436, c_10982])).
% 8.63/3.33  tff(c_28, plain, (![A_22]: (k1_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.63/3.33  tff(c_36, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.63/3.33  tff(c_2033, plain, (![B_305, A_306]: (k5_relat_1(k6_relat_1(B_305), k6_relat_1(A_306))=k6_relat_1(k3_xboole_0(A_306, B_305)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.63/3.33  tff(c_34, plain, (![A_25, B_26]: (k5_relat_1(k6_relat_1(A_25), B_26)=k7_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.63/3.33  tff(c_2039, plain, (![A_306, B_305]: (k7_relat_1(k6_relat_1(A_306), B_305)=k6_relat_1(k3_xboole_0(A_306, B_305)) | ~v1_relat_1(k6_relat_1(A_306)))), inference(superposition, [status(thm), theory('equality')], [c_2033, c_34])).
% 8.63/3.33  tff(c_2049, plain, (![A_306, B_305]: (k7_relat_1(k6_relat_1(A_306), B_305)=k6_relat_1(k3_xboole_0(A_306, B_305)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2039])).
% 8.63/3.33  tff(c_38, plain, (![A_27]: (v4_relat_1(k6_relat_1(A_27), A_27))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.63/3.33  tff(c_2576, plain, (![C_363, B_364, A_365]: (v4_relat_1(C_363, B_364) | ~v4_relat_1(C_363, A_365) | ~v1_relat_1(C_363) | ~r1_tarski(A_365, B_364))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.63/3.33  tff(c_2588, plain, (![A_27, B_364]: (v4_relat_1(k6_relat_1(A_27), B_364) | ~v1_relat_1(k6_relat_1(A_27)) | ~r1_tarski(A_27, B_364))), inference(resolution, [status(thm)], [c_38, c_2576])).
% 8.63/3.33  tff(c_2617, plain, (![A_367, B_368]: (v4_relat_1(k6_relat_1(A_367), B_368) | ~r1_tarski(A_367, B_368))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2588])).
% 8.63/3.33  tff(c_2622, plain, (![A_367, B_368]: (k7_relat_1(k6_relat_1(A_367), B_368)=k6_relat_1(A_367) | ~v1_relat_1(k6_relat_1(A_367)) | ~r1_tarski(A_367, B_368))), inference(resolution, [status(thm)], [c_2617, c_24])).
% 8.63/3.33  tff(c_3495, plain, (![A_439, B_440]: (k6_relat_1(k3_xboole_0(A_439, B_440))=k6_relat_1(A_439) | ~r1_tarski(A_439, B_440))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2049, c_2622])).
% 8.63/3.33  tff(c_3562, plain, (![A_439, B_440]: (k3_xboole_0(A_439, B_440)=k1_relat_1(k6_relat_1(A_439)) | ~r1_tarski(A_439, B_440))), inference(superposition, [status(thm), theory('equality')], [c_3495, c_28])).
% 8.63/3.33  tff(c_3581, plain, (![A_439, B_440]: (k3_xboole_0(A_439, B_440)=A_439 | ~r1_tarski(A_439, B_440))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3562])).
% 8.63/3.33  tff(c_11452, plain, (![A_721]: (k3_xboole_0(k2_relat_1('#skF_3'), A_721)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_721))), inference(resolution, [status(thm)], [c_11000, c_3581])).
% 8.63/3.33  tff(c_22, plain, (![B_15, A_14]: (k10_relat_1(B_15, k3_xboole_0(k2_relat_1(B_15), A_14))=k10_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.63/3.33  tff(c_11732, plain, (![A_721]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_721) | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_721))), inference(superposition, [status(thm), theory('equality')], [c_11452, c_22])).
% 8.63/3.33  tff(c_11821, plain, (![A_722]: (k10_relat_1('#skF_3', A_722)=k1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_722))), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_9587, c_11732])).
% 8.63/3.33  tff(c_11828, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2378, c_11821])).
% 8.63/3.33  tff(c_11844, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11828])).
% 8.63/3.33  tff(c_11846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3834, c_11844])).
% 8.63/3.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.63/3.33  
% 8.63/3.33  Inference rules
% 8.63/3.33  ----------------------
% 8.63/3.33  #Ref     : 0
% 8.63/3.33  #Sup     : 2618
% 8.63/3.33  #Fact    : 0
% 8.63/3.33  #Define  : 0
% 8.63/3.33  #Split   : 14
% 8.63/3.33  #Chain   : 0
% 8.63/3.33  #Close   : 0
% 8.63/3.33  
% 8.63/3.33  Ordering : KBO
% 8.63/3.33  
% 8.63/3.33  Simplification rules
% 8.63/3.33  ----------------------
% 8.63/3.33  #Subsume      : 312
% 8.63/3.33  #Demod        : 1270
% 8.63/3.33  #Tautology    : 860
% 8.63/3.33  #SimpNegUnit  : 3
% 8.63/3.33  #BackRed      : 14
% 8.63/3.33  
% 8.63/3.33  #Partial instantiations: 0
% 8.63/3.33  #Strategies tried      : 1
% 8.63/3.33  
% 8.63/3.33  Timing (in seconds)
% 8.63/3.33  ----------------------
% 8.63/3.33  Preprocessing        : 0.35
% 8.63/3.33  Parsing              : 0.19
% 8.63/3.33  CNF conversion       : 0.02
% 8.63/3.33  Main loop            : 2.20
% 8.63/3.33  Inferencing          : 0.63
% 8.63/3.33  Reduction            : 0.88
% 8.63/3.33  Demodulation         : 0.69
% 8.63/3.33  BG Simplification    : 0.07
% 8.63/3.33  Subsumption          : 0.44
% 8.63/3.33  Abstraction          : 0.09
% 8.63/3.33  MUC search           : 0.00
% 8.63/3.33  Cooper               : 0.00
% 8.63/3.33  Total                : 2.59
% 8.63/3.33  Index Insertion      : 0.00
% 8.63/3.33  Index Deletion       : 0.00
% 8.63/3.33  Index Matching       : 0.00
% 8.63/3.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
