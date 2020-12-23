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
% DateTime   : Thu Dec  3 10:14:30 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 559 expanded)
%              Number of leaves         :   49 ( 205 expanded)
%              Depth                    :   16
%              Number of atoms          :  199 (1135 expanded)
%              Number of equality atoms :  107 ( 484 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_146,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_102,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_68,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_96,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_104,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_96])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_28,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_113,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_104,c_28])).

tff(c_147,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_178,plain,(
    ! [C_70,A_71,B_72] :
      ( v4_relat_1(C_70,A_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_186,plain,(
    v4_relat_1('#skF_3',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_178])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = B_20
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_197,plain,
    ( k7_relat_1('#skF_3',k1_tarski('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_186,c_22])).

tff(c_200,plain,(
    k7_relat_1('#skF_3',k1_tarski('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_197])).

tff(c_212,plain,(
    ! [B_75,A_76] :
      ( k2_relat_1(k7_relat_1(B_75,A_76)) = k9_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_224,plain,
    ( k9_relat_1('#skF_3',k1_tarski('#skF_1')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_212])).

tff(c_231,plain,(
    k9_relat_1('#skF_3',k1_tarski('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_224])).

tff(c_12,plain,(
    ! [A_11,B_13] :
      ( k9_relat_1(A_11,k1_tarski(B_13)) = k11_relat_1(A_11,B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_272,plain,
    ( k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_12])).

tff(c_279,plain,(
    k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_272])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,k1_relat_1(B_18))
      | k11_relat_1(B_18,A_17) = k1_xboole_0
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_345,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k7_relset_1(A_100,B_101,C_102,D_103) = k9_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_351,plain,(
    ! [D_103] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',D_103) = k9_relat_1('#skF_3',D_103) ),
    inference(resolution,[status(thm)],[c_62,c_345])).

tff(c_370,plain,(
    ! [A_108,B_109,C_110] :
      ( k7_relset_1(A_108,B_109,C_110,A_108) = k2_relset_1(A_108,B_109,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_372,plain,(
    k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',k1_tarski('#skF_1')) = k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_370])).

tff(c_377,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_351,c_372])).

tff(c_58,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_387,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_58])).

tff(c_421,plain,(
    ! [B_118,A_119] :
      ( k2_relat_1(k7_relat_1(B_118,k1_tarski(A_119))) = k1_tarski(k1_funct_1(B_118,A_119))
      | ~ r2_hidden(A_119,k1_relat_1(B_118))
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_443,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_421])).

tff(c_451,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_443])).

tff(c_452,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_387,c_451])).

tff(c_457,plain,
    ( k11_relat_1('#skF_3','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_452])).

tff(c_460,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_279,c_457])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_460])).

tff(c_463,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_472,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_463,c_26])).

tff(c_30,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_112,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_104,c_30])).

tff(c_146,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_465,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_146])).

tff(c_500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_465])).

tff(c_501,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_502,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_516,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_502])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_508,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_501,c_24])).

tff(c_32,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(k1_funct_1(B_23,A_22)) = k2_relat_1(B_23)
      | k1_tarski(A_22) != k1_relat_1(B_23)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_507,plain,(
    ! [A_7] : m1_subset_1('#skF_3',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_8])).

tff(c_570,plain,(
    ! [C_132,A_133,B_134] :
      ( v4_relat_1(C_132,A_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_588,plain,(
    ! [A_137] : v4_relat_1('#skF_3',A_137) ),
    inference(resolution,[status(thm)],[c_507,c_570])).

tff(c_591,plain,(
    ! [A_137] :
      ( k7_relat_1('#skF_3',A_137) = '#skF_3'
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_588,c_22])).

tff(c_595,plain,(
    ! [A_138] : k7_relat_1('#skF_3',A_138) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_591])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_600,plain,(
    ! [A_138] :
      ( k9_relat_1('#skF_3',A_138) = k2_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_14])).

tff(c_605,plain,(
    ! [A_138] : k9_relat_1('#skF_3',A_138) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_508,c_600])).

tff(c_681,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( k7_relset_1(A_160,B_161,C_162,D_163) = k9_relat_1(C_162,D_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_684,plain,(
    ! [A_160,B_161,D_163] : k7_relset_1(A_160,B_161,'#skF_3',D_163) = k9_relat_1('#skF_3',D_163) ),
    inference(resolution,[status(thm)],[c_507,c_681])).

tff(c_686,plain,(
    ! [A_160,B_161,D_163] : k7_relset_1(A_160,B_161,'#skF_3',D_163) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_684])).

tff(c_730,plain,(
    ! [A_177,B_178,C_179] :
      ( k7_relset_1(A_177,B_178,C_179,A_177) = k2_relset_1(A_177,B_178,C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_733,plain,(
    ! [A_177,B_178] : k7_relset_1(A_177,B_178,'#skF_3',A_177) = k2_relset_1(A_177,B_178,'#skF_3') ),
    inference(resolution,[status(thm)],[c_507,c_730])).

tff(c_735,plain,(
    ! [A_177,B_178] : k2_relset_1(A_177,B_178,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_733])).

tff(c_736,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_58])).

tff(c_746,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | k1_tarski('#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_736])).

tff(c_748,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_516,c_508,c_746])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_510,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_60])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_676,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k8_relset_1(A_156,B_157,C_158,D_159) = k10_relat_1(C_158,D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_680,plain,(
    ! [A_156,B_157,D_159] : k8_relset_1(A_156,B_157,'#skF_3',D_159) = k10_relat_1('#skF_3',D_159) ),
    inference(resolution,[status(thm)],[c_507,c_676])).

tff(c_715,plain,(
    ! [A_172,B_173,C_174] :
      ( k8_relset_1(A_172,B_173,C_174,B_173) = k1_relset_1(A_172,B_173,C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_718,plain,(
    ! [A_172,B_173] : k8_relset_1(A_172,B_173,'#skF_3',B_173) = k1_relset_1(A_172,B_173,'#skF_3') ),
    inference(resolution,[status(thm)],[c_507,c_715])).

tff(c_720,plain,(
    ! [A_172,B_173] : k1_relset_1(A_172,B_173,'#skF_3') = k10_relat_1('#skF_3',B_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_718])).

tff(c_105,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_128,plain,(
    ! [A_58] :
      ( k10_relat_1(A_58,k2_relat_1(A_58)) = k1_relat_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_137,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_128])).

tff(c_141,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_26,c_137])).

tff(c_503,plain,(
    k10_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_501,c_501,c_141])).

tff(c_886,plain,(
    ! [B_198,A_199,C_200] :
      ( k8_relset_1(B_198,A_199,C_200,k7_relset_1(B_198,A_199,C_200,B_198)) = k1_relset_1(B_198,A_199,C_200)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(B_198,A_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_889,plain,(
    ! [B_198,A_199] : k8_relset_1(B_198,A_199,'#skF_3',k7_relset_1(B_198,A_199,'#skF_3',B_198)) = k1_relset_1(B_198,A_199,'#skF_3') ),
    inference(resolution,[status(thm)],[c_507,c_886])).

tff(c_891,plain,(
    ! [A_199] : k10_relat_1('#skF_3',A_199) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_503,c_680,c_686,c_889])).

tff(c_894,plain,(
    ! [A_156,B_157,D_159] : k8_relset_1(A_156,B_157,'#skF_3',D_159) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_680])).

tff(c_56,plain,(
    ! [B_47,A_46,C_48] :
      ( k1_xboole_0 = B_47
      | k8_relset_1(A_46,B_47,C_48,B_47) = A_46
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_2(C_48,A_46,B_47)
      | ~ v1_funct_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1015,plain,(
    ! [B_212,A_213,C_214] :
      ( B_212 = '#skF_3'
      | k8_relset_1(A_213,B_212,C_214,B_212) = A_213
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_213,B_212)))
      | ~ v1_funct_2(C_214,A_213,B_212)
      | ~ v1_funct_1(C_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_56])).

tff(c_1018,plain,(
    ! [B_212,A_213] :
      ( B_212 = '#skF_3'
      | k8_relset_1(A_213,B_212,'#skF_3',B_212) = A_213
      | ~ v1_funct_2('#skF_3',A_213,B_212)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_507,c_1015])).

tff(c_1022,plain,(
    ! [B_215,A_216] :
      ( B_215 = '#skF_3'
      | A_216 = '#skF_3'
      | ~ v1_funct_2('#skF_3',A_216,B_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_894,c_1018])).

tff(c_1025,plain,
    ( '#skF_2' = '#skF_3'
    | k1_tarski('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_64,c_1022])).

tff(c_1029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_748,c_510,c_1025])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.51  
% 3.06/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.06/1.51  
% 3.06/1.51  %Foreground sorts:
% 3.06/1.51  
% 3.06/1.51  
% 3.06/1.51  %Background operators:
% 3.06/1.51  
% 3.06/1.51  
% 3.06/1.51  %Foreground operators:
% 3.06/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.06/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.06/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.06/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.06/1.51  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.06/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.06/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.06/1.51  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.06/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.06/1.51  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.06/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.06/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.06/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.06/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.06/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.06/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.06/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.06/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.51  
% 3.40/1.53  tff(f_146, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.40/1.53  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.40/1.53  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.40/1.53  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.40/1.53  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.40/1.53  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.40/1.53  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.40/1.53  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.40/1.53  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.40/1.53  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.40/1.53  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_funct_1)).
% 3.40/1.53  tff(f_68, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.40/1.53  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.40/1.53  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.40/1.53  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.40/1.53  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.40/1.53  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.40/1.53  tff(f_134, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 3.40/1.53  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.40/1.53  tff(c_96, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.40/1.53  tff(c_104, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_96])).
% 3.40/1.53  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.40/1.53  tff(c_28, plain, (![A_21]: (k2_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.40/1.53  tff(c_113, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_104, c_28])).
% 3.40/1.53  tff(c_147, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_113])).
% 3.40/1.53  tff(c_178, plain, (![C_70, A_71, B_72]: (v4_relat_1(C_70, A_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.40/1.53  tff(c_186, plain, (v4_relat_1('#skF_3', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_178])).
% 3.40/1.53  tff(c_22, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=B_20 | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.40/1.53  tff(c_197, plain, (k7_relat_1('#skF_3', k1_tarski('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_186, c_22])).
% 3.40/1.53  tff(c_200, plain, (k7_relat_1('#skF_3', k1_tarski('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_197])).
% 3.40/1.53  tff(c_212, plain, (![B_75, A_76]: (k2_relat_1(k7_relat_1(B_75, A_76))=k9_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.40/1.53  tff(c_224, plain, (k9_relat_1('#skF_3', k1_tarski('#skF_1'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_200, c_212])).
% 3.40/1.53  tff(c_231, plain, (k9_relat_1('#skF_3', k1_tarski('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_224])).
% 3.40/1.53  tff(c_12, plain, (![A_11, B_13]: (k9_relat_1(A_11, k1_tarski(B_13))=k11_relat_1(A_11, B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.40/1.53  tff(c_272, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_231, c_12])).
% 3.40/1.53  tff(c_279, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_272])).
% 3.40/1.53  tff(c_18, plain, (![A_17, B_18]: (r2_hidden(A_17, k1_relat_1(B_18)) | k11_relat_1(B_18, A_17)=k1_xboole_0 | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.40/1.53  tff(c_345, plain, (![A_100, B_101, C_102, D_103]: (k7_relset_1(A_100, B_101, C_102, D_103)=k9_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.40/1.53  tff(c_351, plain, (![D_103]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', D_103)=k9_relat_1('#skF_3', D_103))), inference(resolution, [status(thm)], [c_62, c_345])).
% 3.40/1.53  tff(c_370, plain, (![A_108, B_109, C_110]: (k7_relset_1(A_108, B_109, C_110, A_108)=k2_relset_1(A_108, B_109, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.40/1.53  tff(c_372, plain, (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', k1_tarski('#skF_1'))=k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_370])).
% 3.40/1.53  tff(c_377, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_351, c_372])).
% 3.40/1.53  tff(c_58, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.40/1.53  tff(c_387, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_58])).
% 3.40/1.53  tff(c_421, plain, (![B_118, A_119]: (k2_relat_1(k7_relat_1(B_118, k1_tarski(A_119)))=k1_tarski(k1_funct_1(B_118, A_119)) | ~r2_hidden(A_119, k1_relat_1(B_118)) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.40/1.53  tff(c_443, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_200, c_421])).
% 3.40/1.53  tff(c_451, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_443])).
% 3.40/1.53  tff(c_452, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_387, c_451])).
% 3.40/1.53  tff(c_457, plain, (k11_relat_1('#skF_3', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_452])).
% 3.40/1.53  tff(c_460, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_279, c_457])).
% 3.40/1.53  tff(c_462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_460])).
% 3.40/1.53  tff(c_463, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_113])).
% 3.40/1.53  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.53  tff(c_472, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_463, c_463, c_26])).
% 3.40/1.53  tff(c_30, plain, (![A_21]: (k1_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.40/1.53  tff(c_112, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_104, c_30])).
% 3.40/1.53  tff(c_146, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_112])).
% 3.40/1.53  tff(c_465, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_463, c_146])).
% 3.40/1.53  tff(c_500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_472, c_465])).
% 3.40/1.53  tff(c_501, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_112])).
% 3.40/1.53  tff(c_502, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_112])).
% 3.40/1.53  tff(c_516, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_501, c_502])).
% 3.40/1.53  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.53  tff(c_508, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_501, c_501, c_24])).
% 3.40/1.53  tff(c_32, plain, (![B_23, A_22]: (k1_tarski(k1_funct_1(B_23, A_22))=k2_relat_1(B_23) | k1_tarski(A_22)!=k1_relat_1(B_23) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.40/1.53  tff(c_8, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.40/1.53  tff(c_507, plain, (![A_7]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_8])).
% 3.40/1.53  tff(c_570, plain, (![C_132, A_133, B_134]: (v4_relat_1(C_132, A_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.40/1.53  tff(c_588, plain, (![A_137]: (v4_relat_1('#skF_3', A_137))), inference(resolution, [status(thm)], [c_507, c_570])).
% 3.40/1.53  tff(c_591, plain, (![A_137]: (k7_relat_1('#skF_3', A_137)='#skF_3' | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_588, c_22])).
% 3.40/1.53  tff(c_595, plain, (![A_138]: (k7_relat_1('#skF_3', A_138)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_591])).
% 3.40/1.53  tff(c_14, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.40/1.53  tff(c_600, plain, (![A_138]: (k9_relat_1('#skF_3', A_138)=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_595, c_14])).
% 3.40/1.53  tff(c_605, plain, (![A_138]: (k9_relat_1('#skF_3', A_138)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_508, c_600])).
% 3.40/1.53  tff(c_681, plain, (![A_160, B_161, C_162, D_163]: (k7_relset_1(A_160, B_161, C_162, D_163)=k9_relat_1(C_162, D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.40/1.53  tff(c_684, plain, (![A_160, B_161, D_163]: (k7_relset_1(A_160, B_161, '#skF_3', D_163)=k9_relat_1('#skF_3', D_163))), inference(resolution, [status(thm)], [c_507, c_681])).
% 3.40/1.53  tff(c_686, plain, (![A_160, B_161, D_163]: (k7_relset_1(A_160, B_161, '#skF_3', D_163)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_605, c_684])).
% 3.40/1.53  tff(c_730, plain, (![A_177, B_178, C_179]: (k7_relset_1(A_177, B_178, C_179, A_177)=k2_relset_1(A_177, B_178, C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.40/1.53  tff(c_733, plain, (![A_177, B_178]: (k7_relset_1(A_177, B_178, '#skF_3', A_177)=k2_relset_1(A_177, B_178, '#skF_3'))), inference(resolution, [status(thm)], [c_507, c_730])).
% 3.40/1.53  tff(c_735, plain, (![A_177, B_178]: (k2_relset_1(A_177, B_178, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_686, c_733])).
% 3.40/1.53  tff(c_736, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_735, c_58])).
% 3.40/1.53  tff(c_746, plain, (k2_relat_1('#skF_3')!='#skF_3' | k1_tarski('#skF_1')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_736])).
% 3.40/1.53  tff(c_748, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_516, c_508, c_746])).
% 3.40/1.53  tff(c_60, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.40/1.53  tff(c_510, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_501, c_60])).
% 3.40/1.53  tff(c_64, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.40/1.53  tff(c_676, plain, (![A_156, B_157, C_158, D_159]: (k8_relset_1(A_156, B_157, C_158, D_159)=k10_relat_1(C_158, D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.40/1.53  tff(c_680, plain, (![A_156, B_157, D_159]: (k8_relset_1(A_156, B_157, '#skF_3', D_159)=k10_relat_1('#skF_3', D_159))), inference(resolution, [status(thm)], [c_507, c_676])).
% 3.40/1.53  tff(c_715, plain, (![A_172, B_173, C_174]: (k8_relset_1(A_172, B_173, C_174, B_173)=k1_relset_1(A_172, B_173, C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.40/1.53  tff(c_718, plain, (![A_172, B_173]: (k8_relset_1(A_172, B_173, '#skF_3', B_173)=k1_relset_1(A_172, B_173, '#skF_3'))), inference(resolution, [status(thm)], [c_507, c_715])).
% 3.40/1.53  tff(c_720, plain, (![A_172, B_173]: (k1_relset_1(A_172, B_173, '#skF_3')=k10_relat_1('#skF_3', B_173))), inference(demodulation, [status(thm), theory('equality')], [c_680, c_718])).
% 3.40/1.53  tff(c_105, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_96])).
% 3.40/1.53  tff(c_128, plain, (![A_58]: (k10_relat_1(A_58, k2_relat_1(A_58))=k1_relat_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.40/1.53  tff(c_137, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_128])).
% 3.40/1.53  tff(c_141, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_26, c_137])).
% 3.40/1.53  tff(c_503, plain, (k10_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_501, c_501, c_501, c_141])).
% 3.40/1.53  tff(c_886, plain, (![B_198, A_199, C_200]: (k8_relset_1(B_198, A_199, C_200, k7_relset_1(B_198, A_199, C_200, B_198))=k1_relset_1(B_198, A_199, C_200) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(B_198, A_199))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.40/1.53  tff(c_889, plain, (![B_198, A_199]: (k8_relset_1(B_198, A_199, '#skF_3', k7_relset_1(B_198, A_199, '#skF_3', B_198))=k1_relset_1(B_198, A_199, '#skF_3'))), inference(resolution, [status(thm)], [c_507, c_886])).
% 3.40/1.53  tff(c_891, plain, (![A_199]: (k10_relat_1('#skF_3', A_199)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_720, c_503, c_680, c_686, c_889])).
% 3.40/1.53  tff(c_894, plain, (![A_156, B_157, D_159]: (k8_relset_1(A_156, B_157, '#skF_3', D_159)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_891, c_680])).
% 3.40/1.53  tff(c_56, plain, (![B_47, A_46, C_48]: (k1_xboole_0=B_47 | k8_relset_1(A_46, B_47, C_48, B_47)=A_46 | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_2(C_48, A_46, B_47) | ~v1_funct_1(C_48))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.40/1.53  tff(c_1015, plain, (![B_212, A_213, C_214]: (B_212='#skF_3' | k8_relset_1(A_213, B_212, C_214, B_212)=A_213 | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_213, B_212))) | ~v1_funct_2(C_214, A_213, B_212) | ~v1_funct_1(C_214))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_56])).
% 3.40/1.53  tff(c_1018, plain, (![B_212, A_213]: (B_212='#skF_3' | k8_relset_1(A_213, B_212, '#skF_3', B_212)=A_213 | ~v1_funct_2('#skF_3', A_213, B_212) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_507, c_1015])).
% 3.40/1.53  tff(c_1022, plain, (![B_215, A_216]: (B_215='#skF_3' | A_216='#skF_3' | ~v1_funct_2('#skF_3', A_216, B_215))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_894, c_1018])).
% 3.40/1.53  tff(c_1025, plain, ('#skF_2'='#skF_3' | k1_tarski('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_64, c_1022])).
% 3.40/1.53  tff(c_1029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_748, c_510, c_1025])).
% 3.40/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.53  
% 3.40/1.53  Inference rules
% 3.40/1.53  ----------------------
% 3.40/1.53  #Ref     : 0
% 3.40/1.53  #Sup     : 212
% 3.40/1.53  #Fact    : 0
% 3.40/1.53  #Define  : 0
% 3.40/1.53  #Split   : 2
% 3.40/1.53  #Chain   : 0
% 3.40/1.53  #Close   : 0
% 3.40/1.53  
% 3.40/1.53  Ordering : KBO
% 3.40/1.53  
% 3.40/1.53  Simplification rules
% 3.40/1.53  ----------------------
% 3.40/1.53  #Subsume      : 7
% 3.40/1.53  #Demod        : 181
% 3.40/1.53  #Tautology    : 141
% 3.40/1.53  #SimpNegUnit  : 4
% 3.40/1.53  #BackRed      : 21
% 3.40/1.53  
% 3.40/1.53  #Partial instantiations: 0
% 3.40/1.53  #Strategies tried      : 1
% 3.40/1.53  
% 3.40/1.53  Timing (in seconds)
% 3.40/1.53  ----------------------
% 3.40/1.54  Preprocessing        : 0.35
% 3.40/1.54  Parsing              : 0.19
% 3.40/1.54  CNF conversion       : 0.02
% 3.40/1.54  Main loop            : 0.37
% 3.40/1.54  Inferencing          : 0.14
% 3.40/1.54  Reduction            : 0.12
% 3.40/1.54  Demodulation         : 0.09
% 3.40/1.54  BG Simplification    : 0.03
% 3.40/1.54  Subsumption          : 0.05
% 3.40/1.54  Abstraction          : 0.02
% 3.40/1.54  MUC search           : 0.00
% 3.40/1.54  Cooper               : 0.00
% 3.40/1.54  Total                : 0.76
% 3.40/1.54  Index Insertion      : 0.00
% 3.40/1.54  Index Deletion       : 0.00
% 3.40/1.54  Index Matching       : 0.00
% 3.40/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
