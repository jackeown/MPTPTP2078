%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:44 EST 2020

% Result     : Theorem 4.42s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 196 expanded)
%              Number of leaves         :   43 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 375 expanded)
%              Number of equality atoms :   44 ( 101 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_145,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_162,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_145])).

tff(c_40,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,A_21),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_768,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k7_relset_1(A_158,B_159,C_160,D_161) = k9_relat_1(C_160,D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_789,plain,(
    ! [A_162,B_163,D_164] : k7_relset_1(A_162,B_163,k1_xboole_0,D_164) = k9_relat_1(k1_xboole_0,D_164) ),
    inference(resolution,[status(thm)],[c_26,c_768])).

tff(c_54,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( m1_subset_1(k7_relset_1(A_33,B_34,C_35,D_36),k1_zfmisc_1(B_34))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_799,plain,(
    ! [D_164,B_163,A_162] :
      ( m1_subset_1(k9_relat_1(k1_xboole_0,D_164),k1_zfmisc_1(B_163))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_54])).

tff(c_811,plain,(
    ! [D_166,B_167] : m1_subset_1(k9_relat_1(k1_xboole_0,D_166),k1_zfmisc_1(B_167)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_799])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_895,plain,(
    ! [D_173,B_174] : r1_tarski(k9_relat_1(k1_xboole_0,D_173),B_174) ),
    inference(resolution,[status(thm)],[c_811,c_28])).

tff(c_212,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_224,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_212])).

tff(c_934,plain,(
    ! [D_173] : k9_relat_1(k1_xboole_0,D_173) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_895,c_224])).

tff(c_24,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_80,plain,(
    ! [A_45,B_46] : v1_relat_1(k2_zfmisc_1(A_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_82,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_80])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_319,plain,(
    ! [C_86,A_87,B_88] :
      ( v4_relat_1(C_86,A_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_389,plain,(
    ! [A_98,A_99,B_100] :
      ( v4_relat_1(A_98,A_99)
      | ~ r1_tarski(A_98,k2_zfmisc_1(A_99,B_100)) ) ),
    inference(resolution,[status(thm)],[c_30,c_319])).

tff(c_414,plain,(
    ! [A_99,B_100] : v4_relat_1(k2_zfmisc_1(A_99,B_100),A_99) ),
    inference(resolution,[status(thm)],[c_6,c_389])).

tff(c_361,plain,(
    ! [B_96,A_97] :
      ( r1_tarski(k1_relat_1(B_96),A_97)
      | ~ v4_relat_1(B_96,A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_444,plain,(
    ! [B_105] :
      ( k1_relat_1(B_105) = k1_xboole_0
      | ~ v4_relat_1(B_105,k1_xboole_0)
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_361,c_224])).

tff(c_448,plain,(
    ! [B_100] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_100)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_100)) ) ),
    inference(resolution,[status(thm)],[c_414,c_444])).

tff(c_459,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_24,c_24,c_448])).

tff(c_510,plain,(
    ! [B_108,A_109] :
      ( r1_xboole_0(k1_relat_1(B_108),A_109)
      | k9_relat_1(B_108,A_109) != k1_xboole_0
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_513,plain,(
    ! [A_109] :
      ( r1_xboole_0(k1_xboole_0,A_109)
      | k9_relat_1(k1_xboole_0,A_109) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_510])).

tff(c_515,plain,(
    ! [A_109] :
      ( r1_xboole_0(k1_xboole_0,A_109)
      | k9_relat_1(k1_xboole_0,A_109) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_513])).

tff(c_953,plain,(
    ! [A_109] : r1_xboole_0(k1_xboole_0,A_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_515])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_580,plain,(
    ! [B_129,A_130] :
      ( k1_tarski(k1_funct_1(B_129,A_130)) = k2_relat_1(B_129)
      | k1_tarski(A_130) != k1_relat_1(B_129)
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_589,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_58])).

tff(c_595,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_66,c_589])).

tff(c_657,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_595])).

tff(c_338,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_319])).

tff(c_36,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_426,plain,(
    ! [B_103,A_104] :
      ( k1_tarski(B_103) = A_104
      | k1_xboole_0 = A_104
      | ~ r1_tarski(A_104,k1_tarski(B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1605,plain,(
    ! [B_240,B_241] :
      ( k1_tarski(B_240) = k1_relat_1(B_241)
      | k1_relat_1(B_241) = k1_xboole_0
      | ~ v4_relat_1(B_241,k1_tarski(B_240))
      | ~ v1_relat_1(B_241) ) ),
    inference(resolution,[status(thm)],[c_36,c_426])).

tff(c_1639,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_338,c_1605])).

tff(c_1659,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_1639])).

tff(c_1660,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_657,c_1659])).

tff(c_42,plain,(
    ! [B_24,A_23] :
      ( k9_relat_1(B_24,A_23) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_24),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1698,plain,(
    ! [A_23] :
      ( k9_relat_1('#skF_4',A_23) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_23)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1660,c_42])).

tff(c_1737,plain,(
    ! [A_23] : k9_relat_1('#skF_4',A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_953,c_1698])).

tff(c_786,plain,(
    ! [D_161] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_161) = k9_relat_1('#skF_4',D_161) ),
    inference(resolution,[status(thm)],[c_62,c_768])).

tff(c_878,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_58])).

tff(c_1817,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_878])).

tff(c_1824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1817])).

tff(c_1826,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_595])).

tff(c_1832,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1826,c_62])).

tff(c_1883,plain,(
    ! [A_247,B_248,C_249,D_250] :
      ( k7_relset_1(A_247,B_248,C_249,D_250) = k9_relat_1(C_249,D_250)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1896,plain,(
    ! [D_250] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_250) = k9_relat_1('#skF_4',D_250) ),
    inference(resolution,[status(thm)],[c_1832,c_1883])).

tff(c_1825,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_595])).

tff(c_1908,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1826,c_1825])).

tff(c_1916,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1896,c_1908])).

tff(c_1928,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1916])).

tff(c_1932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_1928])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.42/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/2.17  
% 4.42/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/2.18  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.42/2.18  
% 4.42/2.18  %Foreground sorts:
% 4.42/2.18  
% 4.42/2.18  
% 4.42/2.18  %Background operators:
% 4.42/2.18  
% 4.42/2.18  
% 4.42/2.18  %Foreground operators:
% 4.42/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.42/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.42/2.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.42/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.42/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.42/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.42/2.18  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.42/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.42/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.42/2.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.42/2.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.42/2.18  tff('#skF_2', type, '#skF_2': $i).
% 4.42/2.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.42/2.18  tff('#skF_3', type, '#skF_3': $i).
% 4.42/2.18  tff('#skF_1', type, '#skF_1': $i).
% 4.42/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.42/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.42/2.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.42/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.42/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.42/2.18  tff('#skF_4', type, '#skF_4': $i).
% 4.42/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/2.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.42/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.42/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.42/2.18  
% 4.65/2.19  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 4.65/2.19  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.65/2.19  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 4.65/2.19  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.65/2.19  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.65/2.19  tff(f_105, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.65/2.19  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.65/2.19  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.65/2.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.65/2.19  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.65/2.19  tff(f_69, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.65/2.19  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.65/2.19  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.65/2.19  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 4.65/2.19  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 4.65/2.19  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.65/2.19  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.65/2.19  tff(c_145, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.65/2.19  tff(c_162, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_145])).
% 4.65/2.19  tff(c_40, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, A_21), k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.65/2.19  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.65/2.19  tff(c_26, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.65/2.19  tff(c_768, plain, (![A_158, B_159, C_160, D_161]: (k7_relset_1(A_158, B_159, C_160, D_161)=k9_relat_1(C_160, D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.65/2.19  tff(c_789, plain, (![A_162, B_163, D_164]: (k7_relset_1(A_162, B_163, k1_xboole_0, D_164)=k9_relat_1(k1_xboole_0, D_164))), inference(resolution, [status(thm)], [c_26, c_768])).
% 4.65/2.19  tff(c_54, plain, (![A_33, B_34, C_35, D_36]: (m1_subset_1(k7_relset_1(A_33, B_34, C_35, D_36), k1_zfmisc_1(B_34)) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.65/2.19  tff(c_799, plain, (![D_164, B_163, A_162]: (m1_subset_1(k9_relat_1(k1_xboole_0, D_164), k1_zfmisc_1(B_163)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(superposition, [status(thm), theory('equality')], [c_789, c_54])).
% 4.65/2.19  tff(c_811, plain, (![D_166, B_167]: (m1_subset_1(k9_relat_1(k1_xboole_0, D_166), k1_zfmisc_1(B_167)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_799])).
% 4.65/2.19  tff(c_28, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.65/2.19  tff(c_895, plain, (![D_173, B_174]: (r1_tarski(k9_relat_1(k1_xboole_0, D_173), B_174))), inference(resolution, [status(thm)], [c_811, c_28])).
% 4.65/2.19  tff(c_212, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.65/2.19  tff(c_224, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_212])).
% 4.65/2.19  tff(c_934, plain, (![D_173]: (k9_relat_1(k1_xboole_0, D_173)=k1_xboole_0)), inference(resolution, [status(thm)], [c_895, c_224])).
% 4.65/2.19  tff(c_24, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.65/2.19  tff(c_80, plain, (![A_45, B_46]: (v1_relat_1(k2_zfmisc_1(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.65/2.19  tff(c_82, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_80])).
% 4.65/2.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.65/2.19  tff(c_30, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.65/2.19  tff(c_319, plain, (![C_86, A_87, B_88]: (v4_relat_1(C_86, A_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.65/2.19  tff(c_389, plain, (![A_98, A_99, B_100]: (v4_relat_1(A_98, A_99) | ~r1_tarski(A_98, k2_zfmisc_1(A_99, B_100)))), inference(resolution, [status(thm)], [c_30, c_319])).
% 4.65/2.19  tff(c_414, plain, (![A_99, B_100]: (v4_relat_1(k2_zfmisc_1(A_99, B_100), A_99))), inference(resolution, [status(thm)], [c_6, c_389])).
% 4.65/2.19  tff(c_361, plain, (![B_96, A_97]: (r1_tarski(k1_relat_1(B_96), A_97) | ~v4_relat_1(B_96, A_97) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.65/2.19  tff(c_444, plain, (![B_105]: (k1_relat_1(B_105)=k1_xboole_0 | ~v4_relat_1(B_105, k1_xboole_0) | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_361, c_224])).
% 4.65/2.19  tff(c_448, plain, (![B_100]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_100))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_100)))), inference(resolution, [status(thm)], [c_414, c_444])).
% 4.65/2.19  tff(c_459, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_82, c_24, c_24, c_448])).
% 4.65/2.19  tff(c_510, plain, (![B_108, A_109]: (r1_xboole_0(k1_relat_1(B_108), A_109) | k9_relat_1(B_108, A_109)!=k1_xboole_0 | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.65/2.19  tff(c_513, plain, (![A_109]: (r1_xboole_0(k1_xboole_0, A_109) | k9_relat_1(k1_xboole_0, A_109)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_459, c_510])).
% 4.65/2.19  tff(c_515, plain, (![A_109]: (r1_xboole_0(k1_xboole_0, A_109) | k9_relat_1(k1_xboole_0, A_109)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_513])).
% 4.65/2.19  tff(c_953, plain, (![A_109]: (r1_xboole_0(k1_xboole_0, A_109))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_515])).
% 4.65/2.19  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.65/2.19  tff(c_580, plain, (![B_129, A_130]: (k1_tarski(k1_funct_1(B_129, A_130))=k2_relat_1(B_129) | k1_tarski(A_130)!=k1_relat_1(B_129) | ~v1_funct_1(B_129) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.65/2.19  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.65/2.19  tff(c_589, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_580, c_58])).
% 4.65/2.19  tff(c_595, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_66, c_589])).
% 4.65/2.19  tff(c_657, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_595])).
% 4.65/2.19  tff(c_338, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_319])).
% 4.65/2.19  tff(c_36, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.65/2.19  tff(c_426, plain, (![B_103, A_104]: (k1_tarski(B_103)=A_104 | k1_xboole_0=A_104 | ~r1_tarski(A_104, k1_tarski(B_103)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.65/2.19  tff(c_1605, plain, (![B_240, B_241]: (k1_tarski(B_240)=k1_relat_1(B_241) | k1_relat_1(B_241)=k1_xboole_0 | ~v4_relat_1(B_241, k1_tarski(B_240)) | ~v1_relat_1(B_241))), inference(resolution, [status(thm)], [c_36, c_426])).
% 4.65/2.19  tff(c_1639, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_338, c_1605])).
% 4.65/2.19  tff(c_1659, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_162, c_1639])).
% 4.65/2.19  tff(c_1660, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_657, c_1659])).
% 4.65/2.19  tff(c_42, plain, (![B_24, A_23]: (k9_relat_1(B_24, A_23)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_24), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.65/2.19  tff(c_1698, plain, (![A_23]: (k9_relat_1('#skF_4', A_23)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_23) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1660, c_42])).
% 4.65/2.19  tff(c_1737, plain, (![A_23]: (k9_relat_1('#skF_4', A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_953, c_1698])).
% 4.65/2.19  tff(c_786, plain, (![D_161]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_161)=k9_relat_1('#skF_4', D_161))), inference(resolution, [status(thm)], [c_62, c_768])).
% 4.65/2.19  tff(c_878, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_58])).
% 4.65/2.19  tff(c_1817, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_878])).
% 4.65/2.19  tff(c_1824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1817])).
% 4.65/2.19  tff(c_1826, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_595])).
% 4.65/2.19  tff(c_1832, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1826, c_62])).
% 4.65/2.19  tff(c_1883, plain, (![A_247, B_248, C_249, D_250]: (k7_relset_1(A_247, B_248, C_249, D_250)=k9_relat_1(C_249, D_250) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.65/2.19  tff(c_1896, plain, (![D_250]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_250)=k9_relat_1('#skF_4', D_250))), inference(resolution, [status(thm)], [c_1832, c_1883])).
% 4.65/2.19  tff(c_1825, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_595])).
% 4.65/2.19  tff(c_1908, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1826, c_1825])).
% 4.65/2.19  tff(c_1916, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1896, c_1908])).
% 4.65/2.19  tff(c_1928, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_1916])).
% 4.65/2.19  tff(c_1932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_1928])).
% 4.65/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/2.19  
% 4.65/2.19  Inference rules
% 4.65/2.19  ----------------------
% 4.65/2.19  #Ref     : 0
% 4.65/2.19  #Sup     : 380
% 4.65/2.19  #Fact    : 0
% 4.65/2.19  #Define  : 0
% 4.65/2.19  #Split   : 2
% 4.65/2.19  #Chain   : 0
% 4.65/2.19  #Close   : 0
% 4.65/2.19  
% 4.65/2.19  Ordering : KBO
% 4.65/2.19  
% 4.65/2.19  Simplification rules
% 4.65/2.19  ----------------------
% 4.65/2.19  #Subsume      : 38
% 4.65/2.19  #Demod        : 471
% 4.65/2.19  #Tautology    : 225
% 4.65/2.19  #SimpNegUnit  : 2
% 4.65/2.19  #BackRed      : 25
% 4.65/2.19  
% 4.65/2.19  #Partial instantiations: 0
% 4.65/2.19  #Strategies tried      : 1
% 4.65/2.19  
% 4.65/2.19  Timing (in seconds)
% 4.65/2.19  ----------------------
% 4.65/2.20  Preprocessing        : 0.53
% 4.65/2.20  Parsing              : 0.27
% 4.65/2.20  CNF conversion       : 0.04
% 4.65/2.20  Main loop            : 0.77
% 4.65/2.20  Inferencing          : 0.27
% 4.65/2.20  Reduction            : 0.27
% 4.65/2.20  Demodulation         : 0.20
% 4.65/2.20  BG Simplification    : 0.04
% 4.65/2.20  Subsumption          : 0.14
% 4.65/2.20  Abstraction          : 0.03
% 4.65/2.20  MUC search           : 0.00
% 4.65/2.20  Cooper               : 0.00
% 4.65/2.20  Total                : 1.34
% 4.65/2.20  Index Insertion      : 0.00
% 4.65/2.20  Index Deletion       : 0.00
% 4.65/2.20  Index Matching       : 0.00
% 4.65/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
