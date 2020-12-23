%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:58 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 593 expanded)
%              Number of leaves         :   42 ( 223 expanded)
%              Depth                    :   15
%              Number of atoms          :  151 (1281 expanded)
%              Number of equality atoms :   39 ( 287 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_44,plain,(
    ! [A_26,B_27] : v1_relat_1(k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_149,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_152,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_149])).

tff(c_161,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_152])).

tff(c_46,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k9_relat_1(B_29,A_28),k2_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_24,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1910,plain,(
    ! [B_230,A_231] :
      ( k1_tarski(k1_funct_1(B_230,A_231)) = k2_relat_1(B_230)
      | k1_tarski(A_231) != k1_relat_1(B_230)
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1873,plain,(
    ! [A_222,B_223,C_224,D_225] :
      ( k7_relset_1(A_222,B_223,C_224,D_225) = k9_relat_1(C_224,D_225)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1889,plain,(
    ! [D_225] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_225) = k9_relat_1('#skF_4',D_225) ),
    inference(resolution,[status(thm)],[c_66,c_1873])).

tff(c_62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1900,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1889,c_62])).

tff(c_1916,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_1900])).

tff(c_1925,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_70,c_1916])).

tff(c_2031,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1925])).

tff(c_248,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_266,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_248])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_269,plain,(
    ! [B_78,A_79] :
      ( k1_tarski(B_78) = A_79
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,k1_tarski(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3009,plain,(
    ! [B_317,B_318] :
      ( k1_tarski(B_317) = k1_relat_1(B_318)
      | k1_relat_1(B_318) = k1_xboole_0
      | ~ v4_relat_1(B_318,k1_tarski(B_317))
      | ~ v1_relat_1(B_318) ) ),
    inference(resolution,[status(thm)],[c_38,c_269])).

tff(c_3047,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_266,c_3009])).

tff(c_3064,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_3047])).

tff(c_3065,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2031,c_3064])).

tff(c_1782,plain,(
    ! [A_214] :
      ( m1_subset_1(A_214,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_214),k2_relat_1(A_214))))
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1809,plain,(
    ! [A_214] :
      ( r1_tarski(A_214,k2_zfmisc_1(k1_relat_1(A_214),k2_relat_1(A_214)))
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(resolution,[status(thm)],[c_1782,c_28])).

tff(c_3097,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3065,c_1809])).

tff(c_3132,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_70,c_24,c_3097])).

tff(c_26,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_117,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_26,c_113])).

tff(c_181,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_117,c_181])).

tff(c_3175,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3132,c_189])).

tff(c_3239,plain,(
    ! [A_13] : r1_tarski('#skF_4',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3175,c_117])).

tff(c_22,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,(
    ! [A_44,B_45] : v1_relat_1(k2_zfmisc_1(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_99,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_314,plain,(
    ! [C_81,B_82,A_83] :
      ( v5_relat_1(C_81,B_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_407,plain,(
    ! [A_100,B_101,A_102] :
      ( v5_relat_1(A_100,B_101)
      | ~ r1_tarski(A_100,k2_zfmisc_1(A_102,B_101)) ) ),
    inference(resolution,[status(thm)],[c_30,c_314])).

tff(c_439,plain,(
    ! [A_102,B_101] : v5_relat_1(k2_zfmisc_1(A_102,B_101),B_101) ),
    inference(resolution,[status(thm)],[c_6,c_407])).

tff(c_385,plain,(
    ! [B_98,A_99] :
      ( r1_tarski(k2_relat_1(B_98),A_99)
      | ~ v5_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_509,plain,(
    ! [B_115] :
      ( k2_relat_1(B_115) = k1_xboole_0
      | ~ v5_relat_1(B_115,k1_xboole_0)
      | ~ v1_relat_1(B_115) ) ),
    inference(resolution,[status(thm)],[c_385,c_189])).

tff(c_513,plain,(
    ! [A_102] :
      ( k2_relat_1(k2_zfmisc_1(A_102,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_102,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_439,c_509])).

tff(c_524,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_22,c_22,c_513])).

tff(c_3225,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3175,c_3175,c_524])).

tff(c_207,plain,(
    ! [B_64,A_65] :
      ( r1_tarski(k9_relat_1(B_64,A_65),k2_relat_1(B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3457,plain,(
    ! [B_326,A_327] :
      ( k9_relat_1(B_326,A_327) = k2_relat_1(B_326)
      | ~ r1_tarski(k2_relat_1(B_326),k9_relat_1(B_326,A_327))
      | ~ v1_relat_1(B_326) ) ),
    inference(resolution,[status(thm)],[c_207,c_2])).

tff(c_3460,plain,(
    ! [A_327] :
      ( k9_relat_1('#skF_4',A_327) = k2_relat_1('#skF_4')
      | ~ r1_tarski('#skF_4',k9_relat_1('#skF_4',A_327))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3225,c_3457])).

tff(c_3466,plain,(
    ! [A_327] : k9_relat_1('#skF_4',A_327) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_3239,c_3225,c_3460])).

tff(c_3663,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3466,c_1900])).

tff(c_3667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3239,c_3663])).

tff(c_3668,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1925])).

tff(c_3721,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_3668])).

tff(c_3725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_3721])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:55:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.94/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/2.02  
% 4.94/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/2.02  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.94/2.02  
% 4.94/2.02  %Foreground sorts:
% 4.94/2.02  
% 4.94/2.02  
% 4.94/2.02  %Background operators:
% 4.94/2.02  
% 4.94/2.02  
% 4.94/2.02  %Foreground operators:
% 4.94/2.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.94/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.94/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.94/2.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.94/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.94/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.94/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.94/2.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.94/2.02  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.94/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.94/2.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.94/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.94/2.02  tff('#skF_2', type, '#skF_2': $i).
% 4.94/2.02  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.94/2.02  tff('#skF_3', type, '#skF_3': $i).
% 4.94/2.02  tff('#skF_1', type, '#skF_1': $i).
% 4.94/2.02  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.94/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.94/2.02  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.94/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.94/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.94/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.94/2.02  tff('#skF_4', type, '#skF_4': $i).
% 4.94/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.94/2.02  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.94/2.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.94/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.94/2.02  
% 4.94/2.03  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.94/2.03  tff(f_126, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 4.94/2.03  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.94/2.03  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 4.94/2.03  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.94/2.03  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 4.94/2.03  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.94/2.03  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.94/2.03  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.94/2.03  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.94/2.03  tff(f_114, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.94/2.03  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.94/2.03  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.94/2.03  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.94/2.03  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.94/2.03  tff(c_44, plain, (![A_26, B_27]: (v1_relat_1(k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.94/2.03  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.94/2.03  tff(c_149, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.94/2.03  tff(c_152, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_149])).
% 4.94/2.03  tff(c_161, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_152])).
% 4.94/2.03  tff(c_46, plain, (![B_29, A_28]: (r1_tarski(k9_relat_1(B_29, A_28), k2_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.94/2.03  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.94/2.03  tff(c_24, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.94/2.03  tff(c_1910, plain, (![B_230, A_231]: (k1_tarski(k1_funct_1(B_230, A_231))=k2_relat_1(B_230) | k1_tarski(A_231)!=k1_relat_1(B_230) | ~v1_funct_1(B_230) | ~v1_relat_1(B_230))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.94/2.03  tff(c_1873, plain, (![A_222, B_223, C_224, D_225]: (k7_relset_1(A_222, B_223, C_224, D_225)=k9_relat_1(C_224, D_225) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.94/2.03  tff(c_1889, plain, (![D_225]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_225)=k9_relat_1('#skF_4', D_225))), inference(resolution, [status(thm)], [c_66, c_1873])).
% 4.94/2.03  tff(c_62, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.94/2.03  tff(c_1900, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1889, c_62])).
% 4.94/2.03  tff(c_1916, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1910, c_1900])).
% 4.94/2.03  tff(c_1925, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_70, c_1916])).
% 4.94/2.03  tff(c_2031, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1925])).
% 4.94/2.03  tff(c_248, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.94/2.03  tff(c_266, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_248])).
% 4.94/2.03  tff(c_38, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(B_23), A_22) | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.94/2.03  tff(c_269, plain, (![B_78, A_79]: (k1_tarski(B_78)=A_79 | k1_xboole_0=A_79 | ~r1_tarski(A_79, k1_tarski(B_78)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.94/2.03  tff(c_3009, plain, (![B_317, B_318]: (k1_tarski(B_317)=k1_relat_1(B_318) | k1_relat_1(B_318)=k1_xboole_0 | ~v4_relat_1(B_318, k1_tarski(B_317)) | ~v1_relat_1(B_318))), inference(resolution, [status(thm)], [c_38, c_269])).
% 4.94/2.03  tff(c_3047, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_266, c_3009])).
% 4.94/2.03  tff(c_3064, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_161, c_3047])).
% 4.94/2.03  tff(c_3065, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2031, c_3064])).
% 4.94/2.03  tff(c_1782, plain, (![A_214]: (m1_subset_1(A_214, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_214), k2_relat_1(A_214)))) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.94/2.03  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.94/2.03  tff(c_1809, plain, (![A_214]: (r1_tarski(A_214, k2_zfmisc_1(k1_relat_1(A_214), k2_relat_1(A_214))) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(resolution, [status(thm)], [c_1782, c_28])).
% 4.94/2.03  tff(c_3097, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3065, c_1809])).
% 4.94/2.03  tff(c_3132, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_70, c_24, c_3097])).
% 4.94/2.03  tff(c_26, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.94/2.03  tff(c_113, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.94/2.03  tff(c_117, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_26, c_113])).
% 4.94/2.03  tff(c_181, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.94/2.03  tff(c_189, plain, (![A_13]: (k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_117, c_181])).
% 4.94/2.03  tff(c_3175, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3132, c_189])).
% 4.94/2.03  tff(c_3239, plain, (![A_13]: (r1_tarski('#skF_4', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_3175, c_117])).
% 4.94/2.03  tff(c_22, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.94/2.03  tff(c_97, plain, (![A_44, B_45]: (v1_relat_1(k2_zfmisc_1(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.94/2.03  tff(c_99, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_97])).
% 4.94/2.03  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.94/2.03  tff(c_30, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.94/2.03  tff(c_314, plain, (![C_81, B_82, A_83]: (v5_relat_1(C_81, B_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.94/2.03  tff(c_407, plain, (![A_100, B_101, A_102]: (v5_relat_1(A_100, B_101) | ~r1_tarski(A_100, k2_zfmisc_1(A_102, B_101)))), inference(resolution, [status(thm)], [c_30, c_314])).
% 4.94/2.03  tff(c_439, plain, (![A_102, B_101]: (v5_relat_1(k2_zfmisc_1(A_102, B_101), B_101))), inference(resolution, [status(thm)], [c_6, c_407])).
% 4.94/2.03  tff(c_385, plain, (![B_98, A_99]: (r1_tarski(k2_relat_1(B_98), A_99) | ~v5_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.94/2.03  tff(c_509, plain, (![B_115]: (k2_relat_1(B_115)=k1_xboole_0 | ~v5_relat_1(B_115, k1_xboole_0) | ~v1_relat_1(B_115))), inference(resolution, [status(thm)], [c_385, c_189])).
% 4.94/2.03  tff(c_513, plain, (![A_102]: (k2_relat_1(k2_zfmisc_1(A_102, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_102, k1_xboole_0)))), inference(resolution, [status(thm)], [c_439, c_509])).
% 4.94/2.03  tff(c_524, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_99, c_22, c_22, c_513])).
% 4.94/2.03  tff(c_3225, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3175, c_3175, c_524])).
% 4.94/2.03  tff(c_207, plain, (![B_64, A_65]: (r1_tarski(k9_relat_1(B_64, A_65), k2_relat_1(B_64)) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.94/2.03  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.94/2.03  tff(c_3457, plain, (![B_326, A_327]: (k9_relat_1(B_326, A_327)=k2_relat_1(B_326) | ~r1_tarski(k2_relat_1(B_326), k9_relat_1(B_326, A_327)) | ~v1_relat_1(B_326))), inference(resolution, [status(thm)], [c_207, c_2])).
% 4.94/2.03  tff(c_3460, plain, (![A_327]: (k9_relat_1('#skF_4', A_327)=k2_relat_1('#skF_4') | ~r1_tarski('#skF_4', k9_relat_1('#skF_4', A_327)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3225, c_3457])).
% 4.94/2.03  tff(c_3466, plain, (![A_327]: (k9_relat_1('#skF_4', A_327)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_3239, c_3225, c_3460])).
% 4.94/2.03  tff(c_3663, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3466, c_1900])).
% 4.94/2.03  tff(c_3667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3239, c_3663])).
% 4.94/2.03  tff(c_3668, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1925])).
% 4.94/2.03  tff(c_3721, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_3668])).
% 4.94/2.03  tff(c_3725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_3721])).
% 4.94/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/2.03  
% 4.94/2.03  Inference rules
% 4.94/2.03  ----------------------
% 4.94/2.03  #Ref     : 0
% 4.94/2.03  #Sup     : 739
% 4.94/2.03  #Fact    : 0
% 4.94/2.03  #Define  : 0
% 4.94/2.03  #Split   : 12
% 4.94/2.03  #Chain   : 0
% 4.94/2.03  #Close   : 0
% 4.94/2.03  
% 4.94/2.03  Ordering : KBO
% 4.94/2.03  
% 4.94/2.03  Simplification rules
% 4.94/2.03  ----------------------
% 4.94/2.03  #Subsume      : 160
% 4.94/2.03  #Demod        : 931
% 4.94/2.03  #Tautology    : 322
% 4.94/2.03  #SimpNegUnit  : 46
% 4.94/2.03  #BackRed      : 133
% 4.94/2.03  
% 4.94/2.03  #Partial instantiations: 0
% 4.94/2.03  #Strategies tried      : 1
% 4.94/2.03  
% 4.94/2.03  Timing (in seconds)
% 4.94/2.03  ----------------------
% 4.94/2.04  Preprocessing        : 0.37
% 4.94/2.04  Parsing              : 0.19
% 4.94/2.04  CNF conversion       : 0.03
% 4.94/2.04  Main loop            : 0.80
% 4.94/2.04  Inferencing          : 0.27
% 4.94/2.04  Reduction            : 0.28
% 4.94/2.04  Demodulation         : 0.20
% 4.94/2.04  BG Simplification    : 0.03
% 4.94/2.04  Subsumption          : 0.16
% 4.94/2.04  Abstraction          : 0.05
% 4.94/2.04  MUC search           : 0.00
% 4.94/2.04  Cooper               : 0.00
% 4.94/2.04  Total                : 1.20
% 4.94/2.04  Index Insertion      : 0.00
% 4.94/2.04  Index Deletion       : 0.00
% 4.94/2.04  Index Matching       : 0.00
% 4.94/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
