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
% DateTime   : Thu Dec  3 10:14:44 EST 2020

% Result     : Theorem 6.77s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 472 expanded)
%              Number of leaves         :   44 ( 182 expanded)
%              Depth                    :   15
%              Number of atoms          :  159 ( 993 expanded)
%              Number of equality atoms :   46 ( 275 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_130,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_143,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_130])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    ! [A_34] : k2_zfmisc_1(A_34,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    ! [A_57] :
      ( m1_subset_1(A_57,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_57),k2_relat_1(A_57))))
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1026,plain,(
    ! [A_208,B_209,C_210,D_211] :
      ( k7_relset_1(A_208,B_209,C_210,D_211) = k9_relat_1(C_210,D_211)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1042,plain,(
    ! [A_57,D_211] :
      ( k7_relset_1(k1_relat_1(A_57),k2_relat_1(A_57),A_57,D_211) = k9_relat_1(A_57,D_211)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(resolution,[status(thm)],[c_60,c_1026])).

tff(c_970,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( m1_subset_1(k7_relset_1(A_194,B_195,C_196,D_197),k1_zfmisc_1(B_195))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2941,plain,(
    ! [A_397,B_398,C_399,D_400] :
      ( r1_tarski(k7_relset_1(A_397,B_398,C_399,D_400),B_398)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(A_397,B_398))) ) ),
    inference(resolution,[status(thm)],[c_970,c_36])).

tff(c_5427,plain,(
    ! [A_547,D_548] :
      ( r1_tarski(k7_relset_1(k1_relat_1(A_547),k2_relat_1(A_547),A_547,D_548),k2_relat_1(A_547))
      | ~ v1_funct_1(A_547)
      | ~ v1_relat_1(A_547) ) ),
    inference(resolution,[status(thm)],[c_60,c_2941])).

tff(c_5501,plain,(
    ! [A_549,D_550] :
      ( r1_tarski(k9_relat_1(A_549,D_550),k2_relat_1(A_549))
      | ~ v1_funct_1(A_549)
      | ~ v1_relat_1(A_549)
      | ~ v1_funct_1(A_549)
      | ~ v1_relat_1(A_549) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_5427])).

tff(c_172,plain,(
    ! [A_76] :
      ( k2_relat_1(A_76) = k1_xboole_0
      | k1_relat_1(A_76) != k1_xboole_0
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_176,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_143,c_172])).

tff(c_182,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_1070,plain,(
    ! [B_216,A_217] :
      ( k1_tarski(k1_funct_1(B_216,A_217)) = k2_relat_1(B_216)
      | k1_tarski(A_217) != k1_relat_1(B_216)
      | ~ v1_funct_1(B_216)
      | ~ v1_relat_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1044,plain,(
    ! [D_211] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_211) = k9_relat_1('#skF_4',D_211) ),
    inference(resolution,[status(thm)],[c_70,c_1026])).

tff(c_66,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1045,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1044,c_66])).

tff(c_1076,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1070,c_1045])).

tff(c_1085,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_74,c_1076])).

tff(c_1087,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1085])).

tff(c_540,plain,(
    ! [C_136,A_137,B_138] :
      ( v4_relat_1(C_136,A_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_555,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_540])).

tff(c_42,plain,(
    ! [B_39,A_38] :
      ( r1_tarski(k1_relat_1(B_39),A_38)
      | ~ v4_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_647,plain,(
    ! [B_151,A_152] :
      ( k1_tarski(B_151) = A_152
      | k1_xboole_0 = A_152
      | ~ r1_tarski(A_152,k1_tarski(B_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1738,plain,(
    ! [B_296,B_297] :
      ( k1_tarski(B_296) = k1_relat_1(B_297)
      | k1_relat_1(B_297) = k1_xboole_0
      | ~ v4_relat_1(B_297,k1_tarski(B_296))
      | ~ v1_relat_1(B_297) ) ),
    inference(resolution,[status(thm)],[c_42,c_647])).

tff(c_1772,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_555,c_1738])).

tff(c_1792,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_1772])).

tff(c_1794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_1087,c_1792])).

tff(c_1795,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1085])).

tff(c_5506,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5501,c_1795])).

tff(c_5531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_74,c_5506])).

tff(c_5532,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_5533,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_6303,plain,(
    ! [A_661] :
      ( m1_subset_1(A_661,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_661),k2_relat_1(A_661))))
      | ~ v1_funct_1(A_661)
      | ~ v1_relat_1(A_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6324,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4'))))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5533,c_6303])).

tff(c_6337,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_74,c_32,c_5532,c_6324])).

tff(c_6356,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6337,c_36])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5534,plain,(
    ! [B_551,A_552] :
      ( B_551 = A_552
      | ~ r1_tarski(B_551,A_552)
      | ~ r1_tarski(A_552,B_551) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5542,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_5534])).

tff(c_6367,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6356,c_5542])).

tff(c_6398,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6367,c_8])).

tff(c_6327,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0)))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5532,c_6303])).

tff(c_6339,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_74,c_32,c_5533,c_6327])).

tff(c_6488,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6367,c_6339])).

tff(c_38,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,k1_zfmisc_1(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6665,plain,(
    ! [A_683,B_684,C_685,D_686] :
      ( k7_relset_1(A_683,B_684,C_685,D_686) = k9_relat_1(C_685,D_686)
      | ~ m1_subset_1(C_685,k1_zfmisc_1(k2_zfmisc_1(A_683,B_684))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7152,plain,(
    ! [A_754,B_755,A_756,D_757] :
      ( k7_relset_1(A_754,B_755,A_756,D_757) = k9_relat_1(A_756,D_757)
      | ~ r1_tarski(A_756,k2_zfmisc_1(A_754,B_755)) ) ),
    inference(resolution,[status(thm)],[c_38,c_6665])).

tff(c_7169,plain,(
    ! [A_754,B_755,D_757] : k7_relset_1(A_754,B_755,'#skF_4',D_757) = k9_relat_1('#skF_4',D_757) ),
    inference(resolution,[status(thm)],[c_6398,c_7152])).

tff(c_6396,plain,(
    ! [A_34] : k2_zfmisc_1(A_34,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6367,c_6367,c_32])).

tff(c_6581,plain,(
    ! [A_674,B_675,C_676,D_677] :
      ( m1_subset_1(k7_relset_1(A_674,B_675,C_676,D_677),k1_zfmisc_1(B_675))
      | ~ m1_subset_1(C_676,k1_zfmisc_1(k2_zfmisc_1(A_674,B_675))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7281,plain,(
    ! [A_770,B_771,C_772,D_773] :
      ( r1_tarski(k7_relset_1(A_770,B_771,C_772,D_773),B_771)
      | ~ m1_subset_1(C_772,k1_zfmisc_1(k2_zfmisc_1(A_770,B_771))) ) ),
    inference(resolution,[status(thm)],[c_6581,c_36])).

tff(c_7836,plain,(
    ! [A_827,C_828,D_829] :
      ( r1_tarski(k7_relset_1(A_827,'#skF_4',C_828,D_829),'#skF_4')
      | ~ m1_subset_1(C_828,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6396,c_7281])).

tff(c_7855,plain,(
    ! [D_757] :
      ( r1_tarski(k9_relat_1('#skF_4',D_757),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7169,c_7836])).

tff(c_7867,plain,(
    ! [D_830] : r1_tarski(k9_relat_1('#skF_4',D_830),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_7855])).

tff(c_6388,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6367,c_6367,c_5542])).

tff(c_7890,plain,(
    ! [D_830] : k9_relat_1('#skF_4',D_830) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7867,c_6388])).

tff(c_6683,plain,(
    ! [D_686] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_686) = k9_relat_1('#skF_4',D_686) ),
    inference(resolution,[status(thm)],[c_70,c_6665])).

tff(c_6686,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6683,c_66])).

tff(c_7905,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7890,c_6686])).

tff(c_7921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6398,c_7905])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.77/2.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.43  
% 6.77/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.77/2.43  
% 6.77/2.43  %Foreground sorts:
% 6.77/2.43  
% 6.77/2.43  
% 6.77/2.43  %Background operators:
% 6.77/2.43  
% 6.77/2.43  
% 6.77/2.43  %Foreground operators:
% 6.77/2.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.77/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.77/2.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.77/2.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.77/2.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.77/2.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.77/2.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.77/2.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.77/2.43  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.77/2.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.77/2.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.77/2.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.77/2.43  tff('#skF_2', type, '#skF_2': $i).
% 6.77/2.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.77/2.43  tff('#skF_3', type, '#skF_3': $i).
% 6.77/2.43  tff('#skF_1', type, '#skF_1': $i).
% 6.77/2.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.77/2.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.77/2.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.77/2.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.77/2.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.77/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.77/2.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.77/2.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.77/2.43  tff('#skF_4', type, '#skF_4': $i).
% 6.77/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.77/2.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.77/2.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.77/2.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.77/2.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.77/2.43  
% 6.77/2.45  tff(f_123, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 6.77/2.45  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.77/2.45  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.77/2.45  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 6.77/2.45  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.77/2.45  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 6.77/2.45  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.77/2.45  tff(f_75, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 6.77/2.45  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 6.77/2.45  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.77/2.45  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 6.77/2.45  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.77/2.45  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.77/2.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.77/2.45  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.77/2.45  tff(c_130, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.77/2.45  tff(c_143, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_130])).
% 6.77/2.45  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.77/2.45  tff(c_32, plain, (![A_34]: (k2_zfmisc_1(A_34, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.77/2.45  tff(c_60, plain, (![A_57]: (m1_subset_1(A_57, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_57), k2_relat_1(A_57)))) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.77/2.45  tff(c_1026, plain, (![A_208, B_209, C_210, D_211]: (k7_relset_1(A_208, B_209, C_210, D_211)=k9_relat_1(C_210, D_211) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.77/2.45  tff(c_1042, plain, (![A_57, D_211]: (k7_relset_1(k1_relat_1(A_57), k2_relat_1(A_57), A_57, D_211)=k9_relat_1(A_57, D_211) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(resolution, [status(thm)], [c_60, c_1026])).
% 6.77/2.45  tff(c_970, plain, (![A_194, B_195, C_196, D_197]: (m1_subset_1(k7_relset_1(A_194, B_195, C_196, D_197), k1_zfmisc_1(B_195)) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.77/2.45  tff(c_36, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.77/2.45  tff(c_2941, plain, (![A_397, B_398, C_399, D_400]: (r1_tarski(k7_relset_1(A_397, B_398, C_399, D_400), B_398) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(A_397, B_398))))), inference(resolution, [status(thm)], [c_970, c_36])).
% 6.77/2.45  tff(c_5427, plain, (![A_547, D_548]: (r1_tarski(k7_relset_1(k1_relat_1(A_547), k2_relat_1(A_547), A_547, D_548), k2_relat_1(A_547)) | ~v1_funct_1(A_547) | ~v1_relat_1(A_547))), inference(resolution, [status(thm)], [c_60, c_2941])).
% 6.77/2.45  tff(c_5501, plain, (![A_549, D_550]: (r1_tarski(k9_relat_1(A_549, D_550), k2_relat_1(A_549)) | ~v1_funct_1(A_549) | ~v1_relat_1(A_549) | ~v1_funct_1(A_549) | ~v1_relat_1(A_549))), inference(superposition, [status(thm), theory('equality')], [c_1042, c_5427])).
% 6.77/2.45  tff(c_172, plain, (![A_76]: (k2_relat_1(A_76)=k1_xboole_0 | k1_relat_1(A_76)!=k1_xboole_0 | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.77/2.45  tff(c_176, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_143, c_172])).
% 6.77/2.45  tff(c_182, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_176])).
% 6.77/2.45  tff(c_1070, plain, (![B_216, A_217]: (k1_tarski(k1_funct_1(B_216, A_217))=k2_relat_1(B_216) | k1_tarski(A_217)!=k1_relat_1(B_216) | ~v1_funct_1(B_216) | ~v1_relat_1(B_216))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.77/2.45  tff(c_1044, plain, (![D_211]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_211)=k9_relat_1('#skF_4', D_211))), inference(resolution, [status(thm)], [c_70, c_1026])).
% 6.77/2.45  tff(c_66, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.77/2.45  tff(c_1045, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1044, c_66])).
% 6.77/2.45  tff(c_1076, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1070, c_1045])).
% 6.77/2.45  tff(c_1085, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_74, c_1076])).
% 6.77/2.45  tff(c_1087, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1085])).
% 6.77/2.45  tff(c_540, plain, (![C_136, A_137, B_138]: (v4_relat_1(C_136, A_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.77/2.45  tff(c_555, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_540])).
% 6.77/2.45  tff(c_42, plain, (![B_39, A_38]: (r1_tarski(k1_relat_1(B_39), A_38) | ~v4_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.77/2.45  tff(c_647, plain, (![B_151, A_152]: (k1_tarski(B_151)=A_152 | k1_xboole_0=A_152 | ~r1_tarski(A_152, k1_tarski(B_151)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.77/2.45  tff(c_1738, plain, (![B_296, B_297]: (k1_tarski(B_296)=k1_relat_1(B_297) | k1_relat_1(B_297)=k1_xboole_0 | ~v4_relat_1(B_297, k1_tarski(B_296)) | ~v1_relat_1(B_297))), inference(resolution, [status(thm)], [c_42, c_647])).
% 6.77/2.45  tff(c_1772, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_555, c_1738])).
% 6.77/2.45  tff(c_1792, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_143, c_1772])).
% 6.77/2.45  tff(c_1794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_1087, c_1792])).
% 6.77/2.45  tff(c_1795, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1085])).
% 6.77/2.45  tff(c_5506, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5501, c_1795])).
% 6.77/2.45  tff(c_5531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_74, c_5506])).
% 6.77/2.45  tff(c_5532, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_176])).
% 6.77/2.45  tff(c_5533, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_176])).
% 6.77/2.45  tff(c_6303, plain, (![A_661]: (m1_subset_1(A_661, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_661), k2_relat_1(A_661)))) | ~v1_funct_1(A_661) | ~v1_relat_1(A_661))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.77/2.45  tff(c_6324, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5533, c_6303])).
% 6.77/2.45  tff(c_6337, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_74, c_32, c_5532, c_6324])).
% 6.77/2.45  tff(c_6356, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_6337, c_36])).
% 6.77/2.45  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.77/2.45  tff(c_5534, plain, (![B_551, A_552]: (B_551=A_552 | ~r1_tarski(B_551, A_552) | ~r1_tarski(A_552, B_551))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.45  tff(c_5542, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_5534])).
% 6.77/2.45  tff(c_6367, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6356, c_5542])).
% 6.77/2.45  tff(c_6398, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_6367, c_8])).
% 6.77/2.45  tff(c_6327, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5532, c_6303])).
% 6.77/2.45  tff(c_6339, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_74, c_32, c_5533, c_6327])).
% 6.77/2.45  tff(c_6488, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6367, c_6339])).
% 6.77/2.45  tff(c_38, plain, (![A_36, B_37]: (m1_subset_1(A_36, k1_zfmisc_1(B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.77/2.45  tff(c_6665, plain, (![A_683, B_684, C_685, D_686]: (k7_relset_1(A_683, B_684, C_685, D_686)=k9_relat_1(C_685, D_686) | ~m1_subset_1(C_685, k1_zfmisc_1(k2_zfmisc_1(A_683, B_684))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.77/2.45  tff(c_7152, plain, (![A_754, B_755, A_756, D_757]: (k7_relset_1(A_754, B_755, A_756, D_757)=k9_relat_1(A_756, D_757) | ~r1_tarski(A_756, k2_zfmisc_1(A_754, B_755)))), inference(resolution, [status(thm)], [c_38, c_6665])).
% 6.77/2.45  tff(c_7169, plain, (![A_754, B_755, D_757]: (k7_relset_1(A_754, B_755, '#skF_4', D_757)=k9_relat_1('#skF_4', D_757))), inference(resolution, [status(thm)], [c_6398, c_7152])).
% 6.77/2.45  tff(c_6396, plain, (![A_34]: (k2_zfmisc_1(A_34, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6367, c_6367, c_32])).
% 6.77/2.45  tff(c_6581, plain, (![A_674, B_675, C_676, D_677]: (m1_subset_1(k7_relset_1(A_674, B_675, C_676, D_677), k1_zfmisc_1(B_675)) | ~m1_subset_1(C_676, k1_zfmisc_1(k2_zfmisc_1(A_674, B_675))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.77/2.45  tff(c_7281, plain, (![A_770, B_771, C_772, D_773]: (r1_tarski(k7_relset_1(A_770, B_771, C_772, D_773), B_771) | ~m1_subset_1(C_772, k1_zfmisc_1(k2_zfmisc_1(A_770, B_771))))), inference(resolution, [status(thm)], [c_6581, c_36])).
% 6.77/2.45  tff(c_7836, plain, (![A_827, C_828, D_829]: (r1_tarski(k7_relset_1(A_827, '#skF_4', C_828, D_829), '#skF_4') | ~m1_subset_1(C_828, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6396, c_7281])).
% 6.77/2.45  tff(c_7855, plain, (![D_757]: (r1_tarski(k9_relat_1('#skF_4', D_757), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_7169, c_7836])).
% 6.77/2.45  tff(c_7867, plain, (![D_830]: (r1_tarski(k9_relat_1('#skF_4', D_830), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_7855])).
% 6.77/2.45  tff(c_6388, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6367, c_6367, c_5542])).
% 6.77/2.45  tff(c_7890, plain, (![D_830]: (k9_relat_1('#skF_4', D_830)='#skF_4')), inference(resolution, [status(thm)], [c_7867, c_6388])).
% 6.77/2.45  tff(c_6683, plain, (![D_686]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_686)=k9_relat_1('#skF_4', D_686))), inference(resolution, [status(thm)], [c_70, c_6665])).
% 6.77/2.45  tff(c_6686, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6683, c_66])).
% 6.77/2.45  tff(c_7905, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_7890, c_6686])).
% 6.77/2.45  tff(c_7921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6398, c_7905])).
% 6.77/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.45  
% 6.77/2.45  Inference rules
% 6.77/2.45  ----------------------
% 6.77/2.45  #Ref     : 0
% 6.77/2.45  #Sup     : 1622
% 6.77/2.45  #Fact    : 4
% 6.77/2.45  #Define  : 0
% 6.77/2.45  #Split   : 12
% 6.77/2.45  #Chain   : 0
% 6.77/2.45  #Close   : 0
% 6.77/2.45  
% 6.77/2.45  Ordering : KBO
% 6.77/2.45  
% 6.77/2.45  Simplification rules
% 6.77/2.45  ----------------------
% 6.77/2.45  #Subsume      : 195
% 6.77/2.45  #Demod        : 2031
% 6.77/2.45  #Tautology    : 788
% 6.77/2.45  #SimpNegUnit  : 33
% 6.77/2.45  #BackRed      : 99
% 6.77/2.45  
% 6.77/2.45  #Partial instantiations: 0
% 6.77/2.45  #Strategies tried      : 1
% 6.77/2.45  
% 6.77/2.45  Timing (in seconds)
% 6.77/2.45  ----------------------
% 6.77/2.45  Preprocessing        : 0.35
% 6.77/2.45  Parsing              : 0.19
% 6.77/2.45  CNF conversion       : 0.02
% 6.77/2.45  Main loop            : 1.33
% 6.77/2.45  Inferencing          : 0.47
% 6.77/2.45  Reduction            : 0.48
% 6.77/2.45  Demodulation         : 0.35
% 6.77/2.45  BG Simplification    : 0.05
% 6.77/2.45  Subsumption          : 0.24
% 6.77/2.45  Abstraction          : 0.06
% 6.77/2.45  MUC search           : 0.00
% 6.77/2.45  Cooper               : 0.00
% 6.77/2.45  Total                : 1.72
% 6.77/2.45  Index Insertion      : 0.00
% 6.77/2.45  Index Deletion       : 0.00
% 6.77/2.45  Index Matching       : 0.00
% 6.77/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
