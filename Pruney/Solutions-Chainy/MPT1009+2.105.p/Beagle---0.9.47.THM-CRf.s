%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:56 EST 2020

% Result     : Theorem 5.88s
% Output     : CNFRefutation 6.03s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 848 expanded)
%              Number of leaves         :   39 ( 296 expanded)
%              Depth                    :   14
%              Number of atoms          :  250 (1806 expanded)
%              Number of equality atoms :   81 ( 437 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4102,plain,(
    ! [C_466,A_467,B_468] :
      ( v4_relat_1(C_466,A_467)
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_467,B_468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4216,plain,(
    ! [C_479,A_480] :
      ( v4_relat_1(C_479,A_480)
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4102])).

tff(c_4222,plain,(
    ! [A_482,A_483] :
      ( v4_relat_1(A_482,A_483)
      | ~ r1_tarski(A_482,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_4216])).

tff(c_93,plain,(
    ! [A_40,B_41] : v1_relat_1(k2_zfmisc_1(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_95,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_93])).

tff(c_1872,plain,(
    ! [C_242,A_243,B_244] :
      ( v4_relat_1(C_242,A_243)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1888,plain,(
    ! [C_245,A_246] :
      ( v4_relat_1(C_245,A_246)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1872])).

tff(c_1892,plain,(
    ! [A_10,A_246] :
      ( v4_relat_1(A_10,A_246)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_1888])).

tff(c_36,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_177,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_180,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_177])).

tff(c_186,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_180])).

tff(c_38,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k9_relat_1(B_24,A_23),k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [A_25] :
      ( k2_relat_1(A_25) = k1_xboole_0
      | k1_relat_1(A_25) != k1_xboole_0
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_194,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_186,c_42])).

tff(c_196,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_550,plain,(
    ! [B_114,A_115] :
      ( k1_tarski(k1_funct_1(B_114,A_115)) = k2_relat_1(B_114)
      | k1_tarski(A_115) != k1_relat_1(B_114)
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_562,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_58])).

tff(c_570,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_66,c_562])).

tff(c_574,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_570])).

tff(c_225,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_239,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_225])).

tff(c_34,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_290,plain,(
    ! [B_80,A_81] :
      ( k1_tarski(B_80) = A_81
      | k1_xboole_0 = A_81
      | ~ r1_tarski(A_81,k1_tarski(B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1500,plain,(
    ! [B_224,B_225] :
      ( k1_tarski(B_224) = k1_relat_1(B_225)
      | k1_relat_1(B_225) = k1_xboole_0
      | ~ v4_relat_1(B_225,k1_tarski(B_224))
      | ~ v1_relat_1(B_225) ) ),
    inference(resolution,[status(thm)],[c_34,c_290])).

tff(c_1571,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_239,c_1500])).

tff(c_1605,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_1571])).

tff(c_1607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_574,c_1605])).

tff(c_1609,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_570])).

tff(c_1618,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1609,c_62])).

tff(c_50,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( k7_relset_1(A_31,B_32,C_33,D_34) = k9_relat_1(C_33,D_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1708,plain,(
    ! [D_34] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_34) = k9_relat_1('#skF_4',D_34) ),
    inference(resolution,[status(thm)],[c_1618,c_50])).

tff(c_1608,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_570])).

tff(c_1731,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1609,c_1608])).

tff(c_1751,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1708,c_1731])).

tff(c_1791,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_1751])).

tff(c_1795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_1791])).

tff(c_1797,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_1894,plain,(
    ! [B_249,A_250] :
      ( r1_tarski(k1_relat_1(B_249),A_250)
      | ~ v4_relat_1(B_249,A_250)
      | ~ v1_relat_1(B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1905,plain,(
    ! [A_250] :
      ( r1_tarski(k1_xboole_0,A_250)
      | ~ v4_relat_1('#skF_4',A_250)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1797,c_1894])).

tff(c_1911,plain,(
    ! [A_251] :
      ( r1_tarski(k1_xboole_0,A_251)
      | ~ v4_relat_1('#skF_4',A_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_1905])).

tff(c_1929,plain,(
    ! [A_246] :
      ( r1_tarski(k1_xboole_0,A_246)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1892,c_1911])).

tff(c_1938,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1929])).

tff(c_1796,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_2256,plain,(
    ! [A_292] :
      ( m1_subset_1(A_292,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_292),k2_relat_1(A_292))))
      | ~ v1_funct_1(A_292)
      | ~ v1_relat_1(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2279,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4'))))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1797,c_2256])).

tff(c_2297,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_66,c_20,c_1796,c_2279])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2311,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2297,c_24])).

tff(c_2323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1938,c_2311])).

tff(c_2324,plain,(
    ! [A_246] : r1_tarski(k1_xboole_0,A_246) ),
    inference(splitRight,[status(thm)],[c_1929])).

tff(c_2325,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1929])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2345,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_2325,c_2])).

tff(c_2351,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2324,c_2345])).

tff(c_2360,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2351,c_1797])).

tff(c_127,plain,(
    ! [A_49] :
      ( k1_relat_1(A_49) = k1_xboole_0
      | k2_relat_1(A_49) != k1_xboole_0
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_134,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_127])).

tff(c_136,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_162,plain,(
    ! [A_55] :
      ( k2_relat_1(A_55) = k1_xboole_0
      | k1_relat_1(A_55) != k1_xboole_0
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_165,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_162])).

tff(c_171,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_165])).

tff(c_2362,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2351,c_2351,c_171])).

tff(c_2436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_2362])).

tff(c_2437,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_4178,plain,(
    ! [B_475,A_476] :
      ( r1_tarski(k1_relat_1(B_475),A_476)
      | ~ v4_relat_1(B_475,A_476)
      | ~ v1_relat_1(B_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4189,plain,(
    ! [A_476] :
      ( r1_tarski(k1_xboole_0,A_476)
      | ~ v4_relat_1(k1_xboole_0,A_476)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2437,c_4178])).

tff(c_4195,plain,(
    ! [A_476] :
      ( r1_tarski(k1_xboole_0,A_476)
      | ~ v4_relat_1(k1_xboole_0,A_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_4189])).

tff(c_4226,plain,(
    ! [A_483] :
      ( r1_tarski(k1_xboole_0,A_483)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4222,c_4195])).

tff(c_4233,plain,(
    ! [A_483] : r1_tarski(k1_xboole_0,A_483) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4226])).

tff(c_2492,plain,(
    ! [B_306,A_307] :
      ( v1_relat_1(B_306)
      | ~ m1_subset_1(B_306,k1_zfmisc_1(A_307))
      | ~ v1_relat_1(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2495,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_2492])).

tff(c_2501,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2495])).

tff(c_2509,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2501,c_42])).

tff(c_2515,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2509])).

tff(c_2942,plain,(
    ! [B_364,A_365] :
      ( k1_tarski(k1_funct_1(B_364,A_365)) = k2_relat_1(B_364)
      | k1_tarski(A_365) != k1_relat_1(B_364)
      | ~ v1_funct_1(B_364)
      | ~ v1_relat_1(B_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2951,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2942,c_58])).

tff(c_2957,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_66,c_2951])).

tff(c_3015,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2957])).

tff(c_2584,plain,(
    ! [C_317,A_318,B_319] :
      ( v4_relat_1(C_317,A_318)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_318,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2598,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_2584])).

tff(c_2567,plain,(
    ! [B_315,A_316] :
      ( k1_tarski(B_315) = A_316
      | k1_xboole_0 = A_316
      | ~ r1_tarski(A_316,k1_tarski(B_315)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3898,plain,(
    ! [B_457,B_458] :
      ( k1_tarski(B_457) = k1_relat_1(B_458)
      | k1_relat_1(B_458) = k1_xboole_0
      | ~ v4_relat_1(B_458,k1_tarski(B_457))
      | ~ v1_relat_1(B_458) ) ),
    inference(resolution,[status(thm)],[c_34,c_2567])).

tff(c_3941,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2598,c_3898])).

tff(c_3958,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_3941])).

tff(c_3960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2515,c_3015,c_3958])).

tff(c_3962,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2957])).

tff(c_3970,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3962,c_62])).

tff(c_4025,plain,(
    ! [A_459,B_460,C_461,D_462] :
      ( k7_relset_1(A_459,B_460,C_461,D_462) = k9_relat_1(C_461,D_462)
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k2_zfmisc_1(A_459,B_460))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4037,plain,(
    ! [D_462] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_462) = k9_relat_1('#skF_4',D_462) ),
    inference(resolution,[status(thm)],[c_3970,c_4025])).

tff(c_3961,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2957])).

tff(c_4059,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3962,c_3961])).

tff(c_4066,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4037,c_4059])).

tff(c_4078,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_4066])).

tff(c_4082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_4078])).

tff(c_4083,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2509])).

tff(c_4084,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2509])).

tff(c_4881,plain,(
    ! [A_536] :
      ( m1_subset_1(A_536,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_536),k2_relat_1(A_536))))
      | ~ v1_funct_1(A_536)
      | ~ v1_relat_1(A_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4896,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4'))))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4084,c_4881])).

tff(c_4913,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_66,c_20,c_4083,c_4896])).

tff(c_4936,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4913,c_24])).

tff(c_4949,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_4936,c_2])).

tff(c_4959,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4233,c_4949])).

tff(c_4976,plain,(
    ! [A_483] : r1_tarski('#skF_4',A_483) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4959,c_4233])).

tff(c_4088,plain,(
    ! [A_23] :
      ( r1_tarski(k9_relat_1('#skF_4',A_23),k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4083,c_38])).

tff(c_4098,plain,(
    ! [A_465] : r1_tarski(k9_relat_1('#skF_4',A_465),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_4088])).

tff(c_4101,plain,(
    ! [A_465] :
      ( k9_relat_1('#skF_4',A_465) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k9_relat_1('#skF_4',A_465)) ) ),
    inference(resolution,[status(thm)],[c_4098,c_2])).

tff(c_4236,plain,(
    ! [A_465] : k9_relat_1('#skF_4',A_465) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4233,c_4101])).

tff(c_4975,plain,(
    ! [A_465] : k9_relat_1('#skF_4',A_465) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4959,c_4236])).

tff(c_5136,plain,(
    ! [A_543,B_544,C_545,D_546] :
      ( k7_relset_1(A_543,B_544,C_545,D_546) = k9_relat_1(C_545,D_546)
      | ~ m1_subset_1(C_545,k1_zfmisc_1(k2_zfmisc_1(A_543,B_544))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5147,plain,(
    ! [D_546] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_546) = k9_relat_1('#skF_4',D_546) ),
    inference(resolution,[status(thm)],[c_62,c_5136])).

tff(c_5207,plain,(
    ! [D_546] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_546) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4975,c_5147])).

tff(c_5208,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5207,c_58])).

tff(c_5211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4976,c_5208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.88/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.15  
% 5.88/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.15  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.88/2.15  
% 5.88/2.15  %Foreground sorts:
% 5.88/2.15  
% 5.88/2.15  
% 5.88/2.15  %Background operators:
% 5.88/2.15  
% 5.88/2.15  
% 5.88/2.15  %Foreground operators:
% 5.88/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.88/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.88/2.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.88/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.88/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.88/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.88/2.15  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.88/2.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.88/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.88/2.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.88/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.88/2.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.88/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.88/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.88/2.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.88/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.88/2.15  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.88/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.88/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.88/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.88/2.15  tff('#skF_4', type, '#skF_4': $i).
% 5.88/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.88/2.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.88/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.88/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.88/2.15  
% 6.03/2.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.03/2.19  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.03/2.19  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.03/2.19  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.03/2.19  tff(f_75, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.03/2.19  tff(f_125, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 6.03/2.19  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.03/2.19  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 6.03/2.19  tff(f_85, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 6.03/2.19  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 6.03/2.19  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 6.03/2.19  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.03/2.19  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.03/2.19  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 6.03/2.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.03/2.19  tff(c_26, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.03/2.19  tff(c_20, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.03/2.19  tff(c_4102, plain, (![C_466, A_467, B_468]: (v4_relat_1(C_466, A_467) | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_467, B_468))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.03/2.19  tff(c_4216, plain, (![C_479, A_480]: (v4_relat_1(C_479, A_480) | ~m1_subset_1(C_479, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4102])).
% 6.03/2.19  tff(c_4222, plain, (![A_482, A_483]: (v4_relat_1(A_482, A_483) | ~r1_tarski(A_482, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_4216])).
% 6.03/2.19  tff(c_93, plain, (![A_40, B_41]: (v1_relat_1(k2_zfmisc_1(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.03/2.19  tff(c_95, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_93])).
% 6.03/2.19  tff(c_1872, plain, (![C_242, A_243, B_244]: (v4_relat_1(C_242, A_243) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.03/2.19  tff(c_1888, plain, (![C_245, A_246]: (v4_relat_1(C_245, A_246) | ~m1_subset_1(C_245, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1872])).
% 6.03/2.19  tff(c_1892, plain, (![A_10, A_246]: (v4_relat_1(A_10, A_246) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_1888])).
% 6.03/2.19  tff(c_36, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.03/2.19  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.03/2.19  tff(c_177, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.03/2.19  tff(c_180, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_177])).
% 6.03/2.19  tff(c_186, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_180])).
% 6.03/2.19  tff(c_38, plain, (![B_24, A_23]: (r1_tarski(k9_relat_1(B_24, A_23), k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.03/2.19  tff(c_42, plain, (![A_25]: (k2_relat_1(A_25)=k1_xboole_0 | k1_relat_1(A_25)!=k1_xboole_0 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.03/2.19  tff(c_194, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_186, c_42])).
% 6.03/2.19  tff(c_196, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_194])).
% 6.03/2.19  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.03/2.19  tff(c_550, plain, (![B_114, A_115]: (k1_tarski(k1_funct_1(B_114, A_115))=k2_relat_1(B_114) | k1_tarski(A_115)!=k1_relat_1(B_114) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.03/2.19  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.03/2.19  tff(c_562, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_550, c_58])).
% 6.03/2.19  tff(c_570, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_66, c_562])).
% 6.03/2.19  tff(c_574, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_570])).
% 6.03/2.19  tff(c_225, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.03/2.19  tff(c_239, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_225])).
% 6.03/2.19  tff(c_34, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.03/2.19  tff(c_290, plain, (![B_80, A_81]: (k1_tarski(B_80)=A_81 | k1_xboole_0=A_81 | ~r1_tarski(A_81, k1_tarski(B_80)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.03/2.19  tff(c_1500, plain, (![B_224, B_225]: (k1_tarski(B_224)=k1_relat_1(B_225) | k1_relat_1(B_225)=k1_xboole_0 | ~v4_relat_1(B_225, k1_tarski(B_224)) | ~v1_relat_1(B_225))), inference(resolution, [status(thm)], [c_34, c_290])).
% 6.03/2.19  tff(c_1571, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_239, c_1500])).
% 6.03/2.19  tff(c_1605, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_186, c_1571])).
% 6.03/2.19  tff(c_1607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_574, c_1605])).
% 6.03/2.19  tff(c_1609, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_570])).
% 6.03/2.19  tff(c_1618, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1609, c_62])).
% 6.03/2.19  tff(c_50, plain, (![A_31, B_32, C_33, D_34]: (k7_relset_1(A_31, B_32, C_33, D_34)=k9_relat_1(C_33, D_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.03/2.19  tff(c_1708, plain, (![D_34]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_34)=k9_relat_1('#skF_4', D_34))), inference(resolution, [status(thm)], [c_1618, c_50])).
% 6.03/2.19  tff(c_1608, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_570])).
% 6.03/2.19  tff(c_1731, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1609, c_1608])).
% 6.03/2.19  tff(c_1751, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1708, c_1731])).
% 6.03/2.19  tff(c_1791, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_1751])).
% 6.03/2.19  tff(c_1795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_186, c_1791])).
% 6.03/2.19  tff(c_1797, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_194])).
% 6.03/2.19  tff(c_1894, plain, (![B_249, A_250]: (r1_tarski(k1_relat_1(B_249), A_250) | ~v4_relat_1(B_249, A_250) | ~v1_relat_1(B_249))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.03/2.19  tff(c_1905, plain, (![A_250]: (r1_tarski(k1_xboole_0, A_250) | ~v4_relat_1('#skF_4', A_250) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1797, c_1894])).
% 6.03/2.19  tff(c_1911, plain, (![A_251]: (r1_tarski(k1_xboole_0, A_251) | ~v4_relat_1('#skF_4', A_251))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_1905])).
% 6.03/2.19  tff(c_1929, plain, (![A_246]: (r1_tarski(k1_xboole_0, A_246) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_1892, c_1911])).
% 6.03/2.19  tff(c_1938, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1929])).
% 6.03/2.19  tff(c_1796, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_194])).
% 6.03/2.19  tff(c_2256, plain, (![A_292]: (m1_subset_1(A_292, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_292), k2_relat_1(A_292)))) | ~v1_funct_1(A_292) | ~v1_relat_1(A_292))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.03/2.19  tff(c_2279, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1797, c_2256])).
% 6.03/2.19  tff(c_2297, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_66, c_20, c_1796, c_2279])).
% 6.03/2.19  tff(c_24, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.03/2.19  tff(c_2311, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_2297, c_24])).
% 6.03/2.19  tff(c_2323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1938, c_2311])).
% 6.03/2.19  tff(c_2324, plain, (![A_246]: (r1_tarski(k1_xboole_0, A_246))), inference(splitRight, [status(thm)], [c_1929])).
% 6.03/2.19  tff(c_2325, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1929])).
% 6.03/2.19  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.03/2.19  tff(c_2345, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_2325, c_2])).
% 6.03/2.19  tff(c_2351, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2324, c_2345])).
% 6.03/2.19  tff(c_2360, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2351, c_1797])).
% 6.03/2.19  tff(c_127, plain, (![A_49]: (k1_relat_1(A_49)=k1_xboole_0 | k2_relat_1(A_49)!=k1_xboole_0 | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.03/2.19  tff(c_134, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_127])).
% 6.03/2.19  tff(c_136, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_134])).
% 6.03/2.19  tff(c_162, plain, (![A_55]: (k2_relat_1(A_55)=k1_xboole_0 | k1_relat_1(A_55)!=k1_xboole_0 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.03/2.19  tff(c_165, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_162])).
% 6.03/2.19  tff(c_171, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_136, c_165])).
% 6.03/2.19  tff(c_2362, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2351, c_2351, c_171])).
% 6.03/2.19  tff(c_2436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2360, c_2362])).
% 6.03/2.19  tff(c_2437, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_134])).
% 6.03/2.19  tff(c_4178, plain, (![B_475, A_476]: (r1_tarski(k1_relat_1(B_475), A_476) | ~v4_relat_1(B_475, A_476) | ~v1_relat_1(B_475))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.03/2.19  tff(c_4189, plain, (![A_476]: (r1_tarski(k1_xboole_0, A_476) | ~v4_relat_1(k1_xboole_0, A_476) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2437, c_4178])).
% 6.03/2.19  tff(c_4195, plain, (![A_476]: (r1_tarski(k1_xboole_0, A_476) | ~v4_relat_1(k1_xboole_0, A_476))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_4189])).
% 6.03/2.19  tff(c_4226, plain, (![A_483]: (r1_tarski(k1_xboole_0, A_483) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_4222, c_4195])).
% 6.03/2.19  tff(c_4233, plain, (![A_483]: (r1_tarski(k1_xboole_0, A_483))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4226])).
% 6.03/2.19  tff(c_2492, plain, (![B_306, A_307]: (v1_relat_1(B_306) | ~m1_subset_1(B_306, k1_zfmisc_1(A_307)) | ~v1_relat_1(A_307))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.03/2.19  tff(c_2495, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_2492])).
% 6.03/2.19  tff(c_2501, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2495])).
% 6.03/2.19  tff(c_2509, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2501, c_42])).
% 6.03/2.19  tff(c_2515, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2509])).
% 6.03/2.19  tff(c_2942, plain, (![B_364, A_365]: (k1_tarski(k1_funct_1(B_364, A_365))=k2_relat_1(B_364) | k1_tarski(A_365)!=k1_relat_1(B_364) | ~v1_funct_1(B_364) | ~v1_relat_1(B_364))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.03/2.19  tff(c_2951, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2942, c_58])).
% 6.03/2.19  tff(c_2957, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2501, c_66, c_2951])).
% 6.03/2.19  tff(c_3015, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2957])).
% 6.03/2.19  tff(c_2584, plain, (![C_317, A_318, B_319]: (v4_relat_1(C_317, A_318) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.03/2.19  tff(c_2598, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_2584])).
% 6.03/2.19  tff(c_2567, plain, (![B_315, A_316]: (k1_tarski(B_315)=A_316 | k1_xboole_0=A_316 | ~r1_tarski(A_316, k1_tarski(B_315)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.03/2.19  tff(c_3898, plain, (![B_457, B_458]: (k1_tarski(B_457)=k1_relat_1(B_458) | k1_relat_1(B_458)=k1_xboole_0 | ~v4_relat_1(B_458, k1_tarski(B_457)) | ~v1_relat_1(B_458))), inference(resolution, [status(thm)], [c_34, c_2567])).
% 6.03/2.19  tff(c_3941, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2598, c_3898])).
% 6.03/2.19  tff(c_3958, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2501, c_3941])).
% 6.03/2.19  tff(c_3960, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2515, c_3015, c_3958])).
% 6.03/2.19  tff(c_3962, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_2957])).
% 6.03/2.19  tff(c_3970, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3962, c_62])).
% 6.03/2.19  tff(c_4025, plain, (![A_459, B_460, C_461, D_462]: (k7_relset_1(A_459, B_460, C_461, D_462)=k9_relat_1(C_461, D_462) | ~m1_subset_1(C_461, k1_zfmisc_1(k2_zfmisc_1(A_459, B_460))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.03/2.19  tff(c_4037, plain, (![D_462]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_462)=k9_relat_1('#skF_4', D_462))), inference(resolution, [status(thm)], [c_3970, c_4025])).
% 6.03/2.19  tff(c_3961, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2957])).
% 6.03/2.19  tff(c_4059, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3962, c_3961])).
% 6.03/2.19  tff(c_4066, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4037, c_4059])).
% 6.03/2.19  tff(c_4078, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_4066])).
% 6.03/2.19  tff(c_4082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2501, c_4078])).
% 6.03/2.19  tff(c_4083, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2509])).
% 6.03/2.19  tff(c_4084, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2509])).
% 6.03/2.19  tff(c_4881, plain, (![A_536]: (m1_subset_1(A_536, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_536), k2_relat_1(A_536)))) | ~v1_funct_1(A_536) | ~v1_relat_1(A_536))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.03/2.19  tff(c_4896, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4084, c_4881])).
% 6.03/2.19  tff(c_4913, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2501, c_66, c_20, c_4083, c_4896])).
% 6.03/2.19  tff(c_4936, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_4913, c_24])).
% 6.03/2.19  tff(c_4949, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_4936, c_2])).
% 6.03/2.19  tff(c_4959, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4233, c_4949])).
% 6.03/2.19  tff(c_4976, plain, (![A_483]: (r1_tarski('#skF_4', A_483))), inference(demodulation, [status(thm), theory('equality')], [c_4959, c_4233])).
% 6.03/2.19  tff(c_4088, plain, (![A_23]: (r1_tarski(k9_relat_1('#skF_4', A_23), k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4083, c_38])).
% 6.03/2.19  tff(c_4098, plain, (![A_465]: (r1_tarski(k9_relat_1('#skF_4', A_465), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2501, c_4088])).
% 6.03/2.19  tff(c_4101, plain, (![A_465]: (k9_relat_1('#skF_4', A_465)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k9_relat_1('#skF_4', A_465)))), inference(resolution, [status(thm)], [c_4098, c_2])).
% 6.03/2.19  tff(c_4236, plain, (![A_465]: (k9_relat_1('#skF_4', A_465)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4233, c_4101])).
% 6.03/2.19  tff(c_4975, plain, (![A_465]: (k9_relat_1('#skF_4', A_465)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4959, c_4236])).
% 6.03/2.19  tff(c_5136, plain, (![A_543, B_544, C_545, D_546]: (k7_relset_1(A_543, B_544, C_545, D_546)=k9_relat_1(C_545, D_546) | ~m1_subset_1(C_545, k1_zfmisc_1(k2_zfmisc_1(A_543, B_544))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.03/2.19  tff(c_5147, plain, (![D_546]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_546)=k9_relat_1('#skF_4', D_546))), inference(resolution, [status(thm)], [c_62, c_5136])).
% 6.03/2.19  tff(c_5207, plain, (![D_546]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_546)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4975, c_5147])).
% 6.03/2.19  tff(c_5208, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5207, c_58])).
% 6.03/2.19  tff(c_5211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4976, c_5208])).
% 6.03/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.03/2.19  
% 6.03/2.19  Inference rules
% 6.03/2.19  ----------------------
% 6.03/2.19  #Ref     : 0
% 6.03/2.19  #Sup     : 1056
% 6.03/2.19  #Fact    : 0
% 6.03/2.19  #Define  : 0
% 6.03/2.19  #Split   : 31
% 6.03/2.19  #Chain   : 0
% 6.03/2.20  #Close   : 0
% 6.03/2.20  
% 6.03/2.20  Ordering : KBO
% 6.03/2.20  
% 6.03/2.20  Simplification rules
% 6.03/2.20  ----------------------
% 6.03/2.20  #Subsume      : 286
% 6.03/2.20  #Demod        : 992
% 6.03/2.20  #Tautology    : 415
% 6.03/2.20  #SimpNegUnit  : 86
% 6.03/2.20  #BackRed      : 137
% 6.03/2.20  
% 6.03/2.20  #Partial instantiations: 0
% 6.03/2.20  #Strategies tried      : 1
% 6.03/2.20  
% 6.03/2.20  Timing (in seconds)
% 6.03/2.20  ----------------------
% 6.03/2.20  Preprocessing        : 0.34
% 6.03/2.20  Parsing              : 0.18
% 6.03/2.20  CNF conversion       : 0.02
% 6.03/2.20  Main loop            : 1.01
% 6.03/2.20  Inferencing          : 0.34
% 6.03/2.20  Reduction            : 0.35
% 6.03/2.20  Demodulation         : 0.24
% 6.03/2.20  BG Simplification    : 0.04
% 6.03/2.20  Subsumption          : 0.20
% 6.03/2.20  Abstraction          : 0.04
% 6.03/2.20  MUC search           : 0.00
% 6.03/2.20  Cooper               : 0.00
% 6.03/2.20  Total                : 1.42
% 6.03/2.20  Index Insertion      : 0.00
% 6.03/2.20  Index Deletion       : 0.00
% 6.03/2.20  Index Matching       : 0.00
% 6.03/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
