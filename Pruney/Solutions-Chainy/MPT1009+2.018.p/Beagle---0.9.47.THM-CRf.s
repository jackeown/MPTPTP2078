%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:44 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 176 expanded)
%              Number of leaves         :   40 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 326 expanded)
%              Number of equality atoms :   33 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_136,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_149,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_136])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    ! [B_22,A_21] :
      ( k1_tarski(k1_funct_1(B_22,A_21)) = k2_relat_1(B_22)
      | k1_tarski(A_21) != k1_relat_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_395,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k7_relset_1(A_99,B_100,C_101,D_102) = k9_relat_1(C_101,D_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_406,plain,(
    ! [D_102] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_102) = k9_relat_1('#skF_4',D_102) ),
    inference(resolution,[status(thm)],[c_56,c_395])).

tff(c_52,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_500,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_52])).

tff(c_512,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_500])).

tff(c_514,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_60,c_512])).

tff(c_556,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_514])).

tff(c_246,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_261,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_246])).

tff(c_325,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(k1_relat_1(B_91),A_92)
      | ~ v4_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1428,plain,(
    ! [B_222,B_223] :
      ( k1_tarski(B_222) = k1_relat_1(B_223)
      | k1_relat_1(B_223) = k1_xboole_0
      | ~ v4_relat_1(B_223,k1_tarski(B_222))
      | ~ v1_relat_1(B_223) ) ),
    inference(resolution,[status(thm)],[c_325,c_16])).

tff(c_1462,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_261,c_1428])).

tff(c_1480,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1462])).

tff(c_1481,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_556,c_1480])).

tff(c_26,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_557,plain,(
    ! [D_119,B_120,C_121,A_122] :
      ( m1_subset_1(D_119,k1_zfmisc_1(k2_zfmisc_1(B_120,C_121)))
      | ~ r1_tarski(k1_relat_1(D_119),B_120)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(k2_zfmisc_1(A_122,C_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_570,plain,(
    ! [B_123] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_123,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_123) ) ),
    inference(resolution,[status(thm)],[c_56,c_557])).

tff(c_590,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_570])).

tff(c_612,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_1491,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1481,c_612])).

tff(c_1502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1491])).

tff(c_1503,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1519,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1503,c_28])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(B_49,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_123])).

tff(c_1569,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1519,c_135])).

tff(c_1595,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1569,c_8])).

tff(c_38,plain,(
    ! [A_20] : k9_relat_1(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1592,plain,(
    ! [A_20] : k9_relat_1('#skF_4',A_20) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1569,c_1569,c_38])).

tff(c_1714,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_500])).

tff(c_1718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1595,c_1714])).

tff(c_1719,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_514])).

tff(c_1737,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1719])).

tff(c_1741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:17:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.57  
% 3.56/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.58  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.56/1.58  
% 3.56/1.58  %Foreground sorts:
% 3.56/1.58  
% 3.56/1.58  
% 3.56/1.58  %Background operators:
% 3.56/1.58  
% 3.56/1.58  
% 3.56/1.58  %Foreground operators:
% 3.56/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.56/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.56/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.56/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.56/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.56/1.58  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.56/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.56/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.56/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.56/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.56/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.56/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.58  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.56/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.56/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.56/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.56/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.56/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.58  
% 3.56/1.59  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.56/1.59  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.56/1.59  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.56/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.56/1.59  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.56/1.59  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.56/1.59  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.56/1.59  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.56/1.59  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.56/1.59  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.56/1.59  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 3.56/1.59  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.56/1.59  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.56/1.59  tff(f_67, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 3.56/1.59  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.56/1.59  tff(c_136, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.56/1.59  tff(c_149, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_136])).
% 3.56/1.59  tff(c_36, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.56/1.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.59  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.56/1.59  tff(c_40, plain, (![B_22, A_21]: (k1_tarski(k1_funct_1(B_22, A_21))=k2_relat_1(B_22) | k1_tarski(A_21)!=k1_relat_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.56/1.59  tff(c_395, plain, (![A_99, B_100, C_101, D_102]: (k7_relset_1(A_99, B_100, C_101, D_102)=k9_relat_1(C_101, D_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.56/1.59  tff(c_406, plain, (![D_102]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_102)=k9_relat_1('#skF_4', D_102))), inference(resolution, [status(thm)], [c_56, c_395])).
% 3.56/1.59  tff(c_52, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.56/1.59  tff(c_500, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_52])).
% 3.56/1.59  tff(c_512, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_500])).
% 3.56/1.59  tff(c_514, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_60, c_512])).
% 3.56/1.59  tff(c_556, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_514])).
% 3.56/1.59  tff(c_246, plain, (![C_72, A_73, B_74]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.56/1.59  tff(c_261, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_246])).
% 3.56/1.59  tff(c_325, plain, (![B_91, A_92]: (r1_tarski(k1_relat_1(B_91), A_92) | ~v4_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.56/1.59  tff(c_16, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.56/1.59  tff(c_1428, plain, (![B_222, B_223]: (k1_tarski(B_222)=k1_relat_1(B_223) | k1_relat_1(B_223)=k1_xboole_0 | ~v4_relat_1(B_223, k1_tarski(B_222)) | ~v1_relat_1(B_223))), inference(resolution, [status(thm)], [c_325, c_16])).
% 3.56/1.59  tff(c_1462, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_261, c_1428])).
% 3.56/1.59  tff(c_1480, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_149, c_1462])).
% 3.56/1.59  tff(c_1481, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_556, c_1480])).
% 3.56/1.59  tff(c_26, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.59  tff(c_557, plain, (![D_119, B_120, C_121, A_122]: (m1_subset_1(D_119, k1_zfmisc_1(k2_zfmisc_1(B_120, C_121))) | ~r1_tarski(k1_relat_1(D_119), B_120) | ~m1_subset_1(D_119, k1_zfmisc_1(k2_zfmisc_1(A_122, C_121))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.56/1.59  tff(c_570, plain, (![B_123]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_123, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_123))), inference(resolution, [status(thm)], [c_56, c_557])).
% 3.56/1.59  tff(c_590, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_570])).
% 3.56/1.59  tff(c_612, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_590])).
% 3.56/1.59  tff(c_1491, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1481, c_612])).
% 3.56/1.59  tff(c_1502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1491])).
% 3.56/1.59  tff(c_1503, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_590])).
% 3.56/1.59  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.56/1.59  tff(c_1519, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_1503, c_28])).
% 3.56/1.59  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.56/1.59  tff(c_123, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(B_49, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.59  tff(c_135, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_123])).
% 3.56/1.59  tff(c_1569, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1519, c_135])).
% 3.56/1.59  tff(c_1595, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1569, c_8])).
% 3.56/1.59  tff(c_38, plain, (![A_20]: (k9_relat_1(k1_xboole_0, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.56/1.59  tff(c_1592, plain, (![A_20]: (k9_relat_1('#skF_4', A_20)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1569, c_1569, c_38])).
% 3.56/1.59  tff(c_1714, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_500])).
% 3.56/1.59  tff(c_1718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1595, c_1714])).
% 3.56/1.59  tff(c_1719, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_514])).
% 3.56/1.59  tff(c_1737, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1719])).
% 3.56/1.59  tff(c_1741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_1737])).
% 3.56/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.59  
% 3.56/1.59  Inference rules
% 3.56/1.59  ----------------------
% 3.56/1.59  #Ref     : 0
% 3.56/1.59  #Sup     : 338
% 3.56/1.59  #Fact    : 0
% 3.56/1.59  #Define  : 0
% 3.56/1.59  #Split   : 5
% 3.56/1.59  #Chain   : 0
% 3.56/1.59  #Close   : 0
% 3.56/1.59  
% 3.56/1.59  Ordering : KBO
% 3.56/1.59  
% 3.56/1.59  Simplification rules
% 3.56/1.59  ----------------------
% 3.56/1.59  #Subsume      : 31
% 3.56/1.59  #Demod        : 439
% 3.56/1.59  #Tautology    : 185
% 3.56/1.59  #SimpNegUnit  : 5
% 3.56/1.59  #BackRed      : 63
% 3.56/1.59  
% 3.56/1.59  #Partial instantiations: 0
% 3.56/1.59  #Strategies tried      : 1
% 3.56/1.59  
% 3.56/1.59  Timing (in seconds)
% 3.56/1.59  ----------------------
% 3.56/1.59  Preprocessing        : 0.33
% 3.56/1.59  Parsing              : 0.18
% 3.56/1.59  CNF conversion       : 0.02
% 3.56/1.59  Main loop            : 0.53
% 3.56/1.59  Inferencing          : 0.19
% 3.56/1.59  Reduction            : 0.18
% 3.56/1.59  Demodulation         : 0.13
% 3.56/1.59  BG Simplification    : 0.02
% 3.56/1.59  Subsumption          : 0.09
% 3.56/1.59  Abstraction          : 0.02
% 3.56/1.59  MUC search           : 0.00
% 3.56/1.59  Cooper               : 0.00
% 3.56/1.60  Total                : 0.88
% 3.56/1.60  Index Insertion      : 0.00
% 3.56/1.60  Index Deletion       : 0.00
% 3.56/1.60  Index Matching       : 0.00
% 3.56/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
