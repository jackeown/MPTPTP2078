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
% DateTime   : Thu Dec  3 10:14:44 EST 2020

% Result     : Theorem 4.65s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 251 expanded)
%              Number of leaves         :   40 ( 104 expanded)
%              Depth                    :   13
%              Number of atoms          :  109 ( 531 expanded)
%              Number of equality atoms :   33 ( 133 expanded)
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

tff(f_111,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

tff(f_99,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_127,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_140,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_127])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1756,plain,(
    ! [B_212,A_213] :
      ( k1_tarski(k1_funct_1(B_212,A_213)) = k2_relat_1(B_212)
      | k1_tarski(A_213) != k1_relat_1(B_212)
      | ~ v1_funct_1(B_212)
      | ~ v1_relat_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1705,plain,(
    ! [A_205,B_206,C_207,D_208] :
      ( k7_relset_1(A_205,B_206,C_207,D_208) = k9_relat_1(C_207,D_208)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1719,plain,(
    ! [D_208] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_208) = k9_relat_1('#skF_4',D_208) ),
    inference(resolution,[status(thm)],[c_60,c_1705])).

tff(c_56,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1746,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1719,c_56])).

tff(c_1762,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1756,c_1746])).

tff(c_1771,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_64,c_1762])).

tff(c_1814,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1771])).

tff(c_306,plain,(
    ! [C_76,A_77,B_78] :
      ( v4_relat_1(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_321,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_306])).

tff(c_254,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(k1_relat_1(B_68),A_69)
      | ~ v4_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2530,plain,(
    ! [B_289,B_290] :
      ( k1_tarski(B_289) = k1_relat_1(B_290)
      | k1_relat_1(B_290) = k1_xboole_0
      | ~ v4_relat_1(B_290,k1_tarski(B_289))
      | ~ v1_relat_1(B_290) ) ),
    inference(resolution,[status(thm)],[c_254,c_16])).

tff(c_2564,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_321,c_2530])).

tff(c_2582,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_2564])).

tff(c_2583,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1814,c_2582])).

tff(c_1655,plain,(
    ! [A_201] :
      ( m1_subset_1(A_201,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_201),k2_relat_1(A_201))))
      | ~ v1_funct_1(A_201)
      | ~ v1_relat_1(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1674,plain,(
    ! [A_201] :
      ( r1_tarski(A_201,k2_zfmisc_1(k1_relat_1(A_201),k2_relat_1(A_201)))
      | ~ v1_funct_1(A_201)
      | ~ v1_relat_1(A_201) ) ),
    inference(resolution,[status(thm)],[c_1655,c_28])).

tff(c_2621,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2583,c_1674])).

tff(c_2664,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_64,c_26,c_2621])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_204,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_219,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_204])).

tff(c_2700,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2664,c_219])).

tff(c_2753,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2700,c_8])).

tff(c_38,plain,(
    ! [A_20] : k9_relat_1(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2750,plain,(
    ! [A_20] : k9_relat_1('#skF_4',A_20) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2700,c_2700,c_38])).

tff(c_3088,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2750,c_1746])).

tff(c_3092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2753,c_3088])).

tff(c_3093,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1771])).

tff(c_3137,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_3093])).

tff(c_3141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_3137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.65/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.82  
% 4.65/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.82  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.73/1.82  
% 4.73/1.82  %Foreground sorts:
% 4.73/1.82  
% 4.73/1.82  
% 4.73/1.82  %Background operators:
% 4.73/1.82  
% 4.73/1.82  
% 4.73/1.82  %Foreground operators:
% 4.73/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.73/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.73/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.73/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.73/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.73/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.73/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.73/1.82  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.73/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.73/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.73/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.73/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.73/1.82  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.73/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.73/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.73/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.73/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.73/1.82  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.73/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.73/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.73/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.73/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.73/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.73/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.73/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.73/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.73/1.82  
% 4.73/1.84  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 4.73/1.84  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.73/1.84  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 4.73/1.84  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.73/1.84  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 4.73/1.84  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.73/1.84  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.73/1.84  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.73/1.84  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.73/1.84  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.73/1.84  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.73/1.84  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.73/1.84  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.73/1.84  tff(f_67, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 4.73/1.84  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.73/1.84  tff(c_127, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.73/1.84  tff(c_140, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_127])).
% 4.73/1.84  tff(c_36, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.73/1.84  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.73/1.84  tff(c_26, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.73/1.84  tff(c_1756, plain, (![B_212, A_213]: (k1_tarski(k1_funct_1(B_212, A_213))=k2_relat_1(B_212) | k1_tarski(A_213)!=k1_relat_1(B_212) | ~v1_funct_1(B_212) | ~v1_relat_1(B_212))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.73/1.84  tff(c_1705, plain, (![A_205, B_206, C_207, D_208]: (k7_relset_1(A_205, B_206, C_207, D_208)=k9_relat_1(C_207, D_208) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.73/1.84  tff(c_1719, plain, (![D_208]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_208)=k9_relat_1('#skF_4', D_208))), inference(resolution, [status(thm)], [c_60, c_1705])).
% 4.73/1.84  tff(c_56, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.73/1.84  tff(c_1746, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1719, c_56])).
% 4.73/1.84  tff(c_1762, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1756, c_1746])).
% 4.73/1.84  tff(c_1771, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_64, c_1762])).
% 4.73/1.84  tff(c_1814, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1771])).
% 4.73/1.84  tff(c_306, plain, (![C_76, A_77, B_78]: (v4_relat_1(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.73/1.84  tff(c_321, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_306])).
% 4.73/1.84  tff(c_254, plain, (![B_68, A_69]: (r1_tarski(k1_relat_1(B_68), A_69) | ~v4_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.73/1.84  tff(c_16, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.73/1.84  tff(c_2530, plain, (![B_289, B_290]: (k1_tarski(B_289)=k1_relat_1(B_290) | k1_relat_1(B_290)=k1_xboole_0 | ~v4_relat_1(B_290, k1_tarski(B_289)) | ~v1_relat_1(B_290))), inference(resolution, [status(thm)], [c_254, c_16])).
% 4.73/1.84  tff(c_2564, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_321, c_2530])).
% 4.73/1.84  tff(c_2582, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_2564])).
% 4.73/1.84  tff(c_2583, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1814, c_2582])).
% 4.73/1.84  tff(c_1655, plain, (![A_201]: (m1_subset_1(A_201, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_201), k2_relat_1(A_201)))) | ~v1_funct_1(A_201) | ~v1_relat_1(A_201))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.73/1.84  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.73/1.84  tff(c_1674, plain, (![A_201]: (r1_tarski(A_201, k2_zfmisc_1(k1_relat_1(A_201), k2_relat_1(A_201))) | ~v1_funct_1(A_201) | ~v1_relat_1(A_201))), inference(resolution, [status(thm)], [c_1655, c_28])).
% 4.73/1.84  tff(c_2621, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2583, c_1674])).
% 4.73/1.84  tff(c_2664, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_64, c_26, c_2621])).
% 4.73/1.84  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.73/1.84  tff(c_204, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.73/1.84  tff(c_219, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_204])).
% 4.73/1.84  tff(c_2700, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2664, c_219])).
% 4.73/1.84  tff(c_2753, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2700, c_8])).
% 4.73/1.84  tff(c_38, plain, (![A_20]: (k9_relat_1(k1_xboole_0, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.73/1.84  tff(c_2750, plain, (![A_20]: (k9_relat_1('#skF_4', A_20)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2700, c_2700, c_38])).
% 4.73/1.84  tff(c_3088, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2750, c_1746])).
% 4.73/1.84  tff(c_3092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2753, c_3088])).
% 4.73/1.84  tff(c_3093, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1771])).
% 4.73/1.84  tff(c_3137, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_3093])).
% 4.73/1.84  tff(c_3141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_3137])).
% 4.73/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.84  
% 4.73/1.84  Inference rules
% 4.73/1.84  ----------------------
% 4.73/1.84  #Ref     : 0
% 4.73/1.84  #Sup     : 658
% 4.73/1.84  #Fact    : 0
% 4.73/1.84  #Define  : 0
% 4.73/1.84  #Split   : 4
% 4.73/1.84  #Chain   : 0
% 4.73/1.84  #Close   : 0
% 4.73/1.84  
% 4.73/1.84  Ordering : KBO
% 4.73/1.84  
% 4.73/1.84  Simplification rules
% 4.73/1.84  ----------------------
% 4.73/1.84  #Subsume      : 78
% 4.73/1.84  #Demod        : 938
% 4.73/1.84  #Tautology    : 375
% 4.73/1.84  #SimpNegUnit  : 2
% 4.73/1.84  #BackRed      : 101
% 4.73/1.84  
% 4.73/1.84  #Partial instantiations: 0
% 4.73/1.84  #Strategies tried      : 1
% 4.73/1.84  
% 4.73/1.84  Timing (in seconds)
% 4.73/1.84  ----------------------
% 4.73/1.84  Preprocessing        : 0.33
% 4.73/1.84  Parsing              : 0.18
% 4.73/1.84  CNF conversion       : 0.02
% 4.73/1.84  Main loop            : 0.74
% 4.73/1.84  Inferencing          : 0.24
% 4.73/1.84  Reduction            : 0.27
% 4.73/1.84  Demodulation         : 0.20
% 4.73/1.84  BG Simplification    : 0.03
% 4.73/1.84  Subsumption          : 0.14
% 4.73/1.84  Abstraction          : 0.03
% 4.73/1.84  MUC search           : 0.00
% 4.73/1.84  Cooper               : 0.00
% 4.73/1.84  Total                : 1.10
% 4.73/1.84  Index Insertion      : 0.00
% 4.73/1.84  Index Deletion       : 0.00
% 4.73/1.84  Index Matching       : 0.00
% 4.73/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
