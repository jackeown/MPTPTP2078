%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:45 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 309 expanded)
%              Number of leaves         :   40 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          :  115 ( 678 expanded)
%              Number of equality atoms :   33 ( 167 expanded)
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

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_127,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_140,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_127])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_561,plain,(
    ! [B_121,A_122] :
      ( k1_tarski(k1_funct_1(B_121,A_122)) = k2_relat_1(B_121)
      | k1_tarski(A_122) != k1_relat_1(B_121)
      | ~ v1_funct_1(B_121)
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_463,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k7_relset_1(A_105,B_106,C_107,D_108) = k9_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_474,plain,(
    ! [D_108] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_108) = k9_relat_1('#skF_4',D_108) ),
    inference(resolution,[status(thm)],[c_60,c_463])).

tff(c_56,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_504,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_56])).

tff(c_567,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_504])).

tff(c_576,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_64,c_567])).

tff(c_578,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_306,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_321,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_306])).

tff(c_254,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(k1_relat_1(B_69),A_70)
      | ~ v4_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1871,plain,(
    ! [B_251,B_252] :
      ( k1_tarski(B_251) = k1_relat_1(B_252)
      | k1_relat_1(B_252) = k1_xboole_0
      | ~ v4_relat_1(B_252,k1_tarski(B_251))
      | ~ v1_relat_1(B_252) ) ),
    inference(resolution,[status(thm)],[c_254,c_16])).

tff(c_1905,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_321,c_1871])).

tff(c_1923,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1905])).

tff(c_1924,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_578,c_1923])).

tff(c_50,plain,(
    ! [B_34,A_33] :
      ( m1_subset_1(B_34,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_34),A_33)))
      | ~ r1_tarski(k2_relat_1(B_34),A_33)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1953,plain,(
    ! [A_33] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A_33)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_33)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1924,c_50])).

tff(c_1991,plain,(
    ! [A_33] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_64,c_26,c_1953])).

tff(c_2054,plain,(
    ! [A_255] : ~ r1_tarski(k2_relat_1('#skF_4'),A_255) ),
    inference(splitLeft,[status(thm)],[c_1991])).

tff(c_2059,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_2054])).

tff(c_2060,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1991])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2082,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2060,c_28])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_204,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_219,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_204])).

tff(c_2111,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2082,c_219])).

tff(c_2162,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2111,c_8])).

tff(c_38,plain,(
    ! [A_20] : k9_relat_1(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2159,plain,(
    ! [A_20] : k9_relat_1('#skF_4',A_20) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2111,c_2111,c_38])).

tff(c_2251,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2159,c_504])).

tff(c_2255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2162,c_2251])).

tff(c_2256,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_2274,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2256])).

tff(c_2278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_2274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:19:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.64  
% 3.91/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.91/1.65  
% 3.91/1.65  %Foreground sorts:
% 3.91/1.65  
% 3.91/1.65  
% 3.91/1.65  %Background operators:
% 3.91/1.65  
% 3.91/1.65  
% 3.91/1.65  %Foreground operators:
% 3.91/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.91/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.91/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.91/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.91/1.65  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.91/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.91/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.91/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.91/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.91/1.65  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.91/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.91/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.91/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.91/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.91/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.91/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.91/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.91/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.65  
% 3.91/1.66  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.91/1.66  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.91/1.66  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.91/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.91/1.66  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.91/1.66  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.91/1.66  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.91/1.66  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.91/1.66  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.91/1.66  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.91/1.66  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.91/1.66  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.91/1.66  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.91/1.66  tff(f_67, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 3.91/1.66  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.91/1.66  tff(c_127, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.91/1.66  tff(c_140, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_127])).
% 3.91/1.66  tff(c_36, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.91/1.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.66  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.91/1.66  tff(c_26, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.91/1.66  tff(c_561, plain, (![B_121, A_122]: (k1_tarski(k1_funct_1(B_121, A_122))=k2_relat_1(B_121) | k1_tarski(A_122)!=k1_relat_1(B_121) | ~v1_funct_1(B_121) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.91/1.66  tff(c_463, plain, (![A_105, B_106, C_107, D_108]: (k7_relset_1(A_105, B_106, C_107, D_108)=k9_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.91/1.66  tff(c_474, plain, (![D_108]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_108)=k9_relat_1('#skF_4', D_108))), inference(resolution, [status(thm)], [c_60, c_463])).
% 3.91/1.66  tff(c_56, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.91/1.66  tff(c_504, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_56])).
% 3.91/1.66  tff(c_567, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_561, c_504])).
% 3.91/1.66  tff(c_576, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_64, c_567])).
% 3.91/1.66  tff(c_578, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_576])).
% 3.91/1.66  tff(c_306, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.91/1.66  tff(c_321, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_306])).
% 3.91/1.66  tff(c_254, plain, (![B_69, A_70]: (r1_tarski(k1_relat_1(B_69), A_70) | ~v4_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.91/1.66  tff(c_16, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.91/1.66  tff(c_1871, plain, (![B_251, B_252]: (k1_tarski(B_251)=k1_relat_1(B_252) | k1_relat_1(B_252)=k1_xboole_0 | ~v4_relat_1(B_252, k1_tarski(B_251)) | ~v1_relat_1(B_252))), inference(resolution, [status(thm)], [c_254, c_16])).
% 3.91/1.66  tff(c_1905, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_321, c_1871])).
% 3.91/1.66  tff(c_1923, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1905])).
% 3.91/1.66  tff(c_1924, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_578, c_1923])).
% 3.91/1.66  tff(c_50, plain, (![B_34, A_33]: (m1_subset_1(B_34, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_34), A_33))) | ~r1_tarski(k2_relat_1(B_34), A_33) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.91/1.66  tff(c_1953, plain, (![A_33]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A_33))) | ~r1_tarski(k2_relat_1('#skF_4'), A_33) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1924, c_50])).
% 3.91/1.66  tff(c_1991, plain, (![A_33]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_4'), A_33))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_64, c_26, c_1953])).
% 3.91/1.66  tff(c_2054, plain, (![A_255]: (~r1_tarski(k2_relat_1('#skF_4'), A_255))), inference(splitLeft, [status(thm)], [c_1991])).
% 3.91/1.66  tff(c_2059, plain, $false, inference(resolution, [status(thm)], [c_6, c_2054])).
% 3.91/1.66  tff(c_2060, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1991])).
% 3.91/1.66  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.91/1.66  tff(c_2082, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_2060, c_28])).
% 3.91/1.66  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.91/1.66  tff(c_204, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.66  tff(c_219, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_204])).
% 3.91/1.66  tff(c_2111, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2082, c_219])).
% 3.91/1.66  tff(c_2162, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2111, c_8])).
% 3.91/1.66  tff(c_38, plain, (![A_20]: (k9_relat_1(k1_xboole_0, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.91/1.66  tff(c_2159, plain, (![A_20]: (k9_relat_1('#skF_4', A_20)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2111, c_2111, c_38])).
% 3.91/1.66  tff(c_2251, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2159, c_504])).
% 3.91/1.66  tff(c_2255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2162, c_2251])).
% 3.91/1.66  tff(c_2256, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_576])).
% 3.91/1.66  tff(c_2274, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_2256])).
% 3.91/1.66  tff(c_2278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_2274])).
% 3.91/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.66  
% 3.91/1.66  Inference rules
% 3.91/1.66  ----------------------
% 3.91/1.66  #Ref     : 0
% 3.91/1.66  #Sup     : 440
% 3.91/1.66  #Fact    : 0
% 3.91/1.66  #Define  : 0
% 3.91/1.66  #Split   : 6
% 3.91/1.66  #Chain   : 0
% 3.91/1.66  #Close   : 0
% 3.91/1.66  
% 3.91/1.66  Ordering : KBO
% 3.91/1.66  
% 3.91/1.66  Simplification rules
% 3.91/1.66  ----------------------
% 3.91/1.66  #Subsume      : 43
% 3.91/1.66  #Demod        : 679
% 3.91/1.66  #Tautology    : 248
% 3.91/1.66  #SimpNegUnit  : 2
% 3.91/1.66  #BackRed      : 97
% 3.91/1.66  
% 3.91/1.66  #Partial instantiations: 0
% 3.91/1.66  #Strategies tried      : 1
% 3.91/1.66  
% 3.91/1.66  Timing (in seconds)
% 3.91/1.66  ----------------------
% 3.91/1.66  Preprocessing        : 0.32
% 3.91/1.66  Parsing              : 0.17
% 3.91/1.66  CNF conversion       : 0.02
% 3.91/1.66  Main loop            : 0.58
% 3.91/1.66  Inferencing          : 0.19
% 3.91/1.66  Reduction            : 0.21
% 3.91/1.66  Demodulation         : 0.15
% 3.91/1.66  BG Simplification    : 0.02
% 3.91/1.66  Subsumption          : 0.11
% 3.91/1.66  Abstraction          : 0.02
% 3.91/1.66  MUC search           : 0.00
% 3.91/1.66  Cooper               : 0.00
% 3.91/1.67  Total                : 0.94
% 3.91/1.67  Index Insertion      : 0.00
% 3.91/1.67  Index Deletion       : 0.00
% 3.91/1.67  Index Matching       : 0.00
% 3.91/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
