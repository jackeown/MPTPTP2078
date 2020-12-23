%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:45 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 204 expanded)
%              Number of leaves         :   31 (  81 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 448 expanded)
%              Number of equality atoms :   30 ( 101 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_91,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
      & v1_relat_1(B)
      & v4_relat_1(B,A)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v1_funct_2(B,A,A)
      & v3_funct_2(B,A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_176,plain,(
    ! [C_41,B_42,A_43] :
      ( v1_xboole_0(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(B_42,A_43)))
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_195,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_176])).

tff(c_240,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_56,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48])).

tff(c_50,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_649,plain,(
    ! [B_77,C_78,A_79] :
      ( k1_xboole_0 = B_77
      | v1_funct_2(C_78,A_79,B_77)
      | k1_relset_1(A_79,B_77,C_78) != A_79
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_662,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_52,c_649])).

tff(c_675,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_662])).

tff(c_676,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_675])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_146,plain,(
    ! [B_38,A_39] :
      ( ~ r1_xboole_0(B_38,A_39)
      | ~ r1_tarski(B_38,A_39)
      | v1_xboole_0(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_166,plain,(
    ! [A_40] :
      ( ~ r1_tarski(A_40,k1_xboole_0)
      | v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_175,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_166])).

tff(c_707,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_175])).

tff(c_717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_707])).

tff(c_718,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_723,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_718,c_2])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    ! [A_32] : m1_subset_1('#skF_1'(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_108,plain,(
    m1_subset_1('#skF_1'(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_101])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_117,plain,(
    r1_tarski('#skF_1'(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_108,c_16])).

tff(c_174,plain,(
    v1_xboole_0('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_117,c_166])).

tff(c_204,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_36,plain,(
    ! [A_17] : v1_funct_2('#skF_1'(A_17),A_17,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_220,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_36])).

tff(c_890,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_723,c_723,c_220])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_14] :
      ( v1_funct_2(k1_xboole_0,A_14,k1_xboole_0)
      | k1_xboole_0 = A_14
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_14,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_60,plain,(
    ! [A_14] :
      ( v1_funct_2(k1_xboole_0,A_14,k1_xboole_0)
      | k1_xboole_0 = A_14
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22])).

tff(c_151,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_154,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_151])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_154])).

tff(c_159,plain,(
    ! [A_14] :
      ( v1_funct_2(k1_xboole_0,A_14,k1_xboole_0)
      | k1_xboole_0 = A_14 ) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_965,plain,(
    ! [A_97] :
      ( v1_funct_2('#skF_4',A_97,'#skF_4')
      | A_97 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_723,c_723,c_159])).

tff(c_719,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_727,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_719,c_2])).

tff(c_749,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_727])).

tff(c_753,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_56])).

tff(c_974,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_965,c_753])).

tff(c_1002,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_753])).

tff(c_1006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_1002])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.45  
% 2.96/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.45  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.29/1.45  
% 3.29/1.45  %Foreground sorts:
% 3.29/1.45  
% 3.29/1.45  
% 3.29/1.45  %Background operators:
% 3.29/1.45  
% 3.29/1.45  
% 3.29/1.45  %Foreground operators:
% 3.29/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.29/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.29/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.29/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.29/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.29/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.29/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.29/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.29/1.45  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.29/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.29/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.45  
% 3.29/1.46  tff(f_104, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 3.29/1.46  tff(f_58, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.29/1.46  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.29/1.46  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.29/1.46  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.29/1.46  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.29/1.46  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.29/1.46  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.29/1.46  tff(f_91, axiom, (![A]: (?[B]: ((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_funct_1(B)) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_funct_2)).
% 3.29/1.46  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.29/1.46  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.29/1.46  tff(c_176, plain, (![C_41, B_42, A_43]: (v1_xboole_0(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(B_42, A_43))) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.29/1.46  tff(c_195, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_176])).
% 3.29/1.46  tff(c_240, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_195])).
% 3.29/1.46  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.29/1.46  tff(c_48, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.29/1.46  tff(c_56, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48])).
% 3.29/1.46  tff(c_50, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.29/1.46  tff(c_649, plain, (![B_77, C_78, A_79]: (k1_xboole_0=B_77 | v1_funct_2(C_78, A_79, B_77) | k1_relset_1(A_79, B_77, C_78)!=A_79 | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_77))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.29/1.46  tff(c_662, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_52, c_649])).
% 3.29/1.46  tff(c_675, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_662])).
% 3.29/1.46  tff(c_676, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_56, c_675])).
% 3.29/1.46  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.46  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/1.46  tff(c_146, plain, (![B_38, A_39]: (~r1_xboole_0(B_38, A_39) | ~r1_tarski(B_38, A_39) | v1_xboole_0(B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.29/1.46  tff(c_166, plain, (![A_40]: (~r1_tarski(A_40, k1_xboole_0) | v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_6, c_146])).
% 3.29/1.46  tff(c_175, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_166])).
% 3.29/1.46  tff(c_707, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_676, c_175])).
% 3.29/1.46  tff(c_717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_707])).
% 3.29/1.46  tff(c_718, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_195])).
% 3.29/1.46  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.46  tff(c_723, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_718, c_2])).
% 3.29/1.46  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.29/1.46  tff(c_101, plain, (![A_32]: (m1_subset_1('#skF_1'(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.29/1.46  tff(c_108, plain, (m1_subset_1('#skF_1'(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_101])).
% 3.29/1.46  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.46  tff(c_117, plain, (r1_tarski('#skF_1'(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_108, c_16])).
% 3.29/1.46  tff(c_174, plain, (v1_xboole_0('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_117, c_166])).
% 3.29/1.46  tff(c_204, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_174, c_2])).
% 3.29/1.46  tff(c_36, plain, (![A_17]: (v1_funct_2('#skF_1'(A_17), A_17, A_17))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.29/1.46  tff(c_220, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_204, c_36])).
% 3.29/1.46  tff(c_890, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_723, c_723, c_723, c_220])).
% 3.29/1.46  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.46  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.29/1.46  tff(c_22, plain, (![A_14]: (v1_funct_2(k1_xboole_0, A_14, k1_xboole_0) | k1_xboole_0=A_14 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_14, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.29/1.46  tff(c_60, plain, (![A_14]: (v1_funct_2(k1_xboole_0, A_14, k1_xboole_0) | k1_xboole_0=A_14 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_22])).
% 3.29/1.46  tff(c_151, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_60])).
% 3.29/1.46  tff(c_154, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_151])).
% 3.29/1.46  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_154])).
% 3.29/1.46  tff(c_159, plain, (![A_14]: (v1_funct_2(k1_xboole_0, A_14, k1_xboole_0) | k1_xboole_0=A_14)), inference(splitRight, [status(thm)], [c_60])).
% 3.29/1.46  tff(c_965, plain, (![A_97]: (v1_funct_2('#skF_4', A_97, '#skF_4') | A_97='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_723, c_723, c_723, c_159])).
% 3.29/1.46  tff(c_719, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_195])).
% 3.29/1.46  tff(c_727, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_719, c_2])).
% 3.29/1.46  tff(c_749, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_723, c_727])).
% 3.29/1.46  tff(c_753, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_56])).
% 3.29/1.46  tff(c_974, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_965, c_753])).
% 3.29/1.46  tff(c_1002, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_974, c_753])).
% 3.29/1.46  tff(c_1006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_890, c_1002])).
% 3.29/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.46  
% 3.29/1.46  Inference rules
% 3.29/1.46  ----------------------
% 3.29/1.46  #Ref     : 0
% 3.29/1.46  #Sup     : 191
% 3.29/1.46  #Fact    : 0
% 3.29/1.46  #Define  : 0
% 3.29/1.46  #Split   : 3
% 3.29/1.46  #Chain   : 0
% 3.29/1.46  #Close   : 0
% 3.29/1.46  
% 3.29/1.46  Ordering : KBO
% 3.29/1.46  
% 3.29/1.46  Simplification rules
% 3.29/1.46  ----------------------
% 3.29/1.46  #Subsume      : 25
% 3.29/1.46  #Demod        : 292
% 3.29/1.46  #Tautology    : 126
% 3.29/1.46  #SimpNegUnit  : 7
% 3.29/1.46  #BackRed      : 67
% 3.29/1.46  
% 3.29/1.46  #Partial instantiations: 0
% 3.29/1.46  #Strategies tried      : 1
% 3.29/1.46  
% 3.29/1.46  Timing (in seconds)
% 3.29/1.46  ----------------------
% 3.29/1.47  Preprocessing        : 0.28
% 3.29/1.47  Parsing              : 0.15
% 3.29/1.47  CNF conversion       : 0.02
% 3.29/1.47  Main loop            : 0.38
% 3.29/1.47  Inferencing          : 0.13
% 3.29/1.47  Reduction            : 0.13
% 3.29/1.47  Demodulation         : 0.10
% 3.29/1.47  BG Simplification    : 0.02
% 3.29/1.47  Subsumption          : 0.07
% 3.29/1.47  Abstraction          : 0.02
% 3.29/1.47  MUC search           : 0.00
% 3.29/1.47  Cooper               : 0.00
% 3.29/1.47  Total                : 0.70
% 3.29/1.47  Index Insertion      : 0.00
% 3.29/1.47  Index Deletion       : 0.00
% 3.29/1.47  Index Matching       : 0.00
% 3.29/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
