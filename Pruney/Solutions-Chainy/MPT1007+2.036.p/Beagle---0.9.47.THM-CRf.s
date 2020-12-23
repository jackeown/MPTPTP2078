%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:16 EST 2020

% Result     : Theorem 8.16s
% Output     : CNFRefutation 8.16s
% Verified   : 
% Statistics : Number of formulae       :   68 (  83 expanded)
%              Number of leaves         :   39 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 140 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_122,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_126,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_122])).

tff(c_136,plain,(
    ! [C_63,B_64,A_65] :
      ( v5_relat_1(C_63,B_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_140,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_136])).

tff(c_40,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v5_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_70,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_246,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_250,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_246])).

tff(c_2998,plain,(
    ! [B_3502,A_3503,C_3504] :
      ( k1_xboole_0 = B_3502
      | k1_relset_1(A_3503,B_3502,C_3504) = A_3503
      | ~ v1_funct_2(C_3504,A_3503,B_3502)
      | ~ m1_subset_1(C_3504,k1_zfmisc_1(k2_zfmisc_1(A_3503,B_3502))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3013,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_2998])).

tff(c_3016,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_250,c_3013])).

tff(c_3017,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3016])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [E_12,B_7,C_8] : r2_hidden(E_12,k1_enumset1(E_12,B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_103,plain,(
    ! [A_47,B_48] : r2_hidden(A_47,k2_tarski(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_14])).

tff(c_106,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_103])).

tff(c_3065,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3017,c_106])).

tff(c_363,plain,(
    ! [B_122,A_123] :
      ( r2_hidden(k1_funct_1(B_122,A_123),k2_relat_1(B_122))
      | ~ r2_hidden(A_123,k1_relat_1(B_122))
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_17281,plain,(
    ! [B_16511,A_16512,B_16513] :
      ( r2_hidden(k1_funct_1(B_16511,A_16512),B_16513)
      | ~ r1_tarski(k2_relat_1(B_16511),B_16513)
      | ~ r2_hidden(A_16512,k1_relat_1(B_16511))
      | ~ v1_funct_1(B_16511)
      | ~ v1_relat_1(B_16511) ) ),
    inference(resolution,[status(thm)],[c_363,c_2])).

tff(c_64,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_17302,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_17281,c_64])).

tff(c_17319,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_72,c_3065,c_17302])).

tff(c_17322,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_17319])).

tff(c_17326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_140,c_17322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:11:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.16/2.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.16/2.84  
% 8.16/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.16/2.84  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 8.16/2.84  
% 8.16/2.84  %Foreground sorts:
% 8.16/2.84  
% 8.16/2.84  
% 8.16/2.84  %Background operators:
% 8.16/2.84  
% 8.16/2.84  
% 8.16/2.84  %Foreground operators:
% 8.16/2.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.16/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.16/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.16/2.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.16/2.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.16/2.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.16/2.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.16/2.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.16/2.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.16/2.84  tff('#skF_5', type, '#skF_5': $i).
% 8.16/2.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.16/2.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 8.16/2.84  tff('#skF_6', type, '#skF_6': $i).
% 8.16/2.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.16/2.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.16/2.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.16/2.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.16/2.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.16/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.16/2.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.16/2.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.16/2.84  tff('#skF_4', type, '#skF_4': $i).
% 8.16/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.16/2.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.16/2.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 8.16/2.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.16/2.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.16/2.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.16/2.84  
% 8.16/2.85  tff(f_111, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 8.16/2.85  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.16/2.85  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.16/2.85  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.16/2.85  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.16/2.85  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.16/2.85  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.16/2.85  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 8.16/2.85  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 8.16/2.85  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 8.16/2.85  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.16/2.85  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.16/2.85  tff(c_122, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.16/2.85  tff(c_126, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_122])).
% 8.16/2.85  tff(c_136, plain, (![C_63, B_64, A_65]: (v5_relat_1(C_63, B_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.16/2.85  tff(c_140, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_136])).
% 8.16/2.85  tff(c_40, plain, (![B_20, A_19]: (r1_tarski(k2_relat_1(B_20), A_19) | ~v5_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.16/2.85  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.16/2.85  tff(c_66, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.16/2.85  tff(c_70, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.16/2.85  tff(c_246, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.16/2.85  tff(c_250, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_246])).
% 8.16/2.85  tff(c_2998, plain, (![B_3502, A_3503, C_3504]: (k1_xboole_0=B_3502 | k1_relset_1(A_3503, B_3502, C_3504)=A_3503 | ~v1_funct_2(C_3504, A_3503, B_3502) | ~m1_subset_1(C_3504, k1_zfmisc_1(k2_zfmisc_1(A_3503, B_3502))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.16/2.85  tff(c_3013, plain, (k1_xboole_0='#skF_5' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4') | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_68, c_2998])).
% 8.16/2.85  tff(c_3016, plain, (k1_xboole_0='#skF_5' | k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_250, c_3013])).
% 8.16/2.85  tff(c_3017, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_3016])).
% 8.16/2.85  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.16/2.85  tff(c_85, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.16/2.85  tff(c_14, plain, (![E_12, B_7, C_8]: (r2_hidden(E_12, k1_enumset1(E_12, B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.16/2.85  tff(c_103, plain, (![A_47, B_48]: (r2_hidden(A_47, k2_tarski(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_14])).
% 8.16/2.85  tff(c_106, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_103])).
% 8.16/2.85  tff(c_3065, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3017, c_106])).
% 8.16/2.85  tff(c_363, plain, (![B_122, A_123]: (r2_hidden(k1_funct_1(B_122, A_123), k2_relat_1(B_122)) | ~r2_hidden(A_123, k1_relat_1(B_122)) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.16/2.85  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.16/2.85  tff(c_17281, plain, (![B_16511, A_16512, B_16513]: (r2_hidden(k1_funct_1(B_16511, A_16512), B_16513) | ~r1_tarski(k2_relat_1(B_16511), B_16513) | ~r2_hidden(A_16512, k1_relat_1(B_16511)) | ~v1_funct_1(B_16511) | ~v1_relat_1(B_16511))), inference(resolution, [status(thm)], [c_363, c_2])).
% 8.16/2.85  tff(c_64, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.16/2.85  tff(c_17302, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_17281, c_64])).
% 8.16/2.85  tff(c_17319, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_72, c_3065, c_17302])).
% 8.16/2.85  tff(c_17322, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_17319])).
% 8.16/2.85  tff(c_17326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_140, c_17322])).
% 8.16/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.16/2.85  
% 8.16/2.85  Inference rules
% 8.16/2.85  ----------------------
% 8.16/2.85  #Ref     : 0
% 8.16/2.85  #Sup     : 2594
% 8.16/2.85  #Fact    : 25
% 8.16/2.85  #Define  : 0
% 8.16/2.85  #Split   : 6
% 8.16/2.85  #Chain   : 0
% 8.16/2.85  #Close   : 0
% 8.16/2.85  
% 8.16/2.85  Ordering : KBO
% 8.16/2.85  
% 8.16/2.85  Simplification rules
% 8.16/2.85  ----------------------
% 8.16/2.85  #Subsume      : 476
% 8.16/2.85  #Demod        : 337
% 8.16/2.85  #Tautology    : 245
% 8.16/2.85  #SimpNegUnit  : 59
% 8.16/2.85  #BackRed      : 4
% 8.16/2.85  
% 8.16/2.85  #Partial instantiations: 9384
% 8.16/2.85  #Strategies tried      : 1
% 8.16/2.85  
% 8.16/2.85  Timing (in seconds)
% 8.16/2.85  ----------------------
% 8.16/2.86  Preprocessing        : 0.34
% 8.16/2.86  Parsing              : 0.18
% 8.16/2.86  CNF conversion       : 0.02
% 8.16/2.86  Main loop            : 1.74
% 8.16/2.86  Inferencing          : 0.72
% 8.16/2.86  Reduction            : 0.39
% 8.16/2.86  Demodulation         : 0.28
% 8.16/2.86  BG Simplification    : 0.10
% 8.16/2.86  Subsumption          : 0.42
% 8.16/2.86  Abstraction          : 0.10
% 8.16/2.86  MUC search           : 0.00
% 8.16/2.86  Cooper               : 0.00
% 8.16/2.86  Total                : 2.11
% 8.16/2.86  Index Insertion      : 0.00
% 8.16/2.86  Index Deletion       : 0.00
% 8.16/2.86  Index Matching       : 0.00
% 8.16/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
