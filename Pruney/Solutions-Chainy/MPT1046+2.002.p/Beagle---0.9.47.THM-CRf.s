%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:06 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 409 expanded)
%              Number of leaves         :   30 ( 144 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 789 expanded)
%              Number of equality atoms :   36 ( 198 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_enumset1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => k5_partfun1(A,A,k3_partfun1(B,A,A)) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k5_partfun1(A,B,k3_partfun1(C,A,B)) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_48,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
      <=> k5_partfun1(A,B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_partfun1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_93,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_xboole_0(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_107,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_93])).

tff(c_108,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_109,plain,(
    ! [C_30,A_31,B_32] :
      ( k3_partfun1(C_30,A_31,B_32) = C_30
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_118,plain,
    ( k3_partfun1('#skF_2','#skF_1','#skF_1') = '#skF_2'
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_109])).

tff(c_123,plain,(
    k3_partfun1('#skF_2','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_118])).

tff(c_30,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_134,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_2') != k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_30])).

tff(c_34,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_353,plain,(
    ! [B_50,A_51,C_52] :
      ( k1_xboole_0 = B_50
      | k5_partfun1(A_51,B_50,k3_partfun1(C_52,A_51,B_50)) = k1_tarski(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50)))
      | ~ v1_funct_2(C_52,A_51,B_50)
      | ~ v1_funct_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_365,plain,
    ( k1_xboole_0 = '#skF_1'
    | k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) = k1_tarski('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_353])).

tff(c_373,plain,
    ( k1_xboole_0 = '#skF_1'
    | k5_partfun1('#skF_1','#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_123,c_365])).

tff(c_374,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_373])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_389,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_2])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_389])).

tff(c_393,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_401,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_393,c_4])).

tff(c_392,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_397,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_392,c_4])).

tff(c_413,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_397])).

tff(c_422,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_36])).

tff(c_47,plain,(
    ! [A_21] : k6_relat_1(A_21) = k6_partfun1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_10])).

tff(c_80,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_83,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_80])).

tff(c_402,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_397,c_397,c_83])).

tff(c_474,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_413,c_413,c_402])).

tff(c_28,plain,(
    ! [C_19,A_17,B_18] :
      ( k3_partfun1(C_19,A_17,B_18) = C_19
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_477,plain,
    ( k3_partfun1('#skF_1','#skF_1','#skF_1') = '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_474,c_28])).

tff(c_483,plain,(
    k3_partfun1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_477])).

tff(c_419,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_1','#skF_1','#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_413,c_30])).

tff(c_505,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_419])).

tff(c_67,plain,(
    ! [A_22] : v1_partfun1(k6_partfun1(A_22),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_67])).

tff(c_403,plain,(
    v1_partfun1('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_397,c_70])).

tff(c_444,plain,(
    v1_partfun1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_413,c_403])).

tff(c_616,plain,(
    ! [A_67,B_68,C_69] :
      ( k5_partfun1(A_67,B_68,C_69) = k1_tarski(C_69)
      | ~ v1_partfun1(C_69,A_67)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_622,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_1') = k1_tarski('#skF_1')
    | ~ v1_partfun1('#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_474,c_616])).

tff(c_631,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_1') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_444,c_622])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 17:18:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.33  
% 2.55/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.33  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_enumset1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.55/1.33  
% 2.55/1.33  %Foreground sorts:
% 2.55/1.33  
% 2.55/1.33  
% 2.55/1.33  %Background operators:
% 2.55/1.33  
% 2.55/1.33  
% 2.55/1.33  %Foreground operators:
% 2.55/1.33  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 2.55/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.55/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.55/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.55/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.55/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.55/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.33  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.33  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 2.55/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.33  
% 2.55/1.34  tff(f_83, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k5_partfun1(A, A, k3_partfun1(B, A, A)) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_2)).
% 2.55/1.34  tff(f_42, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.55/1.34  tff(f_74, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_partfun1)).
% 2.55/1.34  tff(f_60, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k5_partfun1(A, B, k3_partfun1(C, A, B)) = k1_tarski(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t161_funct_2)).
% 2.55/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.55/1.34  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.55/1.34  tff(f_48, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.55/1.34  tff(f_35, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.55/1.34  tff(f_46, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.55/1.34  tff(f_68, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) <=> (k5_partfun1(A, B, C) = k1_tarski(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_partfun1)).
% 2.55/1.34  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.55/1.34  tff(c_93, plain, (![C_27, A_28, B_29]: (v1_xboole_0(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.55/1.34  tff(c_107, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_93])).
% 2.55/1.34  tff(c_108, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_107])).
% 2.55/1.34  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.55/1.34  tff(c_109, plain, (![C_30, A_31, B_32]: (k3_partfun1(C_30, A_31, B_32)=C_30 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_1(C_30))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.55/1.34  tff(c_118, plain, (k3_partfun1('#skF_2', '#skF_1', '#skF_1')='#skF_2' | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_109])).
% 2.55/1.34  tff(c_123, plain, (k3_partfun1('#skF_2', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_118])).
% 2.55/1.34  tff(c_30, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.55/1.34  tff(c_134, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')!=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_30])).
% 2.55/1.34  tff(c_34, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.55/1.34  tff(c_353, plain, (![B_50, A_51, C_52]: (k1_xboole_0=B_50 | k5_partfun1(A_51, B_50, k3_partfun1(C_52, A_51, B_50))=k1_tarski(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))) | ~v1_funct_2(C_52, A_51, B_50) | ~v1_funct_1(C_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.55/1.34  tff(c_365, plain, (k1_xboole_0='#skF_1' | k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))=k1_tarski('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_353])).
% 2.55/1.34  tff(c_373, plain, (k1_xboole_0='#skF_1' | k5_partfun1('#skF_1', '#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_123, c_365])).
% 2.55/1.34  tff(c_374, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_134, c_373])).
% 2.55/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.55/1.34  tff(c_389, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_374, c_2])).
% 2.55/1.34  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_389])).
% 2.55/1.34  tff(c_393, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_107])).
% 2.55/1.34  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.55/1.34  tff(c_401, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_393, c_4])).
% 2.55/1.34  tff(c_392, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_107])).
% 2.55/1.34  tff(c_397, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_392, c_4])).
% 2.55/1.34  tff(c_413, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_401, c_397])).
% 2.55/1.34  tff(c_422, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_36])).
% 2.55/1.34  tff(c_47, plain, (![A_21]: (k6_relat_1(A_21)=k6_partfun1(A_21))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.55/1.34  tff(c_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.55/1.34  tff(c_53, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_47, c_10])).
% 2.55/1.34  tff(c_80, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.55/1.34  tff(c_83, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_80])).
% 2.55/1.34  tff(c_402, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_397, c_397, c_397, c_83])).
% 2.55/1.34  tff(c_474, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_413, c_413, c_413, c_402])).
% 2.55/1.34  tff(c_28, plain, (![C_19, A_17, B_18]: (k3_partfun1(C_19, A_17, B_18)=C_19 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_1(C_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.55/1.34  tff(c_477, plain, (k3_partfun1('#skF_1', '#skF_1', '#skF_1')='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_474, c_28])).
% 2.55/1.34  tff(c_483, plain, (k3_partfun1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_422, c_477])).
% 2.55/1.34  tff(c_419, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_1', '#skF_1', '#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_413, c_30])).
% 2.55/1.34  tff(c_505, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_483, c_419])).
% 2.55/1.34  tff(c_67, plain, (![A_22]: (v1_partfun1(k6_partfun1(A_22), A_22))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.55/1.34  tff(c_70, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_53, c_67])).
% 2.55/1.34  tff(c_403, plain, (v1_partfun1('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_397, c_397, c_70])).
% 2.55/1.34  tff(c_444, plain, (v1_partfun1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_413, c_403])).
% 2.55/1.34  tff(c_616, plain, (![A_67, B_68, C_69]: (k5_partfun1(A_67, B_68, C_69)=k1_tarski(C_69) | ~v1_partfun1(C_69, A_67) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_1(C_69))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.55/1.34  tff(c_622, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_1')=k1_tarski('#skF_1') | ~v1_partfun1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_474, c_616])).
% 2.55/1.34  tff(c_631, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_1')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_422, c_444, c_622])).
% 2.55/1.34  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_505, c_631])).
% 2.55/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  Inference rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Ref     : 0
% 2.55/1.34  #Sup     : 130
% 2.55/1.34  #Fact    : 0
% 2.55/1.34  #Define  : 0
% 2.55/1.34  #Split   : 2
% 2.55/1.34  #Chain   : 0
% 2.55/1.34  #Close   : 0
% 2.55/1.34  
% 2.55/1.34  Ordering : KBO
% 2.55/1.34  
% 2.55/1.34  Simplification rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Subsume      : 23
% 2.55/1.34  #Demod        : 162
% 2.55/1.34  #Tautology    : 76
% 2.55/1.34  #SimpNegUnit  : 4
% 2.55/1.34  #BackRed      : 28
% 2.55/1.34  
% 2.55/1.34  #Partial instantiations: 0
% 2.55/1.34  #Strategies tried      : 1
% 2.55/1.34  
% 2.55/1.34  Timing (in seconds)
% 2.55/1.34  ----------------------
% 2.55/1.35  Preprocessing        : 0.31
% 2.55/1.35  Parsing              : 0.16
% 2.55/1.35  CNF conversion       : 0.02
% 2.55/1.35  Main loop            : 0.28
% 2.55/1.35  Inferencing          : 0.09
% 2.55/1.35  Reduction            : 0.10
% 2.55/1.35  Demodulation         : 0.07
% 2.55/1.35  BG Simplification    : 0.02
% 2.55/1.35  Subsumption          : 0.05
% 2.55/1.35  Abstraction          : 0.02
% 2.55/1.35  MUC search           : 0.00
% 2.55/1.35  Cooper               : 0.00
% 2.55/1.35  Total                : 0.62
% 2.55/1.35  Index Insertion      : 0.00
% 2.55/1.35  Index Deletion       : 0.00
% 2.55/1.35  Index Matching       : 0.00
% 2.55/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
