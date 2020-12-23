%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:44 EST 2020

% Result     : Theorem 7.27s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :   78 (  86 expanded)
%              Number of leaves         :   41 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   74 (  84 expanded)
%              Number of equality atoms :   38 (  45 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_83,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_63,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_44,plain,(
    ! [A_50] : k2_subset_1(A_50) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_55,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_52])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48,plain,(
    ! [A_52] : ~ v1_xboole_0(k1_zfmisc_1(A_52)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_279,plain,(
    ! [B_83,A_84] :
      ( r2_hidden(B_83,A_84)
      | ~ m1_subset_1(B_83,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    ! [A_47] : k3_tarski(k1_zfmisc_1(A_47)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_242,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,k3_tarski(B_70))
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_248,plain,(
    ! [A_69,A_47] :
      ( r1_tarski(A_69,A_47)
      | ~ r2_hidden(A_69,k1_zfmisc_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_242])).

tff(c_286,plain,(
    ! [B_83,A_47] :
      ( r1_tarski(B_83,A_47)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_47))
      | v1_xboole_0(k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_279,c_248])).

tff(c_291,plain,(
    ! [B_85,A_86] :
      ( r1_tarski(B_85,A_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_286])).

tff(c_304,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_291])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_336,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_304,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_356,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_373,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_6])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_136,plain,(
    ! [B_64,A_65] : k5_xboole_0(B_64,A_65) = k5_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    ! [A_65] : k5_xboole_0(k1_xboole_0,A_65) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_10])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_632,plain,(
    ! [A_105,B_106,C_107] : k5_xboole_0(k5_xboole_0(A_105,B_106),C_107) = k5_xboole_0(A_105,k5_xboole_0(B_106,C_107)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_721,plain,(
    ! [A_13,C_107] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_107)) = k5_xboole_0(k1_xboole_0,C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_632])).

tff(c_735,plain,(
    ! [A_108,C_109] : k5_xboole_0(A_108,k5_xboole_0(A_108,C_109)) = C_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_721])).

tff(c_809,plain,(
    ! [A_110,B_111] : k5_xboole_0(A_110,k5_xboole_0(B_111,A_110)) = B_111 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_735])).

tff(c_859,plain,(
    k5_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_809])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1156,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_859,c_16])).

tff(c_46,plain,(
    ! [A_51] : m1_subset_1(k2_subset_1(A_51),k1_zfmisc_1(A_51)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ! [A_51] : m1_subset_1(A_51,k1_zfmisc_1(A_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_1591,plain,(
    ! [A_136,B_137,C_138] :
      ( k4_subset_1(A_136,B_137,C_138) = k2_xboole_0(B_137,C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(A_136))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_9182,plain,(
    ! [A_232,B_233] :
      ( k4_subset_1(A_232,B_233,A_232) = k2_xboole_0(B_233,A_232)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(A_232)) ) ),
    inference(resolution,[status(thm)],[c_56,c_1591])).

tff(c_9189,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_9182])).

tff(c_9194,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_9189])).

tff(c_9196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_9194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.27/2.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.30/2.71  
% 7.30/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.71  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.31/2.71  
% 7.31/2.71  %Foreground sorts:
% 7.31/2.71  
% 7.31/2.71  
% 7.31/2.71  %Background operators:
% 7.31/2.71  
% 7.31/2.71  
% 7.31/2.71  %Foreground operators:
% 7.31/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.31/2.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.31/2.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.31/2.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.31/2.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.31/2.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.31/2.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.31/2.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.31/2.71  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.31/2.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.31/2.71  tff('#skF_2', type, '#skF_2': $i).
% 7.31/2.71  tff('#skF_1', type, '#skF_1': $i).
% 7.31/2.71  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.31/2.71  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.71  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.31/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.31/2.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.31/2.71  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.71  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.31/2.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.31/2.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.31/2.71  
% 7.31/2.72  tff(f_78, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.31/2.72  tff(f_94, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 7.31/2.72  tff(f_83, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 7.31/2.72  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 7.31/2.72  tff(f_63, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 7.31/2.72  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 7.31/2.72  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.31/2.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.31/2.72  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.31/2.72  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.31/2.72  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.31/2.72  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.31/2.72  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.31/2.72  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.31/2.72  tff(f_80, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.31/2.72  tff(f_89, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.31/2.72  tff(c_44, plain, (![A_50]: (k2_subset_1(A_50)=A_50)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.31/2.72  tff(c_52, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.31/2.72  tff(c_55, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_52])).
% 7.31/2.72  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.31/2.72  tff(c_48, plain, (![A_52]: (~v1_xboole_0(k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.31/2.72  tff(c_279, plain, (![B_83, A_84]: (r2_hidden(B_83, A_84) | ~m1_subset_1(B_83, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.31/2.72  tff(c_34, plain, (![A_47]: (k3_tarski(k1_zfmisc_1(A_47))=A_47)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.31/2.72  tff(c_242, plain, (![A_69, B_70]: (r1_tarski(A_69, k3_tarski(B_70)) | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.31/2.72  tff(c_248, plain, (![A_69, A_47]: (r1_tarski(A_69, A_47) | ~r2_hidden(A_69, k1_zfmisc_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_242])).
% 7.31/2.72  tff(c_286, plain, (![B_83, A_47]: (r1_tarski(B_83, A_47) | ~m1_subset_1(B_83, k1_zfmisc_1(A_47)) | v1_xboole_0(k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_279, c_248])).
% 7.31/2.72  tff(c_291, plain, (![B_85, A_86]: (r1_tarski(B_85, A_86) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)))), inference(negUnitSimplification, [status(thm)], [c_48, c_286])).
% 7.31/2.72  tff(c_304, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_291])).
% 7.31/2.72  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.31/2.72  tff(c_336, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_304, c_8])).
% 7.31/2.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.31/2.72  tff(c_356, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_336, c_2])).
% 7.31/2.72  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.31/2.72  tff(c_373, plain, (k5_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_356, c_6])).
% 7.31/2.72  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.31/2.72  tff(c_136, plain, (![B_64, A_65]: (k5_xboole_0(B_64, A_65)=k5_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.31/2.72  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.31/2.72  tff(c_152, plain, (![A_65]: (k5_xboole_0(k1_xboole_0, A_65)=A_65)), inference(superposition, [status(thm), theory('equality')], [c_136, c_10])).
% 7.31/2.72  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.31/2.72  tff(c_632, plain, (![A_105, B_106, C_107]: (k5_xboole_0(k5_xboole_0(A_105, B_106), C_107)=k5_xboole_0(A_105, k5_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.31/2.72  tff(c_721, plain, (![A_13, C_107]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_107))=k5_xboole_0(k1_xboole_0, C_107))), inference(superposition, [status(thm), theory('equality')], [c_14, c_632])).
% 7.31/2.72  tff(c_735, plain, (![A_108, C_109]: (k5_xboole_0(A_108, k5_xboole_0(A_108, C_109))=C_109)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_721])).
% 7.31/2.72  tff(c_809, plain, (![A_110, B_111]: (k5_xboole_0(A_110, k5_xboole_0(B_111, A_110))=B_111)), inference(superposition, [status(thm), theory('equality')], [c_4, c_735])).
% 7.31/2.72  tff(c_859, plain, (k5_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_373, c_809])).
% 7.31/2.72  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.31/2.72  tff(c_1156, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_859, c_16])).
% 7.31/2.72  tff(c_46, plain, (![A_51]: (m1_subset_1(k2_subset_1(A_51), k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.31/2.72  tff(c_56, plain, (![A_51]: (m1_subset_1(A_51, k1_zfmisc_1(A_51)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 7.31/2.72  tff(c_1591, plain, (![A_136, B_137, C_138]: (k4_subset_1(A_136, B_137, C_138)=k2_xboole_0(B_137, C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(A_136)) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.31/2.72  tff(c_9182, plain, (![A_232, B_233]: (k4_subset_1(A_232, B_233, A_232)=k2_xboole_0(B_233, A_232) | ~m1_subset_1(B_233, k1_zfmisc_1(A_232)))), inference(resolution, [status(thm)], [c_56, c_1591])).
% 7.31/2.72  tff(c_9189, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_9182])).
% 7.31/2.72  tff(c_9194, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_9189])).
% 7.31/2.72  tff(c_9196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_9194])).
% 7.31/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.72  
% 7.31/2.72  Inference rules
% 7.31/2.72  ----------------------
% 7.31/2.72  #Ref     : 0
% 7.31/2.72  #Sup     : 2264
% 7.31/2.72  #Fact    : 0
% 7.31/2.72  #Define  : 0
% 7.31/2.72  #Split   : 0
% 7.31/2.72  #Chain   : 0
% 7.31/2.72  #Close   : 0
% 7.31/2.72  
% 7.31/2.72  Ordering : KBO
% 7.31/2.72  
% 7.31/2.72  Simplification rules
% 7.31/2.72  ----------------------
% 7.31/2.72  #Subsume      : 146
% 7.31/2.72  #Demod        : 2424
% 7.31/2.72  #Tautology    : 1218
% 7.31/2.72  #SimpNegUnit  : 5
% 7.31/2.72  #BackRed      : 0
% 7.31/2.72  
% 7.31/2.72  #Partial instantiations: 0
% 7.31/2.72  #Strategies tried      : 1
% 7.31/2.72  
% 7.31/2.72  Timing (in seconds)
% 7.31/2.72  ----------------------
% 7.31/2.73  Preprocessing        : 0.34
% 7.31/2.73  Parsing              : 0.19
% 7.31/2.73  CNF conversion       : 0.02
% 7.31/2.73  Main loop            : 1.57
% 7.31/2.73  Inferencing          : 0.39
% 7.31/2.73  Reduction            : 0.86
% 7.31/2.73  Demodulation         : 0.76
% 7.31/2.73  BG Simplification    : 0.05
% 7.31/2.73  Subsumption          : 0.21
% 7.31/2.73  Abstraction          : 0.07
% 7.31/2.73  MUC search           : 0.00
% 7.31/2.73  Cooper               : 0.00
% 7.31/2.73  Total                : 1.94
% 7.31/2.73  Index Insertion      : 0.00
% 7.31/2.73  Index Deletion       : 0.00
% 7.31/2.73  Index Matching       : 0.00
% 7.31/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
