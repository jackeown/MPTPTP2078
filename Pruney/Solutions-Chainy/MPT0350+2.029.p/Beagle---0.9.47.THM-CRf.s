%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:29 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :   70 (  86 expanded)
%              Number of leaves         :   36 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 106 expanded)
%              Number of equality atoms :   29 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_80,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_46,plain,(
    ! [A_32] : k2_subset_1(A_32) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_54,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != k2_subset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_57,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_54])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,(
    ! [A_35] : ~ v1_xboole_0(k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_430,plain,(
    ! [B_79,A_80] :
      ( r2_hidden(B_79,A_80)
      | ~ m1_subset_1(B_79,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [C_27,A_23] :
      ( r1_tarski(C_27,A_23)
      | ~ r2_hidden(C_27,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_434,plain,(
    ! [B_79,A_23] :
      ( r1_tarski(B_79,A_23)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_23))
      | v1_xboole_0(k1_zfmisc_1(A_23)) ) ),
    inference(resolution,[status(thm)],[c_430,c_24])).

tff(c_784,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(B_101,A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_102)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_434])).

tff(c_805,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_784])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_827,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_805,c_10])).

tff(c_16,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_834,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_16])).

tff(c_844,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_834])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_614,plain,(
    ! [A_91,B_92] :
      ( k4_xboole_0(A_91,B_92) = k3_subset_1(A_91,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_623,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_614])).

tff(c_668,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_16])).

tff(c_677,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_668])).

tff(c_852,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_677])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_674,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_14])).

tff(c_26,plain,(
    ! [C_27,A_23] :
      ( r2_hidden(C_27,k1_zfmisc_1(A_23))
      | ~ r1_tarski(C_27,A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_456,plain,(
    ! [B_83,A_84] :
      ( m1_subset_1(B_83,A_84)
      | ~ r2_hidden(B_83,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_462,plain,(
    ! [C_27,A_23] :
      ( m1_subset_1(C_27,k1_zfmisc_1(A_23))
      | v1_xboole_0(k1_zfmisc_1(A_23))
      | ~ r1_tarski(C_27,A_23) ) ),
    inference(resolution,[status(thm)],[c_26,c_456])).

tff(c_469,plain,(
    ! [C_27,A_23] :
      ( m1_subset_1(C_27,k1_zfmisc_1(A_23))
      | ~ r1_tarski(C_27,A_23) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_462])).

tff(c_1830,plain,(
    ! [A_140,B_141,C_142] :
      ( k4_subset_1(A_140,B_141,C_142) = k2_xboole_0(B_141,C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(A_140))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4039,plain,(
    ! [A_190,B_191,C_192] :
      ( k4_subset_1(A_190,B_191,C_192) = k2_xboole_0(B_191,C_192)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(A_190))
      | ~ r1_tarski(C_192,A_190) ) ),
    inference(resolution,[status(thm)],[c_469,c_1830])).

tff(c_4202,plain,(
    ! [C_197] :
      ( k4_subset_1('#skF_4','#skF_5',C_197) = k2_xboole_0('#skF_5',C_197)
      | ~ r1_tarski(C_197,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_4039])).

tff(c_4272,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_674,c_4202])).

tff(c_4312,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_4272])).

tff(c_4314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_4312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:42:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.90/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.93  
% 4.90/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.93  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 4.90/1.93  
% 4.90/1.93  %Foreground sorts:
% 4.90/1.93  
% 4.90/1.93  
% 4.90/1.93  %Background operators:
% 4.90/1.93  
% 4.90/1.93  
% 4.90/1.93  %Foreground operators:
% 4.90/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.90/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.90/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.90/1.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.90/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.90/1.93  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.90/1.93  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.90/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.90/1.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.90/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.90/1.93  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.90/1.93  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.90/1.93  tff('#skF_5', type, '#skF_5': $i).
% 4.90/1.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.90/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.90/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.90/1.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.90/1.93  tff('#skF_4', type, '#skF_4': $i).
% 4.90/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.90/1.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.90/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.90/1.93  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.90/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.90/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.90/1.93  
% 4.90/1.94  tff(f_73, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.90/1.94  tff(f_91, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 4.90/1.94  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.90/1.94  tff(f_80, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.90/1.94  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.90/1.94  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.90/1.94  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.90/1.94  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.90/1.94  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.90/1.94  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.90/1.94  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.90/1.94  tff(f_86, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.90/1.94  tff(c_46, plain, (![A_32]: (k2_subset_1(A_32)=A_32)), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.90/1.94  tff(c_54, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!=k2_subset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.90/1.94  tff(c_57, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_54])).
% 4.90/1.94  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.90/1.94  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.90/1.94  tff(c_50, plain, (![A_35]: (~v1_xboole_0(k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.90/1.94  tff(c_430, plain, (![B_79, A_80]: (r2_hidden(B_79, A_80) | ~m1_subset_1(B_79, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.90/1.94  tff(c_24, plain, (![C_27, A_23]: (r1_tarski(C_27, A_23) | ~r2_hidden(C_27, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.90/1.94  tff(c_434, plain, (![B_79, A_23]: (r1_tarski(B_79, A_23) | ~m1_subset_1(B_79, k1_zfmisc_1(A_23)) | v1_xboole_0(k1_zfmisc_1(A_23)))), inference(resolution, [status(thm)], [c_430, c_24])).
% 4.90/1.94  tff(c_784, plain, (![B_101, A_102]: (r1_tarski(B_101, A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_102)))), inference(negUnitSimplification, [status(thm)], [c_50, c_434])).
% 4.90/1.94  tff(c_805, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_784])).
% 4.90/1.94  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.90/1.94  tff(c_827, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_805, c_10])).
% 4.90/1.94  tff(c_16, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.90/1.94  tff(c_834, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_827, c_16])).
% 4.90/1.94  tff(c_844, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_834])).
% 4.90/1.94  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.90/1.94  tff(c_614, plain, (![A_91, B_92]: (k4_xboole_0(A_91, B_92)=k3_subset_1(A_91, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.90/1.94  tff(c_623, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_614])).
% 4.90/1.94  tff(c_668, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_623, c_16])).
% 4.90/1.94  tff(c_677, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_668])).
% 4.90/1.94  tff(c_852, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_844, c_677])).
% 4.90/1.94  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.90/1.94  tff(c_674, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_623, c_14])).
% 4.90/1.94  tff(c_26, plain, (![C_27, A_23]: (r2_hidden(C_27, k1_zfmisc_1(A_23)) | ~r1_tarski(C_27, A_23))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.90/1.94  tff(c_456, plain, (![B_83, A_84]: (m1_subset_1(B_83, A_84) | ~r2_hidden(B_83, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.90/1.94  tff(c_462, plain, (![C_27, A_23]: (m1_subset_1(C_27, k1_zfmisc_1(A_23)) | v1_xboole_0(k1_zfmisc_1(A_23)) | ~r1_tarski(C_27, A_23))), inference(resolution, [status(thm)], [c_26, c_456])).
% 4.90/1.94  tff(c_469, plain, (![C_27, A_23]: (m1_subset_1(C_27, k1_zfmisc_1(A_23)) | ~r1_tarski(C_27, A_23))), inference(negUnitSimplification, [status(thm)], [c_50, c_462])).
% 4.90/1.94  tff(c_1830, plain, (![A_140, B_141, C_142]: (k4_subset_1(A_140, B_141, C_142)=k2_xboole_0(B_141, C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(A_140)) | ~m1_subset_1(B_141, k1_zfmisc_1(A_140)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.90/1.94  tff(c_4039, plain, (![A_190, B_191, C_192]: (k4_subset_1(A_190, B_191, C_192)=k2_xboole_0(B_191, C_192) | ~m1_subset_1(B_191, k1_zfmisc_1(A_190)) | ~r1_tarski(C_192, A_190))), inference(resolution, [status(thm)], [c_469, c_1830])).
% 4.90/1.94  tff(c_4202, plain, (![C_197]: (k4_subset_1('#skF_4', '#skF_5', C_197)=k2_xboole_0('#skF_5', C_197) | ~r1_tarski(C_197, '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_4039])).
% 4.90/1.94  tff(c_4272, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_674, c_4202])).
% 4.90/1.94  tff(c_4312, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_852, c_4272])).
% 4.90/1.94  tff(c_4314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_4312])).
% 4.90/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.94  
% 4.90/1.94  Inference rules
% 4.90/1.94  ----------------------
% 4.90/1.94  #Ref     : 0
% 4.90/1.94  #Sup     : 986
% 4.90/1.94  #Fact    : 0
% 4.90/1.94  #Define  : 0
% 4.90/1.94  #Split   : 2
% 4.90/1.94  #Chain   : 0
% 4.90/1.94  #Close   : 0
% 4.90/1.94  
% 4.90/1.94  Ordering : KBO
% 4.90/1.94  
% 4.90/1.94  Simplification rules
% 4.90/1.94  ----------------------
% 4.90/1.94  #Subsume      : 34
% 4.90/1.94  #Demod        : 1521
% 4.90/1.94  #Tautology    : 706
% 4.90/1.94  #SimpNegUnit  : 21
% 4.90/1.94  #BackRed      : 0
% 4.90/1.94  
% 4.90/1.94  #Partial instantiations: 0
% 4.90/1.94  #Strategies tried      : 1
% 4.90/1.94  
% 4.90/1.94  Timing (in seconds)
% 4.90/1.94  ----------------------
% 4.90/1.95  Preprocessing        : 0.33
% 4.90/1.95  Parsing              : 0.17
% 4.90/1.95  CNF conversion       : 0.02
% 4.90/1.95  Main loop            : 0.85
% 4.90/1.95  Inferencing          : 0.28
% 4.90/1.95  Reduction            : 0.37
% 4.90/1.95  Demodulation         : 0.28
% 4.90/1.95  BG Simplification    : 0.03
% 4.90/1.95  Subsumption          : 0.12
% 4.90/1.95  Abstraction          : 0.04
% 4.90/1.95  MUC search           : 0.00
% 4.90/1.95  Cooper               : 0.00
% 4.90/1.95  Total                : 1.21
% 4.90/1.95  Index Insertion      : 0.00
% 4.90/1.95  Index Deletion       : 0.00
% 4.90/1.95  Index Matching       : 0.00
% 4.90/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
