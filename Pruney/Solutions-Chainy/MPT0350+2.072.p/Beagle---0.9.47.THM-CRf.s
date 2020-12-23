%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:35 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   66 (  80 expanded)
%              Number of leaves         :   35 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 100 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_42,plain,(
    ! [A_29] : k2_subset_1(A_29) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != k2_subset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_53,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_50])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [A_32] : ~ v1_xboole_0(k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_210,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(B_69,A_70)
      | ~ m1_subset_1(B_69,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [C_24,A_20] :
      ( r1_tarski(C_24,A_20)
      | ~ r2_hidden(C_24,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_217,plain,(
    ! [B_69,A_20] :
      ( r1_tarski(B_69,A_20)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_210,c_20])).

tff(c_226,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(B_71,A_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_217])).

tff(c_246,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_226])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_250,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_246,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_260,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_2])).

tff(c_346,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = k3_subset_1(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_366,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_346])).

tff(c_14,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(A_13,B_14),k4_xboole_0(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_372,plain,(
    k2_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_14])).

tff(c_378,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_372])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_375,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_12])).

tff(c_22,plain,(
    ! [C_24,A_20] :
      ( r2_hidden(C_24,k1_zfmisc_1(A_20))
      | ~ r1_tarski(C_24,A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_159,plain,(
    ! [B_60,A_61] :
      ( m1_subset_1(B_60,A_61)
      | ~ r2_hidden(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_162,plain,(
    ! [C_24,A_20] :
      ( m1_subset_1(C_24,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20))
      | ~ r1_tarski(C_24,A_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_159])).

tff(c_168,plain,(
    ! [C_24,A_20] :
      ( m1_subset_1(C_24,k1_zfmisc_1(A_20))
      | ~ r1_tarski(C_24,A_20) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_162])).

tff(c_925,plain,(
    ! [A_113,B_114,C_115] :
      ( k4_subset_1(A_113,B_114,C_115) = k2_xboole_0(B_114,C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(A_113))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1766,plain,(
    ! [A_158,B_159,C_160] :
      ( k4_subset_1(A_158,B_159,C_160) = k2_xboole_0(B_159,C_160)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_158))
      | ~ r1_tarski(C_160,A_158) ) ),
    inference(resolution,[status(thm)],[c_168,c_925])).

tff(c_1789,plain,(
    ! [C_161] :
      ( k4_subset_1('#skF_4','#skF_5',C_161) = k2_xboole_0('#skF_5',C_161)
      | ~ r1_tarski(C_161,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_1766])).

tff(c_1845,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_375,c_1789])).

tff(c_1871,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_1845])).

tff(c_1873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.68  
% 3.92/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.69  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 3.92/1.69  
% 3.92/1.69  %Foreground sorts:
% 3.92/1.69  
% 3.92/1.69  
% 3.92/1.69  %Background operators:
% 3.92/1.69  
% 3.92/1.69  
% 3.92/1.69  %Foreground operators:
% 3.92/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.92/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.92/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.92/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.92/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.92/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.92/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.92/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.92/1.69  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.92/1.69  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.92/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.92/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.92/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.69  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.92/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.92/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.92/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.92/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.92/1.69  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.92/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.92/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/1.69  
% 3.92/1.70  tff(f_71, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.92/1.70  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 3.92/1.70  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.92/1.70  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.92/1.70  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.92/1.70  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.92/1.70  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.92/1.70  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.92/1.70  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.92/1.70  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.92/1.70  tff(f_84, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.92/1.70  tff(c_42, plain, (![A_29]: (k2_subset_1(A_29)=A_29)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.92/1.70  tff(c_50, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!=k2_subset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.92/1.70  tff(c_53, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_50])).
% 3.92/1.70  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.92/1.70  tff(c_46, plain, (![A_32]: (~v1_xboole_0(k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.92/1.70  tff(c_210, plain, (![B_69, A_70]: (r2_hidden(B_69, A_70) | ~m1_subset_1(B_69, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.92/1.70  tff(c_20, plain, (![C_24, A_20]: (r1_tarski(C_24, A_20) | ~r2_hidden(C_24, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.92/1.70  tff(c_217, plain, (![B_69, A_20]: (r1_tarski(B_69, A_20) | ~m1_subset_1(B_69, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_210, c_20])).
% 3.92/1.70  tff(c_226, plain, (![B_71, A_72]: (r1_tarski(B_71, A_72) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)))), inference(negUnitSimplification, [status(thm)], [c_46, c_217])).
% 3.92/1.70  tff(c_246, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_226])).
% 3.92/1.70  tff(c_10, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.92/1.70  tff(c_250, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_246, c_10])).
% 3.92/1.70  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.92/1.70  tff(c_260, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_250, c_2])).
% 3.92/1.70  tff(c_346, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=k3_subset_1(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.92/1.70  tff(c_366, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_346])).
% 3.92/1.70  tff(c_14, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, B_14), k4_xboole_0(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.92/1.70  tff(c_372, plain, (k2_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_366, c_14])).
% 3.92/1.70  tff(c_378, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_260, c_372])).
% 3.92/1.70  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.92/1.70  tff(c_375, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_366, c_12])).
% 3.92/1.70  tff(c_22, plain, (![C_24, A_20]: (r2_hidden(C_24, k1_zfmisc_1(A_20)) | ~r1_tarski(C_24, A_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.92/1.70  tff(c_159, plain, (![B_60, A_61]: (m1_subset_1(B_60, A_61) | ~r2_hidden(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.92/1.70  tff(c_162, plain, (![C_24, A_20]: (m1_subset_1(C_24, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)) | ~r1_tarski(C_24, A_20))), inference(resolution, [status(thm)], [c_22, c_159])).
% 3.92/1.70  tff(c_168, plain, (![C_24, A_20]: (m1_subset_1(C_24, k1_zfmisc_1(A_20)) | ~r1_tarski(C_24, A_20))), inference(negUnitSimplification, [status(thm)], [c_46, c_162])).
% 3.92/1.70  tff(c_925, plain, (![A_113, B_114, C_115]: (k4_subset_1(A_113, B_114, C_115)=k2_xboole_0(B_114, C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(A_113)) | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.92/1.70  tff(c_1766, plain, (![A_158, B_159, C_160]: (k4_subset_1(A_158, B_159, C_160)=k2_xboole_0(B_159, C_160) | ~m1_subset_1(B_159, k1_zfmisc_1(A_158)) | ~r1_tarski(C_160, A_158))), inference(resolution, [status(thm)], [c_168, c_925])).
% 3.92/1.70  tff(c_1789, plain, (![C_161]: (k4_subset_1('#skF_4', '#skF_5', C_161)=k2_xboole_0('#skF_5', C_161) | ~r1_tarski(C_161, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_1766])).
% 3.92/1.70  tff(c_1845, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_375, c_1789])).
% 3.92/1.70  tff(c_1871, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_378, c_1845])).
% 3.92/1.70  tff(c_1873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1871])).
% 3.92/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.70  
% 3.92/1.70  Inference rules
% 3.92/1.70  ----------------------
% 3.92/1.70  #Ref     : 0
% 3.92/1.70  #Sup     : 443
% 3.92/1.70  #Fact    : 0
% 3.92/1.70  #Define  : 0
% 3.92/1.70  #Split   : 0
% 3.92/1.70  #Chain   : 0
% 3.92/1.70  #Close   : 0
% 3.92/1.70  
% 3.92/1.70  Ordering : KBO
% 3.92/1.70  
% 3.92/1.70  Simplification rules
% 3.92/1.70  ----------------------
% 3.92/1.70  #Subsume      : 12
% 3.92/1.70  #Demod        : 198
% 3.92/1.70  #Tautology    : 214
% 3.92/1.70  #SimpNegUnit  : 17
% 3.92/1.70  #BackRed      : 4
% 3.92/1.70  
% 3.92/1.70  #Partial instantiations: 0
% 3.92/1.70  #Strategies tried      : 1
% 3.92/1.70  
% 3.92/1.70  Timing (in seconds)
% 3.92/1.70  ----------------------
% 3.92/1.70  Preprocessing        : 0.33
% 3.92/1.70  Parsing              : 0.17
% 3.92/1.70  CNF conversion       : 0.02
% 3.92/1.70  Main loop            : 0.59
% 3.92/1.70  Inferencing          : 0.21
% 3.92/1.70  Reduction            : 0.21
% 3.92/1.70  Demodulation         : 0.16
% 3.92/1.70  BG Simplification    : 0.03
% 3.92/1.70  Subsumption          : 0.09
% 3.92/1.70  Abstraction          : 0.04
% 3.92/1.70  MUC search           : 0.00
% 3.92/1.70  Cooper               : 0.00
% 3.92/1.70  Total                : 0.96
% 3.92/1.70  Index Insertion      : 0.00
% 3.92/1.70  Index Deletion       : 0.00
% 3.92/1.70  Index Matching       : 0.00
% 3.92/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
