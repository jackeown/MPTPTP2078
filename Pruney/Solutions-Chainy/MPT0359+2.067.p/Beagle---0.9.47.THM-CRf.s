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
% DateTime   : Thu Dec  3 09:56:18 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 143 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 206 expanded)
%              Number of equality atoms :   38 ( 105 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_106,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_103])).

tff(c_12,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_86,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_37,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_87,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_37])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_89,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_26])).

tff(c_118,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k3_subset_1(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_subset_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_89,c_118])).

tff(c_127,plain,(
    k3_subset_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_124])).

tff(c_88,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_87,c_86])).

tff(c_128,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_88])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_128])).

tff(c_132,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_10,plain,(
    ! [A_7] : k1_subset_1(A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_subset_1(A_15)) = k2_subset_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_subset_1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_41,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_36])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k3_subset_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_133,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_170,plain,(
    ! [A_39,B_40] :
      ( k3_subset_1(A_39,k3_subset_1(A_39,B_40)) = B_40
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_176,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_170])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( k1_subset_1(A_16) = B_17
      | ~ r1_tarski(B_17,k3_subset_1(A_16,B_17))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_189,plain,(
    ! [B_41,A_42] :
      ( k1_xboole_0 = B_41
      | ~ r1_tarski(B_41,k3_subset_1(A_42,B_41))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24])).

tff(c_192,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_189])).

tff(c_201,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_192])).

tff(c_207,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_210,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_207])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_210])).

tff(c_215,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_217,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_176])).

tff(c_220,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_217])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:13:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.31  
% 1.94/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.31  %$ r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.94/1.31  
% 1.94/1.31  %Foreground sorts:
% 1.94/1.31  
% 1.94/1.31  
% 1.94/1.31  %Background operators:
% 1.94/1.31  
% 1.94/1.31  
% 1.94/1.31  %Foreground operators:
% 1.94/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.94/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.94/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.31  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.94/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.94/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.31  
% 1.94/1.33  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.94/1.33  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.94/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.94/1.33  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.94/1.33  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 1.94/1.33  tff(f_64, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 1.94/1.33  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.94/1.33  tff(f_35, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.94/1.33  tff(f_51, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 1.94/1.33  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.94/1.33  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.94/1.33  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 1.94/1.33  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.33  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.33  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.33  tff(c_94, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.33  tff(c_103, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_94])).
% 1.94/1.33  tff(c_106, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_103])).
% 1.94/1.33  tff(c_12, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.33  tff(c_28, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.33  tff(c_38, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28])).
% 1.94/1.33  tff(c_86, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 1.94/1.33  tff(c_34, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.33  tff(c_37, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 1.94/1.33  tff(c_87, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86, c_37])).
% 1.94/1.33  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.33  tff(c_89, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_26])).
% 1.94/1.33  tff(c_118, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k3_subset_1(A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.33  tff(c_124, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_subset_1('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_89, c_118])).
% 1.94/1.33  tff(c_127, plain, (k3_subset_1('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_106, c_124])).
% 1.94/1.33  tff(c_88, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_87, c_86])).
% 1.94/1.33  tff(c_128, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_88])).
% 1.94/1.33  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_128])).
% 1.94/1.33  tff(c_132, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_38])).
% 1.94/1.33  tff(c_10, plain, (![A_7]: (k1_subset_1(A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.33  tff(c_20, plain, (![A_15]: (k3_subset_1(A_15, k1_subset_1(A_15))=k2_subset_1(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.94/1.33  tff(c_36, plain, (![A_15]: (k3_subset_1(A_15, k1_subset_1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20])).
% 1.94/1.33  tff(c_41, plain, (![A_15]: (k3_subset_1(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_36])).
% 1.94/1.33  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(k3_subset_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.33  tff(c_133, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 1.94/1.33  tff(c_170, plain, (![A_39, B_40]: (k3_subset_1(A_39, k3_subset_1(A_39, B_40))=B_40 | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.94/1.33  tff(c_176, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_170])).
% 1.94/1.33  tff(c_24, plain, (![A_16, B_17]: (k1_subset_1(A_16)=B_17 | ~r1_tarski(B_17, k3_subset_1(A_16, B_17)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.33  tff(c_189, plain, (![B_41, A_42]: (k1_xboole_0=B_41 | ~r1_tarski(B_41, k3_subset_1(A_42, B_41)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_24])).
% 1.94/1.33  tff(c_192, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_189])).
% 1.94/1.33  tff(c_201, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_192])).
% 1.94/1.33  tff(c_207, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_201])).
% 1.94/1.33  tff(c_210, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_207])).
% 1.94/1.33  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_210])).
% 1.94/1.33  tff(c_215, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_201])).
% 1.94/1.33  tff(c_217, plain, (k3_subset_1('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_215, c_176])).
% 1.94/1.33  tff(c_220, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_217])).
% 1.94/1.33  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_220])).
% 1.94/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.33  
% 1.94/1.33  Inference rules
% 1.94/1.33  ----------------------
% 1.94/1.33  #Ref     : 0
% 1.94/1.33  #Sup     : 39
% 1.94/1.33  #Fact    : 0
% 1.94/1.33  #Define  : 0
% 1.94/1.33  #Split   : 2
% 1.94/1.33  #Chain   : 0
% 1.94/1.33  #Close   : 0
% 1.94/1.33  
% 1.94/1.33  Ordering : KBO
% 1.94/1.33  
% 1.94/1.33  Simplification rules
% 1.94/1.33  ----------------------
% 1.94/1.33  #Subsume      : 0
% 1.94/1.33  #Demod        : 27
% 1.94/1.33  #Tautology    : 31
% 1.94/1.33  #SimpNegUnit  : 3
% 1.94/1.33  #BackRed      : 6
% 1.94/1.33  
% 1.94/1.33  #Partial instantiations: 0
% 1.94/1.33  #Strategies tried      : 1
% 1.94/1.33  
% 1.94/1.33  Timing (in seconds)
% 1.94/1.33  ----------------------
% 1.94/1.33  Preprocessing        : 0.30
% 1.94/1.33  Parsing              : 0.16
% 1.94/1.33  CNF conversion       : 0.02
% 1.94/1.33  Main loop            : 0.16
% 1.94/1.33  Inferencing          : 0.05
% 1.94/1.33  Reduction            : 0.06
% 1.94/1.33  Demodulation         : 0.04
% 1.94/1.33  BG Simplification    : 0.01
% 1.94/1.33  Subsumption          : 0.02
% 1.94/1.33  Abstraction          : 0.01
% 1.94/1.33  MUC search           : 0.00
% 1.94/1.33  Cooper               : 0.00
% 1.94/1.33  Total                : 0.50
% 1.94/1.33  Index Insertion      : 0.00
% 1.94/1.33  Index Deletion       : 0.00
% 1.94/1.33  Index Matching       : 0.00
% 1.94/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
