%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:56 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 102 expanded)
%              Number of leaves         :   24 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 172 expanded)
%              Number of equality atoms :   22 (  39 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_205,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,B_67) = k3_subset_1(A_66,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_217,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_205])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_704,plain,(
    ! [A_95] :
      ( r1_xboole_0(A_95,'#skF_3')
      | ~ r1_tarski(A_95,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_10])).

tff(c_742,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_704])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_tarski(A_15,k4_xboole_0(B_16,C_17))
      | ~ r1_xboole_0(A_15,C_17)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_484,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(A_88,B_89) = A_88
      | ~ r1_tarski(A_88,k4_xboole_0(A_88,B_89)) ) ),
    inference(resolution,[status(thm)],[c_14,c_84])).

tff(c_491,plain,(
    ! [B_16,C_17] :
      ( k4_xboole_0(B_16,C_17) = B_16
      | ~ r1_xboole_0(B_16,C_17)
      | ~ r1_tarski(B_16,B_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_484])).

tff(c_504,plain,(
    ! [B_16,C_17] :
      ( k4_xboole_0(B_16,C_17) = B_16
      | ~ r1_xboole_0(B_16,C_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_491])).

tff(c_770,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_742,c_504])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_xboole_0(A_12,k4_xboole_0(C_14,B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_889,plain,(
    ! [A_103] :
      ( r1_xboole_0(A_103,'#skF_2')
      | ~ r1_tarski(A_103,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_18])).

tff(c_1107,plain,(
    ! [A_110] :
      ( k4_xboole_0(A_110,'#skF_2') = A_110
      | ~ r1_tarski(A_110,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_889,c_504])).

tff(c_1142,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_1107])).

tff(c_56,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_xboole_0(A_34,C_35)
      | ~ r1_tarski(A_34,k4_xboole_0(B_36,C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_71,plain,(
    ! [B_36,C_35] : r1_xboole_0(k4_xboole_0(B_36,C_35),C_35) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_1170,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1142,c_71])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_216,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_205])).

tff(c_360,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_tarski(A_78,k4_xboole_0(B_79,C_80))
      | ~ r1_xboole_0(A_78,C_80)
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1558,plain,(
    ! [A_121] :
      ( r1_tarski(A_121,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(A_121,'#skF_2')
      | ~ r1_tarski(A_121,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_360])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1569,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1558,c_28])).

tff(c_1575,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1170,c_1569])).

tff(c_16,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_270,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_16])).

tff(c_316,plain,(
    ! [A_71,B_72] :
      ( k3_subset_1(A_71,k3_subset_1(A_71,B_72)) = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_325,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_316])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k3_subset_1(A_20,B_21),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2225,plain,(
    ! [A_144,B_145] :
      ( k4_xboole_0(A_144,k3_subset_1(A_144,B_145)) = k3_subset_1(A_144,k3_subset_1(A_144,B_145))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_144)) ) ),
    inference(resolution,[status(thm)],[c_24,c_205])).

tff(c_2231,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_2225])).

tff(c_2236,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_325,c_2231])).

tff(c_100,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,(
    ! [A_49,B_50] : r1_tarski(k3_xboole_0(A_49,B_50),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_14])).

tff(c_2298,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2236,c_135])).

tff(c_2308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1575,c_2298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.84  
% 4.35/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.84  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.35/1.84  
% 4.35/1.84  %Foreground sorts:
% 4.35/1.84  
% 4.35/1.84  
% 4.35/1.84  %Background operators:
% 4.35/1.84  
% 4.35/1.84  
% 4.35/1.84  %Foreground operators:
% 4.35/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.35/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.35/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.35/1.84  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.35/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.35/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.35/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.35/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.35/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.35/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.35/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.35/1.84  
% 4.35/1.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.35/1.85  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 4.35/1.85  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.35/1.85  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.35/1.85  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 4.35/1.85  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.35/1.85  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 4.35/1.85  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.35/1.85  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.35/1.85  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.35/1.85  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.35/1.85  tff(c_30, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.35/1.85  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.35/1.85  tff(c_205, plain, (![A_66, B_67]: (k4_xboole_0(A_66, B_67)=k3_subset_1(A_66, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.35/1.85  tff(c_217, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_205])).
% 4.35/1.85  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.35/1.85  tff(c_704, plain, (![A_95]: (r1_xboole_0(A_95, '#skF_3') | ~r1_tarski(A_95, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_217, c_10])).
% 4.35/1.85  tff(c_742, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_704])).
% 4.35/1.85  tff(c_20, plain, (![A_15, B_16, C_17]: (r1_tarski(A_15, k4_xboole_0(B_16, C_17)) | ~r1_xboole_0(A_15, C_17) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.35/1.85  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.35/1.85  tff(c_84, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.35/1.85  tff(c_484, plain, (![A_88, B_89]: (k4_xboole_0(A_88, B_89)=A_88 | ~r1_tarski(A_88, k4_xboole_0(A_88, B_89)))), inference(resolution, [status(thm)], [c_14, c_84])).
% 4.35/1.85  tff(c_491, plain, (![B_16, C_17]: (k4_xboole_0(B_16, C_17)=B_16 | ~r1_xboole_0(B_16, C_17) | ~r1_tarski(B_16, B_16))), inference(resolution, [status(thm)], [c_20, c_484])).
% 4.35/1.85  tff(c_504, plain, (![B_16, C_17]: (k4_xboole_0(B_16, C_17)=B_16 | ~r1_xboole_0(B_16, C_17))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_491])).
% 4.35/1.85  tff(c_770, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_742, c_504])).
% 4.35/1.85  tff(c_18, plain, (![A_12, C_14, B_13]: (r1_xboole_0(A_12, k4_xboole_0(C_14, B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.35/1.85  tff(c_889, plain, (![A_103]: (r1_xboole_0(A_103, '#skF_2') | ~r1_tarski(A_103, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_770, c_18])).
% 4.35/1.85  tff(c_1107, plain, (![A_110]: (k4_xboole_0(A_110, '#skF_2')=A_110 | ~r1_tarski(A_110, '#skF_3'))), inference(resolution, [status(thm)], [c_889, c_504])).
% 4.35/1.85  tff(c_1142, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_6, c_1107])).
% 4.35/1.85  tff(c_56, plain, (![A_34, C_35, B_36]: (r1_xboole_0(A_34, C_35) | ~r1_tarski(A_34, k4_xboole_0(B_36, C_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.35/1.85  tff(c_71, plain, (![B_36, C_35]: (r1_xboole_0(k4_xboole_0(B_36, C_35), C_35))), inference(resolution, [status(thm)], [c_6, c_56])).
% 4.35/1.85  tff(c_1170, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1142, c_71])).
% 4.35/1.85  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.35/1.85  tff(c_216, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_205])).
% 4.35/1.85  tff(c_360, plain, (![A_78, B_79, C_80]: (r1_tarski(A_78, k4_xboole_0(B_79, C_80)) | ~r1_xboole_0(A_78, C_80) | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.35/1.85  tff(c_1558, plain, (![A_121]: (r1_tarski(A_121, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0(A_121, '#skF_2') | ~r1_tarski(A_121, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_216, c_360])).
% 4.35/1.85  tff(c_28, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.35/1.85  tff(c_1569, plain, (~r1_xboole_0('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1558, c_28])).
% 4.35/1.85  tff(c_1575, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1170, c_1569])).
% 4.35/1.85  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.35/1.85  tff(c_270, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_217, c_16])).
% 4.35/1.85  tff(c_316, plain, (![A_71, B_72]: (k3_subset_1(A_71, k3_subset_1(A_71, B_72))=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.35/1.85  tff(c_325, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_32, c_316])).
% 4.35/1.85  tff(c_24, plain, (![A_20, B_21]: (m1_subset_1(k3_subset_1(A_20, B_21), k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.35/1.85  tff(c_2225, plain, (![A_144, B_145]: (k4_xboole_0(A_144, k3_subset_1(A_144, B_145))=k3_subset_1(A_144, k3_subset_1(A_144, B_145)) | ~m1_subset_1(B_145, k1_zfmisc_1(A_144)))), inference(resolution, [status(thm)], [c_24, c_205])).
% 4.35/1.85  tff(c_2231, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_2225])).
% 4.35/1.85  tff(c_2236, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_270, c_325, c_2231])).
% 4.35/1.85  tff(c_100, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.35/1.85  tff(c_135, plain, (![A_49, B_50]: (r1_tarski(k3_xboole_0(A_49, B_50), A_49))), inference(superposition, [status(thm), theory('equality')], [c_100, c_14])).
% 4.35/1.85  tff(c_2298, plain, (r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2236, c_135])).
% 4.35/1.85  tff(c_2308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1575, c_2298])).
% 4.35/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.85  
% 4.35/1.85  Inference rules
% 4.35/1.85  ----------------------
% 4.35/1.85  #Ref     : 0
% 4.35/1.85  #Sup     : 580
% 4.35/1.85  #Fact    : 0
% 4.35/1.85  #Define  : 0
% 4.35/1.85  #Split   : 2
% 4.35/1.85  #Chain   : 0
% 4.35/1.85  #Close   : 0
% 4.35/1.85  
% 4.35/1.85  Ordering : KBO
% 4.35/1.85  
% 4.35/1.85  Simplification rules
% 4.35/1.85  ----------------------
% 4.35/1.85  #Subsume      : 22
% 4.35/1.85  #Demod        : 251
% 4.35/1.85  #Tautology    : 253
% 4.35/1.85  #SimpNegUnit  : 1
% 4.35/1.85  #BackRed      : 7
% 4.35/1.85  
% 4.35/1.85  #Partial instantiations: 0
% 4.35/1.85  #Strategies tried      : 1
% 4.35/1.85  
% 4.35/1.85  Timing (in seconds)
% 4.35/1.85  ----------------------
% 4.35/1.86  Preprocessing        : 0.34
% 4.35/1.86  Parsing              : 0.18
% 4.35/1.86  CNF conversion       : 0.02
% 4.35/1.86  Main loop            : 0.67
% 4.35/1.86  Inferencing          : 0.22
% 4.35/1.86  Reduction            : 0.24
% 4.35/1.86  Demodulation         : 0.18
% 4.35/1.86  BG Simplification    : 0.03
% 4.35/1.86  Subsumption          : 0.13
% 4.35/1.86  Abstraction          : 0.03
% 4.35/1.86  MUC search           : 0.00
% 4.35/1.86  Cooper               : 0.00
% 4.35/1.86  Total                : 1.04
% 4.35/1.86  Index Insertion      : 0.00
% 4.35/1.86  Index Deletion       : 0.00
% 4.35/1.86  Index Matching       : 0.00
% 4.35/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
