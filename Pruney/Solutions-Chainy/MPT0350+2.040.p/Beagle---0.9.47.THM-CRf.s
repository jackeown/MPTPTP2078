%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:31 EST 2020

% Result     : Theorem 6.08s
% Output     : CNFRefutation 6.23s
% Verified   : 
% Statistics : Number of formulae       :   60 (  77 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  83 expanded)
%              Number of equality atoms :   38 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_22,plain,(
    ! [A_23] : k2_subset_1(A_23) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_35,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_32])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1007,plain,(
    ! [A_73,B_74] :
      ( k3_subset_1(A_73,k3_subset_1(A_73,B_74)) = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1013,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_1007])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k3_subset_1(A_26,B_27),k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1272,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = k3_subset_1(A_80,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6253,plain,(
    ! [A_145,B_146] :
      ( k4_xboole_0(A_145,k3_subset_1(A_145,B_146)) = k3_subset_1(A_145,k3_subset_1(A_145,B_146))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1272])).

tff(c_6257,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_6253])).

tff(c_6260,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1013,c_6257])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_110,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k2_xboole_0(A_38,B_39)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_117,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_110])).

tff(c_793,plain,(
    ! [A_67,B_68,C_69] : k4_xboole_0(k4_xboole_0(A_67,B_68),C_69) = k4_xboole_0(A_67,k2_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2924,plain,(
    ! [C_111,A_112,B_113] : k2_xboole_0(C_111,k4_xboole_0(A_112,k2_xboole_0(B_113,C_111))) = k2_xboole_0(C_111,k4_xboole_0(A_112,B_113)) ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_6])).

tff(c_3084,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_2924])).

tff(c_3152,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_3084])).

tff(c_6276,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6260,c_3152])).

tff(c_1280,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1272])).

tff(c_1290,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1280,c_6])).

tff(c_1294,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1290])).

tff(c_6290,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6276,c_1294])).

tff(c_2249,plain,(
    ! [A_99,B_100,C_101] :
      ( k4_subset_1(A_99,B_100,C_101) = k2_xboole_0(B_100,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(A_99))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7336,plain,(
    ! [A_151,B_152,B_153] :
      ( k4_subset_1(A_151,B_152,k3_subset_1(A_151,B_153)) = k2_xboole_0(B_152,k3_subset_1(A_151,B_153))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_151))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_151)) ) ),
    inference(resolution,[status(thm)],[c_26,c_2249])).

tff(c_7346,plain,(
    ! [B_154] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_154)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_154))
      | ~ m1_subset_1(B_154,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_34,c_7336])).

tff(c_7353,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_7346])).

tff(c_7356,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6290,c_7353])).

tff(c_7358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_7356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:38:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.08/2.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.08/2.60  
% 6.08/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.08/2.60  %$ m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.08/2.60  
% 6.08/2.60  %Foreground sorts:
% 6.08/2.60  
% 6.08/2.60  
% 6.08/2.60  %Background operators:
% 6.08/2.60  
% 6.08/2.60  
% 6.08/2.60  %Foreground operators:
% 6.08/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.08/2.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.08/2.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.08/2.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.08/2.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.08/2.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.08/2.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.08/2.60  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.08/2.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.08/2.60  tff('#skF_2', type, '#skF_2': $i).
% 6.08/2.60  tff('#skF_1', type, '#skF_1': $i).
% 6.08/2.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.08/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.08/2.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.08/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.08/2.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.08/2.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.08/2.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.08/2.60  
% 6.23/2.61  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.23/2.61  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 6.23/2.61  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.23/2.61  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.23/2.61  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.23/2.61  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.23/2.61  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.23/2.61  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.23/2.61  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.23/2.61  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.23/2.61  tff(f_65, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.23/2.61  tff(c_22, plain, (![A_23]: (k2_subset_1(A_23)=A_23)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.23/2.61  tff(c_32, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.23/2.61  tff(c_35, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_32])).
% 6.23/2.61  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.23/2.61  tff(c_1007, plain, (![A_73, B_74]: (k3_subset_1(A_73, k3_subset_1(A_73, B_74))=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.23/2.61  tff(c_1013, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_34, c_1007])).
% 6.23/2.61  tff(c_26, plain, (![A_26, B_27]: (m1_subset_1(k3_subset_1(A_26, B_27), k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.23/2.61  tff(c_1272, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=k3_subset_1(A_80, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.23/2.61  tff(c_6253, plain, (![A_145, B_146]: (k4_xboole_0(A_145, k3_subset_1(A_145, B_146))=k3_subset_1(A_145, k3_subset_1(A_145, B_146)) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)))), inference(resolution, [status(thm)], [c_26, c_1272])).
% 6.23/2.61  tff(c_6257, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_6253])).
% 6.23/2.61  tff(c_6260, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1013, c_6257])).
% 6.23/2.61  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.23/2.61  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.23/2.61  tff(c_110, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k2_xboole_0(A_38, B_39))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.23/2.61  tff(c_117, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_110])).
% 6.23/2.61  tff(c_793, plain, (![A_67, B_68, C_69]: (k4_xboole_0(k4_xboole_0(A_67, B_68), C_69)=k4_xboole_0(A_67, k2_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.23/2.61  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.23/2.61  tff(c_2924, plain, (![C_111, A_112, B_113]: (k2_xboole_0(C_111, k4_xboole_0(A_112, k2_xboole_0(B_113, C_111)))=k2_xboole_0(C_111, k4_xboole_0(A_112, B_113)))), inference(superposition, [status(thm), theory('equality')], [c_793, c_6])).
% 6.23/2.61  tff(c_3084, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k2_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_117, c_2924])).
% 6.23/2.61  tff(c_3152, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_2))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_3084])).
% 6.23/2.61  tff(c_6276, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6260, c_3152])).
% 6.23/2.61  tff(c_1280, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_1272])).
% 6.23/2.61  tff(c_1290, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1280, c_6])).
% 6.23/2.61  tff(c_1294, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1290])).
% 6.23/2.61  tff(c_6290, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6276, c_1294])).
% 6.23/2.61  tff(c_2249, plain, (![A_99, B_100, C_101]: (k4_subset_1(A_99, B_100, C_101)=k2_xboole_0(B_100, C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(A_99)) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.23/2.61  tff(c_7336, plain, (![A_151, B_152, B_153]: (k4_subset_1(A_151, B_152, k3_subset_1(A_151, B_153))=k2_xboole_0(B_152, k3_subset_1(A_151, B_153)) | ~m1_subset_1(B_152, k1_zfmisc_1(A_151)) | ~m1_subset_1(B_153, k1_zfmisc_1(A_151)))), inference(resolution, [status(thm)], [c_26, c_2249])).
% 6.23/2.61  tff(c_7346, plain, (![B_154]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_154))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_154)) | ~m1_subset_1(B_154, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_7336])).
% 6.23/2.61  tff(c_7353, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_7346])).
% 6.23/2.61  tff(c_7356, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6290, c_7353])).
% 6.23/2.61  tff(c_7358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_7356])).
% 6.23/2.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.23/2.61  
% 6.23/2.61  Inference rules
% 6.23/2.61  ----------------------
% 6.23/2.61  #Ref     : 0
% 6.23/2.61  #Sup     : 1820
% 6.23/2.61  #Fact    : 0
% 6.23/2.61  #Define  : 0
% 6.23/2.61  #Split   : 0
% 6.23/2.61  #Chain   : 0
% 6.23/2.61  #Close   : 0
% 6.23/2.61  
% 6.23/2.61  Ordering : KBO
% 6.23/2.61  
% 6.23/2.61  Simplification rules
% 6.23/2.61  ----------------------
% 6.23/2.61  #Subsume      : 20
% 6.23/2.61  #Demod        : 1904
% 6.23/2.61  #Tautology    : 1375
% 6.23/2.61  #SimpNegUnit  : 1
% 6.23/2.61  #BackRed      : 1
% 6.23/2.61  
% 6.23/2.61  #Partial instantiations: 0
% 6.23/2.61  #Strategies tried      : 1
% 6.23/2.61  
% 6.23/2.61  Timing (in seconds)
% 6.23/2.61  ----------------------
% 6.23/2.62  Preprocessing        : 0.47
% 6.23/2.62  Parsing              : 0.25
% 6.23/2.62  CNF conversion       : 0.03
% 6.23/2.62  Main loop            : 1.25
% 6.23/2.62  Inferencing          : 0.35
% 6.23/2.62  Reduction            : 0.62
% 6.23/2.62  Demodulation         : 0.54
% 6.23/2.62  BG Simplification    : 0.04
% 6.23/2.62  Subsumption          : 0.17
% 6.23/2.62  Abstraction          : 0.06
% 6.23/2.62  MUC search           : 0.00
% 6.23/2.62  Cooper               : 0.00
% 6.23/2.62  Total                : 1.76
% 6.23/2.62  Index Insertion      : 0.00
% 6.23/2.62  Index Deletion       : 0.00
% 6.23/2.62  Index Matching       : 0.00
% 6.23/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
