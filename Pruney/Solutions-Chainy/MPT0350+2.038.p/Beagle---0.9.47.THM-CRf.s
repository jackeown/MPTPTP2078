%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:30 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   57 (  73 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  82 expanded)
%              Number of equality atoms :   34 (  44 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_18,plain,(
    ! [A_18] : k2_subset_1(A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_31,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_28])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_155,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k3_subset_1(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_159,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_155])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_166,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_10])).

tff(c_147,plain,(
    ! [A_46,B_47] :
      ( k3_subset_1(A_46,k3_subset_1(A_46,B_47)) = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_150,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_147])).

tff(c_171,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k3_subset_1(A_50,B_51),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k3_subset_1(A_19,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_654,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,k3_subset_1(A_74,B_75)) = k3_subset_1(A_74,k3_subset_1(A_74,B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(resolution,[status(thm)],[c_171,c_20])).

tff(c_658,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_654])).

tff(c_661,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_150,c_658])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_699,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_163,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_8])).

tff(c_169,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_163])).

tff(c_711,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_169])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k3_subset_1(A_21,B_22),k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_304,plain,(
    ! [A_58,B_59,C_60] :
      ( k4_subset_1(A_58,B_59,C_60) = k2_xboole_0(B_59,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_838,plain,(
    ! [A_76,B_77,B_78] :
      ( k4_subset_1(A_76,B_77,k3_subset_1(A_76,B_78)) = k2_xboole_0(B_77,k3_subset_1(A_76,B_78))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_76)) ) ),
    inference(resolution,[status(thm)],[c_22,c_304])).

tff(c_915,plain,(
    ! [B_79] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_79)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_79))
      | ~ m1_subset_1(B_79,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30,c_838])).

tff(c_922,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_915])).

tff(c_925,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_922])).

tff(c_927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_925])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:16:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.49  
% 2.93/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.49  %$ m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.93/1.49  
% 2.93/1.49  %Foreground sorts:
% 2.93/1.49  
% 2.93/1.49  
% 2.93/1.49  %Background operators:
% 2.93/1.49  
% 2.93/1.49  
% 2.93/1.49  %Foreground operators:
% 2.93/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.93/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.93/1.49  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.93/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.93/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.93/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.93/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.93/1.49  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.93/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.49  
% 2.93/1.50  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.93/1.50  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.93/1.50  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.93/1.50  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.93/1.50  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.93/1.50  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.93/1.50  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.93/1.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.93/1.50  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.93/1.50  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.93/1.50  tff(c_18, plain, (![A_18]: (k2_subset_1(A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.93/1.50  tff(c_28, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.93/1.50  tff(c_31, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_28])).
% 2.93/1.50  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.93/1.50  tff(c_155, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=k3_subset_1(A_48, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.93/1.50  tff(c_159, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_155])).
% 2.93/1.50  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.50  tff(c_166, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_159, c_10])).
% 2.93/1.50  tff(c_147, plain, (![A_46, B_47]: (k3_subset_1(A_46, k3_subset_1(A_46, B_47))=B_47 | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.93/1.50  tff(c_150, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_30, c_147])).
% 2.93/1.50  tff(c_171, plain, (![A_50, B_51]: (m1_subset_1(k3_subset_1(A_50, B_51), k1_zfmisc_1(A_50)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.93/1.50  tff(c_20, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k3_subset_1(A_19, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.93/1.50  tff(c_654, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k3_subset_1(A_74, B_75))=k3_subset_1(A_74, k3_subset_1(A_74, B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(resolution, [status(thm)], [c_171, c_20])).
% 2.93/1.50  tff(c_658, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_654])).
% 2.93/1.50  tff(c_661, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_150, c_658])).
% 2.93/1.50  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.50  tff(c_699, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_661, c_6])).
% 2.93/1.50  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.93/1.50  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.93/1.50  tff(c_163, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_159, c_8])).
% 2.93/1.50  tff(c_169, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_163])).
% 2.93/1.50  tff(c_711, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_699, c_169])).
% 2.93/1.50  tff(c_22, plain, (![A_21, B_22]: (m1_subset_1(k3_subset_1(A_21, B_22), k1_zfmisc_1(A_21)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.93/1.50  tff(c_304, plain, (![A_58, B_59, C_60]: (k4_subset_1(A_58, B_59, C_60)=k2_xboole_0(B_59, C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.93/1.50  tff(c_838, plain, (![A_76, B_77, B_78]: (k4_subset_1(A_76, B_77, k3_subset_1(A_76, B_78))=k2_xboole_0(B_77, k3_subset_1(A_76, B_78)) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)) | ~m1_subset_1(B_78, k1_zfmisc_1(A_76)))), inference(resolution, [status(thm)], [c_22, c_304])).
% 2.93/1.50  tff(c_915, plain, (![B_79]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_79))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_79)) | ~m1_subset_1(B_79, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_838])).
% 2.93/1.50  tff(c_922, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_915])).
% 2.93/1.50  tff(c_925, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_711, c_922])).
% 2.93/1.50  tff(c_927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_925])).
% 2.93/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.50  
% 2.93/1.50  Inference rules
% 2.93/1.50  ----------------------
% 2.93/1.50  #Ref     : 0
% 2.93/1.50  #Sup     : 247
% 2.93/1.50  #Fact    : 0
% 2.93/1.50  #Define  : 0
% 2.93/1.50  #Split   : 0
% 2.93/1.50  #Chain   : 0
% 2.93/1.50  #Close   : 0
% 2.93/1.50  
% 2.93/1.50  Ordering : KBO
% 2.93/1.50  
% 2.93/1.50  Simplification rules
% 2.93/1.50  ----------------------
% 2.93/1.50  #Subsume      : 3
% 2.93/1.50  #Demod        : 184
% 2.93/1.50  #Tautology    : 144
% 2.93/1.50  #SimpNegUnit  : 1
% 2.93/1.50  #BackRed      : 12
% 2.93/1.50  
% 2.93/1.50  #Partial instantiations: 0
% 2.93/1.50  #Strategies tried      : 1
% 2.93/1.50  
% 2.93/1.50  Timing (in seconds)
% 2.93/1.50  ----------------------
% 2.93/1.51  Preprocessing        : 0.30
% 2.93/1.51  Parsing              : 0.17
% 2.93/1.51  CNF conversion       : 0.02
% 2.93/1.51  Main loop            : 0.37
% 2.93/1.51  Inferencing          : 0.12
% 2.93/1.51  Reduction            : 0.15
% 2.93/1.51  Demodulation         : 0.12
% 2.93/1.51  BG Simplification    : 0.02
% 2.93/1.51  Subsumption          : 0.06
% 2.93/1.51  Abstraction          : 0.02
% 2.93/1.51  MUC search           : 0.00
% 2.93/1.51  Cooper               : 0.00
% 2.93/1.51  Total                : 0.70
% 2.93/1.51  Index Insertion      : 0.00
% 2.93/1.51  Index Deletion       : 0.00
% 2.93/1.51  Index Matching       : 0.00
% 2.93/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
