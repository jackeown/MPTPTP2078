%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:46 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  58 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

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

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_19] : m1_subset_1(k2_subset_1(A_19),k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ! [A_19] : m1_subset_1(A_19,k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_234,plain,(
    ! [A_58,B_59,C_60] :
      ( k4_subset_1(A_58,B_59,C_60) = k2_xboole_0(B_59,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_282,plain,(
    ! [A_63,B_64] :
      ( k4_subset_1(A_63,B_64,A_63) = k2_xboole_0(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_30,c_234])).

tff(c_290,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_282])).

tff(c_26,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_29,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_26])).

tff(c_292,plain,(
    k2_xboole_0('#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_29])).

tff(c_145,plain,(
    ! [A_49,B_50] :
      ( k3_subset_1(A_49,k3_subset_1(A_49,B_50)) = B_50
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_153,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_145])).

tff(c_126,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k3_subset_1(A_46,B_47),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k3_subset_1(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_310,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,k3_subset_1(A_66,B_67)) = k3_subset_1(A_66,k3_subset_1(A_66,B_67))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(resolution,[status(thm)],[c_126,c_16])).

tff(c_314,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_310])).

tff(c_319,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_314])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_42])).

tff(c_325,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_46])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:58:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.67  
% 2.66/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.67  %$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.66/1.67  
% 2.66/1.67  %Foreground sorts:
% 2.66/1.67  
% 2.66/1.67  
% 2.66/1.67  %Background operators:
% 2.66/1.67  
% 2.66/1.67  
% 2.66/1.67  %Foreground operators:
% 2.66/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.66/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.67  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.66/1.67  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.66/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.67  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.67  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.66/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.67  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.66/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.67  
% 2.66/1.69  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.66/1.69  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.66/1.69  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.66/1.69  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.66/1.69  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.66/1.69  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.66/1.69  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.66/1.69  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.66/1.69  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.66/1.69  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.66/1.69  tff(c_14, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.66/1.69  tff(c_18, plain, (![A_19]: (m1_subset_1(k2_subset_1(A_19), k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.66/1.69  tff(c_30, plain, (![A_19]: (m1_subset_1(A_19, k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 2.66/1.69  tff(c_234, plain, (![A_58, B_59, C_60]: (k4_subset_1(A_58, B_59, C_60)=k2_xboole_0(B_59, C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.69  tff(c_282, plain, (![A_63, B_64]: (k4_subset_1(A_63, B_64, A_63)=k2_xboole_0(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(resolution, [status(thm)], [c_30, c_234])).
% 2.66/1.69  tff(c_290, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_282])).
% 2.66/1.69  tff(c_26, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.66/1.69  tff(c_29, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_26])).
% 2.66/1.69  tff(c_292, plain, (k2_xboole_0('#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_290, c_29])).
% 2.66/1.69  tff(c_145, plain, (![A_49, B_50]: (k3_subset_1(A_49, k3_subset_1(A_49, B_50))=B_50 | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.69  tff(c_153, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_28, c_145])).
% 2.66/1.69  tff(c_126, plain, (![A_46, B_47]: (m1_subset_1(k3_subset_1(A_46, B_47), k1_zfmisc_1(A_46)) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.66/1.69  tff(c_16, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k3_subset_1(A_17, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.66/1.69  tff(c_310, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k3_subset_1(A_66, B_67))=k3_subset_1(A_66, k3_subset_1(A_66, B_67)) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(resolution, [status(thm)], [c_126, c_16])).
% 2.66/1.69  tff(c_314, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_310])).
% 2.66/1.69  tff(c_319, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_314])).
% 2.66/1.69  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.69  tff(c_42, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.69  tff(c_46, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_42])).
% 2.66/1.69  tff(c_325, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_319, c_46])).
% 2.66/1.69  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_292, c_325])).
% 2.66/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.69  
% 2.66/1.69  Inference rules
% 2.66/1.69  ----------------------
% 2.66/1.69  #Ref     : 0
% 2.66/1.69  #Sup     : 79
% 2.66/1.69  #Fact    : 0
% 2.66/1.69  #Define  : 0
% 2.66/1.69  #Split   : 0
% 2.66/1.69  #Chain   : 0
% 2.66/1.69  #Close   : 0
% 2.66/1.69  
% 2.66/1.69  Ordering : KBO
% 2.66/1.69  
% 2.66/1.69  Simplification rules
% 2.66/1.69  ----------------------
% 2.66/1.69  #Subsume      : 1
% 2.66/1.69  #Demod        : 16
% 2.66/1.69  #Tautology    : 49
% 2.66/1.69  #SimpNegUnit  : 1
% 2.66/1.69  #BackRed      : 1
% 2.66/1.69  
% 2.66/1.69  #Partial instantiations: 0
% 2.66/1.69  #Strategies tried      : 1
% 2.66/1.69  
% 2.66/1.69  Timing (in seconds)
% 2.66/1.69  ----------------------
% 2.66/1.70  Preprocessing        : 0.49
% 2.66/1.70  Parsing              : 0.26
% 2.66/1.70  CNF conversion       : 0.03
% 2.66/1.70  Main loop            : 0.35
% 2.66/1.70  Inferencing          : 0.14
% 2.66/1.70  Reduction            : 0.11
% 2.66/1.70  Demodulation         : 0.08
% 2.66/1.70  BG Simplification    : 0.02
% 2.66/1.70  Subsumption          : 0.06
% 2.66/1.70  Abstraction          : 0.02
% 2.66/1.70  MUC search           : 0.00
% 2.66/1.70  Cooper               : 0.00
% 2.66/1.70  Total                : 0.89
% 2.66/1.70  Index Insertion      : 0.00
% 2.66/1.70  Index Deletion       : 0.00
% 2.66/1.70  Index Matching       : 0.00
% 2.66/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
