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
% DateTime   : Thu Dec  3 09:58:06 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   46 (  61 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  58 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_52,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,A_24) = k2_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ! [B_23,A_24] : r1_tarski(B_23,k2_xboole_0(A_24,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_171,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_184,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,k2_xboole_0(A_24,B_23)) = k2_xboole_0(A_24,B_23) ),
    inference(resolution,[status(thm)],[c_70,c_171])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_38])).

tff(c_187,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_41,c_171])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_655,plain,(
    ! [A_53,B_54] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A_53),k1_zfmisc_1(B_54)),k1_zfmisc_1(k2_xboole_0(A_53,B_54))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_695,plain,(
    ! [A_5] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A_5),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_655])).

tff(c_709,plain,(
    ! [A_55] : r1_tarski(k2_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_55)),k1_zfmisc_1(A_55)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16,c_695])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1370,plain,(
    ! [A_66] : k2_xboole_0(k2_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_66)),k1_zfmisc_1(A_66)) = k1_zfmisc_1(A_66) ),
    inference(resolution,[status(thm)],[c_709,c_4])).

tff(c_253,plain,(
    ! [A_40,B_41] : k2_xboole_0(A_40,k2_xboole_0(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(resolution,[status(thm)],[c_8,c_171])).

tff(c_291,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_253])).

tff(c_1409,plain,(
    ! [A_66] : k2_xboole_0(k1_zfmisc_1(A_66),k2_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_66))) = k2_xboole_0(k1_zfmisc_1(A_66),k1_zfmisc_1(A_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1370,c_291])).

tff(c_1470,plain,(
    ! [A_67] : k2_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_67)) = k1_zfmisc_1(A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_187,c_1409])).

tff(c_1515,plain,(
    ! [A_67] : r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1470,c_8])).

tff(c_235,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,k1_zfmisc_1(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_246,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_235,c_24])).

tff(c_1539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1515,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.48  
% 3.05/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.48  %$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 3.05/1.48  
% 3.05/1.48  %Foreground sorts:
% 3.05/1.48  
% 3.05/1.48  
% 3.05/1.48  %Background operators:
% 3.05/1.48  
% 3.05/1.48  
% 3.05/1.48  %Foreground operators:
% 3.05/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.05/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.05/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.05/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.05/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.05/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.05/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.48  
% 3.05/1.49  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.05/1.49  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.05/1.49  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.05/1.49  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.05/1.49  tff(f_42, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 3.05/1.49  tff(f_44, axiom, (![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 3.05/1.49  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.05/1.49  tff(f_51, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 3.05/1.49  tff(c_52, plain, (![B_23, A_24]: (k2_xboole_0(B_23, A_24)=k2_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.49  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.49  tff(c_70, plain, (![B_23, A_24]: (r1_tarski(B_23, k2_xboole_0(A_24, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_8])).
% 3.05/1.49  tff(c_171, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.49  tff(c_184, plain, (![B_23, A_24]: (k2_xboole_0(B_23, k2_xboole_0(A_24, B_23))=k2_xboole_0(A_24, B_23))), inference(resolution, [status(thm)], [c_70, c_171])).
% 3.05/1.49  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.49  tff(c_38, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.49  tff(c_41, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_38])).
% 3.05/1.49  tff(c_187, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(resolution, [status(thm)], [c_41, c_171])).
% 3.05/1.49  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.49  tff(c_16, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.05/1.49  tff(c_655, plain, (![A_53, B_54]: (r1_tarski(k2_xboole_0(k1_zfmisc_1(A_53), k1_zfmisc_1(B_54)), k1_zfmisc_1(k2_xboole_0(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.05/1.49  tff(c_695, plain, (![A_5]: (r1_tarski(k2_xboole_0(k1_zfmisc_1(A_5), k1_zfmisc_1(k1_xboole_0)), k1_zfmisc_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_655])).
% 3.05/1.49  tff(c_709, plain, (![A_55]: (r1_tarski(k2_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_55)), k1_zfmisc_1(A_55)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16, c_695])).
% 3.05/1.49  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.49  tff(c_1370, plain, (![A_66]: (k2_xboole_0(k2_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_66)), k1_zfmisc_1(A_66))=k1_zfmisc_1(A_66))), inference(resolution, [status(thm)], [c_709, c_4])).
% 3.05/1.49  tff(c_253, plain, (![A_40, B_41]: (k2_xboole_0(A_40, k2_xboole_0(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(resolution, [status(thm)], [c_8, c_171])).
% 3.05/1.49  tff(c_291, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_253])).
% 3.05/1.49  tff(c_1409, plain, (![A_66]: (k2_xboole_0(k1_zfmisc_1(A_66), k2_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_66)))=k2_xboole_0(k1_zfmisc_1(A_66), k1_zfmisc_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_1370, c_291])).
% 3.05/1.49  tff(c_1470, plain, (![A_67]: (k2_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_67))=k1_zfmisc_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_187, c_1409])).
% 3.05/1.49  tff(c_1515, plain, (![A_67]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_1470, c_8])).
% 3.05/1.49  tff(c_235, plain, (![A_36, B_37]: (m1_subset_1(A_36, k1_zfmisc_1(B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.05/1.49  tff(c_24, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.05/1.49  tff(c_246, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_235, c_24])).
% 3.05/1.49  tff(c_1539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1515, c_246])).
% 3.05/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.49  
% 3.05/1.49  Inference rules
% 3.05/1.49  ----------------------
% 3.05/1.49  #Ref     : 0
% 3.05/1.49  #Sup     : 366
% 3.05/1.49  #Fact    : 0
% 3.05/1.49  #Define  : 0
% 3.05/1.49  #Split   : 0
% 3.05/1.49  #Chain   : 0
% 3.05/1.49  #Close   : 0
% 3.05/1.49  
% 3.05/1.49  Ordering : KBO
% 3.05/1.49  
% 3.05/1.49  Simplification rules
% 3.05/1.49  ----------------------
% 3.05/1.49  #Subsume      : 16
% 3.05/1.49  #Demod        : 470
% 3.05/1.49  #Tautology    : 278
% 3.05/1.49  #SimpNegUnit  : 0
% 3.05/1.49  #BackRed      : 3
% 3.05/1.49  
% 3.05/1.49  #Partial instantiations: 0
% 3.05/1.49  #Strategies tried      : 1
% 3.05/1.49  
% 3.05/1.49  Timing (in seconds)
% 3.05/1.49  ----------------------
% 3.05/1.50  Preprocessing        : 0.28
% 3.05/1.50  Parsing              : 0.15
% 3.05/1.50  CNF conversion       : 0.02
% 3.05/1.50  Main loop            : 0.42
% 3.05/1.50  Inferencing          : 0.14
% 3.05/1.50  Reduction            : 0.20
% 3.05/1.50  Demodulation         : 0.17
% 3.05/1.50  BG Simplification    : 0.02
% 3.05/1.50  Subsumption          : 0.05
% 3.05/1.50  Abstraction          : 0.03
% 3.05/1.50  MUC search           : 0.00
% 3.05/1.50  Cooper               : 0.00
% 3.05/1.50  Total                : 0.73
% 3.05/1.50  Index Insertion      : 0.00
% 3.05/1.50  Index Deletion       : 0.00
% 3.05/1.50  Index Matching       : 0.00
% 3.05/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
