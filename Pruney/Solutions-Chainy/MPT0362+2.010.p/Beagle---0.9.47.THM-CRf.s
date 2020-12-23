%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:33 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   45 (  54 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  73 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k4_xboole_0(A,D),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).

tff(c_38,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [A_25,B_26] : r1_tarski(k3_xboole_0(A_25,B_26),A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_146,plain,(
    ! [A_38,B_39,C_40] :
      ( k9_subset_1(A_38,B_39,C_40) = k3_xboole_0(B_39,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_157,plain,(
    ! [B_41] : k9_subset_1('#skF_1',B_41,'#skF_3') = k3_xboole_0(B_41,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_146])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k9_subset_1(A_13,B_14,C_15),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_163,plain,(
    ! [B_41] :
      ( m1_subset_1(k3_xboole_0(B_41,'#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_16])).

tff(c_171,plain,(
    ! [B_42] : m1_subset_1(k3_xboole_0(B_42,'#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_163])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_178,plain,(
    ! [B_42] : k4_xboole_0('#skF_1',k3_xboole_0(B_42,'#skF_3')) = k3_subset_1('#skF_1',k3_xboole_0(B_42,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_171,c_14])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_66,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k3_subset_1(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_66])).

tff(c_275,plain,(
    ! [A_48,D_49,B_50,C_51] :
      ( r1_tarski(k4_xboole_0(A_48,D_49),k4_xboole_0(B_50,C_51))
      | ~ r1_tarski(C_51,D_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_896,plain,(
    ! [B_82,C_83] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),k4_xboole_0(B_82,C_83))
      | ~ r1_tarski(C_83,'#skF_2')
      | ~ r1_tarski('#skF_1',B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_275])).

tff(c_914,plain,(
    ! [B_42] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0(B_42,'#skF_3')))
      | ~ r1_tarski(k3_xboole_0(B_42,'#skF_3'),'#skF_2')
      | ~ r1_tarski('#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_896])).

tff(c_2055,plain,(
    ! [B_129] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0(B_129,'#skF_3')))
      | ~ r1_tarski(k3_xboole_0(B_129,'#skF_3'),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_914])).

tff(c_154,plain,(
    ! [B_39] : k9_subset_1('#skF_1',B_39,'#skF_3') = k3_xboole_0(B_39,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_146])).

tff(c_20,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k9_subset_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_156,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_20])).

tff(c_2058,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2055,c_156])).

tff(c_2064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_2058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.75  
% 4.01/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.75  %$ r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.01/1.75  
% 4.01/1.75  %Foreground sorts:
% 4.01/1.75  
% 4.01/1.75  
% 4.01/1.75  %Background operators:
% 4.01/1.75  
% 4.01/1.75  
% 4.01/1.75  %Foreground operators:
% 4.01/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.01/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.75  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.01/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.75  tff('#skF_1', type, '#skF_1': $i).
% 4.01/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.01/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.01/1.75  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.01/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.75  
% 4.01/1.77  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.01/1.77  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.01/1.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.01/1.77  tff(f_61, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 4.01/1.77  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.01/1.77  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 4.01/1.77  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.01/1.77  tff(f_37, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k4_xboole_0(A, D), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_xboole_1)).
% 4.01/1.77  tff(c_38, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.01/1.77  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.01/1.77  tff(c_47, plain, (![A_25, B_26]: (r1_tarski(k3_xboole_0(A_25, B_26), A_25))), inference(superposition, [status(thm), theory('equality')], [c_38, c_10])).
% 4.01/1.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.01/1.77  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.01/1.77  tff(c_146, plain, (![A_38, B_39, C_40]: (k9_subset_1(A_38, B_39, C_40)=k3_xboole_0(B_39, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.01/1.77  tff(c_157, plain, (![B_41]: (k9_subset_1('#skF_1', B_41, '#skF_3')=k3_xboole_0(B_41, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_146])).
% 4.01/1.77  tff(c_16, plain, (![A_13, B_14, C_15]: (m1_subset_1(k9_subset_1(A_13, B_14, C_15), k1_zfmisc_1(A_13)) | ~m1_subset_1(C_15, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.01/1.77  tff(c_163, plain, (![B_41]: (m1_subset_1(k3_xboole_0(B_41, '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_157, c_16])).
% 4.01/1.77  tff(c_171, plain, (![B_42]: (m1_subset_1(k3_xboole_0(B_42, '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_163])).
% 4.01/1.77  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.01/1.77  tff(c_178, plain, (![B_42]: (k4_xboole_0('#skF_1', k3_xboole_0(B_42, '#skF_3'))=k3_subset_1('#skF_1', k3_xboole_0(B_42, '#skF_3')))), inference(resolution, [status(thm)], [c_171, c_14])).
% 4.01/1.77  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.01/1.77  tff(c_66, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k3_subset_1(A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.01/1.77  tff(c_74, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_66])).
% 4.01/1.77  tff(c_275, plain, (![A_48, D_49, B_50, C_51]: (r1_tarski(k4_xboole_0(A_48, D_49), k4_xboole_0(B_50, C_51)) | ~r1_tarski(C_51, D_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.01/1.77  tff(c_896, plain, (![B_82, C_83]: (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k4_xboole_0(B_82, C_83)) | ~r1_tarski(C_83, '#skF_2') | ~r1_tarski('#skF_1', B_82))), inference(superposition, [status(thm), theory('equality')], [c_74, c_275])).
% 4.01/1.77  tff(c_914, plain, (![B_42]: (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0(B_42, '#skF_3'))) | ~r1_tarski(k3_xboole_0(B_42, '#skF_3'), '#skF_2') | ~r1_tarski('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_896])).
% 4.01/1.77  tff(c_2055, plain, (![B_129]: (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0(B_129, '#skF_3'))) | ~r1_tarski(k3_xboole_0(B_129, '#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_914])).
% 4.01/1.77  tff(c_154, plain, (![B_39]: (k9_subset_1('#skF_1', B_39, '#skF_3')=k3_xboole_0(B_39, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_146])).
% 4.01/1.77  tff(c_20, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k9_subset_1('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.01/1.77  tff(c_156, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_20])).
% 4.01/1.77  tff(c_2058, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2055, c_156])).
% 4.01/1.77  tff(c_2064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_2058])).
% 4.01/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.77  
% 4.01/1.77  Inference rules
% 4.01/1.77  ----------------------
% 4.01/1.77  #Ref     : 0
% 4.01/1.77  #Sup     : 519
% 4.01/1.77  #Fact    : 0
% 4.01/1.77  #Define  : 0
% 4.01/1.77  #Split   : 16
% 4.01/1.77  #Chain   : 0
% 4.01/1.77  #Close   : 0
% 4.01/1.77  
% 4.01/1.77  Ordering : KBO
% 4.01/1.77  
% 4.01/1.77  Simplification rules
% 4.01/1.77  ----------------------
% 4.01/1.77  #Subsume      : 33
% 4.01/1.77  #Demod        : 376
% 4.01/1.77  #Tautology    : 117
% 4.01/1.77  #SimpNegUnit  : 0
% 4.01/1.77  #BackRed      : 4
% 4.01/1.77  
% 4.01/1.77  #Partial instantiations: 0
% 4.01/1.77  #Strategies tried      : 1
% 4.01/1.77  
% 4.01/1.77  Timing (in seconds)
% 4.01/1.77  ----------------------
% 4.01/1.77  Preprocessing        : 0.29
% 4.01/1.77  Parsing              : 0.16
% 4.01/1.77  CNF conversion       : 0.02
% 4.01/1.77  Main loop            : 0.71
% 4.01/1.77  Inferencing          : 0.21
% 4.01/1.77  Reduction            : 0.29
% 4.01/1.77  Demodulation         : 0.22
% 4.01/1.77  BG Simplification    : 0.03
% 4.01/1.77  Subsumption          : 0.14
% 4.01/1.77  Abstraction          : 0.04
% 4.01/1.77  MUC search           : 0.00
% 4.01/1.77  Cooper               : 0.00
% 4.01/1.77  Total                : 1.03
% 4.01/1.77  Index Insertion      : 0.00
% 4.01/1.77  Index Deletion       : 0.00
% 4.01/1.77  Index Matching       : 0.00
% 4.01/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
