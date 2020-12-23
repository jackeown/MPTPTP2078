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
% DateTime   : Thu Dec  3 09:55:59 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   48 (  58 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  83 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(k3_subset_1(A,B),C)
             => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(C,B)
     => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_16,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_63,plain,(
    ! [A_27,B_28] :
      ( k3_subset_1(A_27,k3_subset_1(A_27,B_28)) = B_28
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_63])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    k3_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_3') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_24])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    ! [A_29,B_30,C_31] :
      ( k9_subset_1(A_29,B_30,C_31) = k3_xboole_0(B_30,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,(
    ! [B_35] : k9_subset_1('#skF_1',B_35,'#skF_3') = k3_xboole_0(B_35,'#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_78])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_subset_1(k9_subset_1(A_10,B_11,C_12),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_102,plain,(
    ! [B_35] :
      ( m1_subset_1(k3_xboole_0(B_35,'#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_10])).

tff(c_110,plain,(
    ! [B_36] : m1_subset_1(k3_xboole_0(B_36,'#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_102])).

tff(c_119,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_110])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k3_subset_1(A_8,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_129,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_119,c_8])).

tff(c_134,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_129])).

tff(c_46,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k3_subset_1(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_199,plain,(
    ! [A_42,B_43,C_44] :
      ( k2_xboole_0(k4_xboole_0(A_42,B_43),k3_xboole_0(A_42,k4_xboole_0(B_43,C_44))) = k4_xboole_0(A_42,C_44)
      | ~ r1_tarski(C_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_238,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_tarski(k4_xboole_0(A_45,B_46),k4_xboole_0(A_45,C_47))
      | ~ r1_tarski(C_47,B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_6])).

tff(c_301,plain,(
    ! [C_50] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k4_xboole_0('#skF_1',C_50))
      | ~ r1_tarski(C_50,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_238])).

tff(c_310,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_301])).

tff(c_319,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_310])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:15:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.23  
% 2.13/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.23  %$ r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.23  
% 2.13/1.23  %Foreground sorts:
% 2.13/1.23  
% 2.13/1.23  
% 2.13/1.23  %Background operators:
% 2.13/1.23  
% 2.13/1.23  
% 2.13/1.23  %Foreground operators:
% 2.13/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.13/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.23  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.13/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.23  
% 2.13/1.24  tff(f_61, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 2.13/1.24  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.13/1.24  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.13/1.24  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.13/1.24  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.13/1.24  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.13/1.24  tff(f_29, axiom, (![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_xboole_1)).
% 2.13/1.24  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.13/1.24  tff(c_16, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.13/1.24  tff(c_18, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.13/1.24  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.13/1.24  tff(c_63, plain, (![A_27, B_28]: (k3_subset_1(A_27, k3_subset_1(A_27, B_28))=B_28 | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.24  tff(c_69, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_22, c_63])).
% 2.13/1.24  tff(c_24, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.24  tff(c_31, plain, (k3_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_24])).
% 2.13/1.24  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.13/1.24  tff(c_78, plain, (![A_29, B_30, C_31]: (k9_subset_1(A_29, B_30, C_31)=k3_xboole_0(B_30, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.13/1.24  tff(c_96, plain, (![B_35]: (k9_subset_1('#skF_1', B_35, '#skF_3')=k3_xboole_0(B_35, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_78])).
% 2.13/1.24  tff(c_10, plain, (![A_10, B_11, C_12]: (m1_subset_1(k9_subset_1(A_10, B_11, C_12), k1_zfmisc_1(A_10)) | ~m1_subset_1(C_12, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.24  tff(c_102, plain, (![B_35]: (m1_subset_1(k3_xboole_0(B_35, '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_10])).
% 2.13/1.24  tff(c_110, plain, (![B_36]: (m1_subset_1(k3_xboole_0(B_36, '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_102])).
% 2.13/1.24  tff(c_119, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_31, c_110])).
% 2.13/1.24  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k3_subset_1(A_8, B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.24  tff(c_129, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_119, c_8])).
% 2.13/1.24  tff(c_134, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_129])).
% 2.13/1.24  tff(c_46, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k3_subset_1(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.24  tff(c_53, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_46])).
% 2.13/1.24  tff(c_199, plain, (![A_42, B_43, C_44]: (k2_xboole_0(k4_xboole_0(A_42, B_43), k3_xboole_0(A_42, k4_xboole_0(B_43, C_44)))=k4_xboole_0(A_42, C_44) | ~r1_tarski(C_44, B_43))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.24  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.24  tff(c_238, plain, (![A_45, B_46, C_47]: (r1_tarski(k4_xboole_0(A_45, B_46), k4_xboole_0(A_45, C_47)) | ~r1_tarski(C_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_199, c_6])).
% 2.13/1.24  tff(c_301, plain, (![C_50]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k4_xboole_0('#skF_1', C_50)) | ~r1_tarski(C_50, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_238])).
% 2.13/1.24  tff(c_310, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_134, c_301])).
% 2.13/1.24  tff(c_319, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_310])).
% 2.13/1.24  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_319])).
% 2.13/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  Inference rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Ref     : 0
% 2.19/1.24  #Sup     : 85
% 2.19/1.24  #Fact    : 0
% 2.19/1.24  #Define  : 0
% 2.19/1.24  #Split   : 0
% 2.19/1.24  #Chain   : 0
% 2.19/1.24  #Close   : 0
% 2.19/1.24  
% 2.19/1.24  Ordering : KBO
% 2.19/1.24  
% 2.19/1.24  Simplification rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Subsume      : 0
% 2.19/1.24  #Demod        : 10
% 2.19/1.24  #Tautology    : 31
% 2.19/1.24  #SimpNegUnit  : 1
% 2.19/1.24  #BackRed      : 0
% 2.19/1.24  
% 2.19/1.24  #Partial instantiations: 0
% 2.19/1.24  #Strategies tried      : 1
% 2.19/1.24  
% 2.19/1.24  Timing (in seconds)
% 2.19/1.24  ----------------------
% 2.19/1.25  Preprocessing        : 0.28
% 2.19/1.25  Parsing              : 0.15
% 2.19/1.25  CNF conversion       : 0.02
% 2.19/1.25  Main loop            : 0.20
% 2.19/1.25  Inferencing          : 0.08
% 2.19/1.25  Reduction            : 0.07
% 2.19/1.25  Demodulation         : 0.05
% 2.19/1.25  BG Simplification    : 0.01
% 2.19/1.25  Subsumption          : 0.03
% 2.19/1.25  Abstraction          : 0.01
% 2.19/1.25  MUC search           : 0.00
% 2.19/1.25  Cooper               : 0.00
% 2.19/1.25  Total                : 0.51
% 2.19/1.25  Index Insertion      : 0.00
% 2.19/1.25  Index Deletion       : 0.00
% 2.19/1.25  Index Matching       : 0.00
% 2.19/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
