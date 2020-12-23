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
% DateTime   : Thu Dec  3 09:56:20 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   49 (  78 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 130 expanded)
%              Number of equality atoms :   17 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_69,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_69])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_159,plain,(
    ! [A_40,B_41,C_42] :
      ( k9_subset_1(A_40,B_41,C_42) = k3_xboole_0(B_41,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_166,plain,(
    ! [B_43] : k9_subset_1('#skF_1',B_43,'#skF_3') = k3_xboole_0(B_43,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_159])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k9_subset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_172,plain,(
    ! [B_43] :
      ( m1_subset_1(k3_xboole_0(B_43,'#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_10])).

tff(c_180,plain,(
    ! [B_44] : m1_subset_1(k3_xboole_0(B_44,'#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_172])).

tff(c_184,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_180])).

tff(c_22,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_350,plain,(
    ! [C_55,A_56,B_57] :
      ( r1_tarski(C_55,k3_subset_1(A_56,B_57))
      | ~ r1_tarski(B_57,k3_subset_1(A_56,C_55))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_363,plain,
    ( r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_350])).

tff(c_370,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_26,c_363])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_81,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_2])).

tff(c_105,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_tarski(k3_xboole_0(A_26,C_27),B_28)
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [B_28] :
      ( r1_tarski('#skF_2',B_28)
      | ~ r1_tarski('#skF_3',B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_105])).

tff(c_8,plain,(
    ! [A_8] : k1_subset_1(A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( k1_subset_1(A_19) = B_20
      | ~ r1_tarski(B_20,k3_subset_1(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_194,plain,(
    ! [B_45,A_46] :
      ( k1_xboole_0 = B_45
      | ~ r1_tarski(B_45,k3_subset_1(A_46,B_45))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_205,plain,(
    ! [A_46] :
      ( k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_46))
      | ~ r1_tarski('#skF_3',k3_subset_1(A_46,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_114,c_194])).

tff(c_215,plain,(
    ! [A_46] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_46))
      | ~ r1_tarski('#skF_3',k3_subset_1(A_46,'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_205])).

tff(c_375,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_370,c_215])).

tff(c_388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.29  
% 2.18/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.30  %$ r1_tarski > m1_subset_1 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.30  
% 2.18/1.30  %Foreground sorts:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Background operators:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Foreground operators:
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.18/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.30  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.18/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.30  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.18/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.30  
% 2.18/1.31  tff(f_69, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 2.18/1.31  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.18/1.31  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.18/1.31  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.18/1.31  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 2.18/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.18/1.31  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.18/1.31  tff(f_37, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.18/1.31  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.18/1.31  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.31  tff(c_69, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.31  tff(c_77, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_24, c_69])).
% 2.18/1.31  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.31  tff(c_159, plain, (![A_40, B_41, C_42]: (k9_subset_1(A_40, B_41, C_42)=k3_xboole_0(B_41, C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.31  tff(c_166, plain, (![B_43]: (k9_subset_1('#skF_1', B_43, '#skF_3')=k3_xboole_0(B_43, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_159])).
% 2.18/1.31  tff(c_10, plain, (![A_9, B_10, C_11]: (m1_subset_1(k9_subset_1(A_9, B_10, C_11), k1_zfmisc_1(A_9)) | ~m1_subset_1(C_11, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.31  tff(c_172, plain, (![B_43]: (m1_subset_1(k3_xboole_0(B_43, '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_166, c_10])).
% 2.18/1.31  tff(c_180, plain, (![B_44]: (m1_subset_1(k3_xboole_0(B_44, '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_172])).
% 2.18/1.31  tff(c_184, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_180])).
% 2.18/1.31  tff(c_22, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.31  tff(c_350, plain, (![C_55, A_56, B_57]: (r1_tarski(C_55, k3_subset_1(A_56, B_57)) | ~r1_tarski(B_57, k3_subset_1(A_56, C_55)) | ~m1_subset_1(C_55, k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.18/1.31  tff(c_363, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_350])).
% 2.18/1.31  tff(c_370, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_26, c_363])).
% 2.18/1.31  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.31  tff(c_81, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_77, c_2])).
% 2.18/1.31  tff(c_105, plain, (![A_26, C_27, B_28]: (r1_tarski(k3_xboole_0(A_26, C_27), B_28) | ~r1_tarski(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.31  tff(c_114, plain, (![B_28]: (r1_tarski('#skF_2', B_28) | ~r1_tarski('#skF_3', B_28))), inference(superposition, [status(thm), theory('equality')], [c_81, c_105])).
% 2.18/1.31  tff(c_8, plain, (![A_8]: (k1_subset_1(A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.31  tff(c_18, plain, (![A_19, B_20]: (k1_subset_1(A_19)=B_20 | ~r1_tarski(B_20, k3_subset_1(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.31  tff(c_194, plain, (![B_45, A_46]: (k1_xboole_0=B_45 | ~r1_tarski(B_45, k3_subset_1(A_46, B_45)) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 2.18/1.31  tff(c_205, plain, (![A_46]: (k1_xboole_0='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(A_46)) | ~r1_tarski('#skF_3', k3_subset_1(A_46, '#skF_2')))), inference(resolution, [status(thm)], [c_114, c_194])).
% 2.18/1.31  tff(c_215, plain, (![A_46]: (~m1_subset_1('#skF_2', k1_zfmisc_1(A_46)) | ~r1_tarski('#skF_3', k3_subset_1(A_46, '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_20, c_205])).
% 2.18/1.31  tff(c_375, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_370, c_215])).
% 2.18/1.31  tff(c_388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_375])).
% 2.18/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  Inference rules
% 2.18/1.31  ----------------------
% 2.18/1.31  #Ref     : 0
% 2.18/1.31  #Sup     : 92
% 2.18/1.31  #Fact    : 0
% 2.18/1.31  #Define  : 0
% 2.18/1.31  #Split   : 0
% 2.18/1.31  #Chain   : 0
% 2.18/1.31  #Close   : 0
% 2.18/1.31  
% 2.18/1.31  Ordering : KBO
% 2.18/1.31  
% 2.18/1.31  Simplification rules
% 2.18/1.31  ----------------------
% 2.18/1.31  #Subsume      : 8
% 2.18/1.31  #Demod        : 29
% 2.18/1.31  #Tautology    : 41
% 2.18/1.31  #SimpNegUnit  : 1
% 2.18/1.31  #BackRed      : 0
% 2.18/1.31  
% 2.18/1.31  #Partial instantiations: 0
% 2.18/1.31  #Strategies tried      : 1
% 2.18/1.31  
% 2.18/1.31  Timing (in seconds)
% 2.18/1.31  ----------------------
% 2.18/1.31  Preprocessing        : 0.30
% 2.18/1.31  Parsing              : 0.17
% 2.18/1.31  CNF conversion       : 0.02
% 2.18/1.31  Main loop            : 0.23
% 2.18/1.31  Inferencing          : 0.08
% 2.18/1.31  Reduction            : 0.08
% 2.18/1.31  Demodulation         : 0.06
% 2.18/1.31  BG Simplification    : 0.02
% 2.18/1.31  Subsumption          : 0.04
% 2.18/1.31  Abstraction          : 0.01
% 2.18/1.31  MUC search           : 0.00
% 2.18/1.31  Cooper               : 0.00
% 2.18/1.31  Total                : 0.56
% 2.18/1.31  Index Insertion      : 0.00
% 2.18/1.31  Index Deletion       : 0.00
% 2.18/1.31  Index Matching       : 0.00
% 2.18/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
