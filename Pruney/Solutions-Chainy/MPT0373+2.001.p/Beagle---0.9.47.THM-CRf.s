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
% DateTime   : Thu Dec  3 09:56:56 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   55 (  65 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 (  87 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_66,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_95,plain,(
    ! [B_36,A_37] :
      ( v1_xboole_0(B_36)
      | ~ m1_subset_1(B_36,A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_103,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_95])).

tff(c_104,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_26,plain,(
    ! [B_23,A_22] :
      ( r2_hidden(B_23,A_22)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_107,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_tarski(A_42),B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_278,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(k1_tarski(A_81),B_82) = k1_tarski(A_81)
      | ~ r2_hidden(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_107,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_157,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k4_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_26,B_27] : k6_subset_1(A_26,B_27) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ! [A_24,B_25] : m1_subset_1(k6_subset_1(A_24,B_25),k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_41,plain,(
    ! [A_24,B_25] : m1_subset_1(k4_xboole_0(A_24,B_25),k1_zfmisc_1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_178,plain,(
    ! [A_58,B_59] : m1_subset_1(k3_xboole_0(A_58,B_59),k1_zfmisc_1(A_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_41])).

tff(c_184,plain,(
    ! [B_2,A_1] : m1_subset_1(k3_xboole_0(B_2,A_1),k1_zfmisc_1(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_368,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1(k1_tarski(A_85),k1_zfmisc_1(B_86))
      | ~ r2_hidden(A_85,B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_184])).

tff(c_36,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_376,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_368,c_36])).

tff(c_379,plain,
    ( ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_376])).

tff(c_382,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_379])).

tff(c_384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_382])).

tff(c_386,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_393,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_386,c_4])).

tff(c_397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.26  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.18/1.26  
% 2.18/1.26  %Foreground sorts:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Background operators:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Foreground operators:
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.18/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.26  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.18/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.26  
% 2.18/1.27  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.18/1.27  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.18/1.27  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.18/1.27  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.18/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.18/1.27  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.18/1.27  tff(f_68, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.18/1.27  tff(f_66, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.18/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.18/1.27  tff(c_38, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.18/1.27  tff(c_40, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.18/1.27  tff(c_95, plain, (![B_36, A_37]: (v1_xboole_0(B_36) | ~m1_subset_1(B_36, A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.27  tff(c_103, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_95])).
% 2.18/1.27  tff(c_104, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_103])).
% 2.18/1.27  tff(c_26, plain, (![B_23, A_22]: (r2_hidden(B_23, A_22) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.27  tff(c_107, plain, (![A_42, B_43]: (r1_tarski(k1_tarski(A_42), B_43) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.27  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.27  tff(c_278, plain, (![A_81, B_82]: (k3_xboole_0(k1_tarski(A_81), B_82)=k1_tarski(A_81) | ~r2_hidden(A_81, B_82))), inference(resolution, [status(thm)], [c_107, c_8])).
% 2.18/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.27  tff(c_157, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k4_xboole_0(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.27  tff(c_34, plain, (![A_26, B_27]: (k6_subset_1(A_26, B_27)=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.18/1.27  tff(c_32, plain, (![A_24, B_25]: (m1_subset_1(k6_subset_1(A_24, B_25), k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.18/1.27  tff(c_41, plain, (![A_24, B_25]: (m1_subset_1(k4_xboole_0(A_24, B_25), k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 2.18/1.27  tff(c_178, plain, (![A_58, B_59]: (m1_subset_1(k3_xboole_0(A_58, B_59), k1_zfmisc_1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_41])).
% 2.18/1.27  tff(c_184, plain, (![B_2, A_1]: (m1_subset_1(k3_xboole_0(B_2, A_1), k1_zfmisc_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_178])).
% 2.18/1.27  tff(c_368, plain, (![A_85, B_86]: (m1_subset_1(k1_tarski(A_85), k1_zfmisc_1(B_86)) | ~r2_hidden(A_85, B_86))), inference(superposition, [status(thm), theory('equality')], [c_278, c_184])).
% 2.18/1.27  tff(c_36, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.18/1.27  tff(c_376, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_368, c_36])).
% 2.18/1.27  tff(c_379, plain, (~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_376])).
% 2.18/1.27  tff(c_382, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_379])).
% 2.18/1.27  tff(c_384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_382])).
% 2.18/1.27  tff(c_386, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_103])).
% 2.18/1.27  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.27  tff(c_393, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_386, c_4])).
% 2.18/1.27  tff(c_397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_393])).
% 2.18/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  Inference rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Ref     : 0
% 2.18/1.27  #Sup     : 85
% 2.18/1.27  #Fact    : 0
% 2.18/1.27  #Define  : 0
% 2.18/1.27  #Split   : 2
% 2.18/1.27  #Chain   : 0
% 2.18/1.27  #Close   : 0
% 2.18/1.27  
% 2.18/1.27  Ordering : KBO
% 2.18/1.27  
% 2.18/1.27  Simplification rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Subsume      : 9
% 2.18/1.27  #Demod        : 8
% 2.18/1.27  #Tautology    : 39
% 2.18/1.27  #SimpNegUnit  : 2
% 2.18/1.27  #BackRed      : 0
% 2.18/1.27  
% 2.18/1.27  #Partial instantiations: 0
% 2.18/1.27  #Strategies tried      : 1
% 2.18/1.27  
% 2.18/1.27  Timing (in seconds)
% 2.18/1.27  ----------------------
% 2.18/1.28  Preprocessing        : 0.30
% 2.18/1.28  Parsing              : 0.17
% 2.18/1.28  CNF conversion       : 0.02
% 2.18/1.28  Main loop            : 0.22
% 2.18/1.28  Inferencing          : 0.08
% 2.18/1.28  Reduction            : 0.07
% 2.18/1.28  Demodulation         : 0.05
% 2.18/1.28  BG Simplification    : 0.01
% 2.18/1.28  Subsumption          : 0.03
% 2.18/1.28  Abstraction          : 0.01
% 2.18/1.28  MUC search           : 0.00
% 2.18/1.28  Cooper               : 0.00
% 2.18/1.28  Total                : 0.55
% 2.18/1.28  Index Insertion      : 0.00
% 2.18/1.28  Index Deletion       : 0.00
% 2.18/1.28  Index Matching       : 0.00
% 2.18/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
