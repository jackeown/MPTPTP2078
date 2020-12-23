%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:54 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   50 (  83 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 ( 131 expanded)
%              Number of equality atoms :   18 (  35 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_26,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_3')
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_41,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_10,plain,(
    ! [A_4,B_5,C_6] :
      ( r2_hidden(A_4,k4_xboole_0(B_5,k1_tarski(C_6)))
      | C_6 = A_4
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden(k1_mcart_1(A_32),B_33)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_33,C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_77,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_74])).

tff(c_48,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k1_tarski(A_23),k1_zfmisc_1(B_24))
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_tarski(A_23),B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_48,c_18])).

tff(c_58,plain,(
    ! [B_30,A_31] :
      ( k1_tarski(B_30) = A_31
      | k1_xboole_0 = A_31
      | ~ r1_tarski(A_31,k1_tarski(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    ! [B_41,A_42] :
      ( k1_tarski(B_41) = k1_tarski(A_42)
      | k1_tarski(A_42) = k1_xboole_0
      | ~ r2_hidden(A_42,k1_tarski(B_41)) ) ),
    inference(resolution,[status(thm)],[c_52,c_58])).

tff(c_94,plain,
    ( k1_tarski(k1_mcart_1('#skF_1')) = k1_tarski('#skF_2')
    | k1_tarski(k1_mcart_1('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_90])).

tff(c_95,plain,(
    k1_tarski(k1_mcart_1('#skF_1')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_12,plain,(
    ! [C_6,B_5] : ~ r2_hidden(C_6,k4_xboole_0(B_5,k1_tarski(C_6))) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_116,plain,(
    ! [B_5] : ~ r2_hidden(k1_mcart_1('#skF_1'),k4_xboole_0(B_5,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_12])).

tff(c_131,plain,(
    ! [B_5] : ~ r2_hidden(k1_mcart_1('#skF_1'),B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_116])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_77])).

tff(c_138,plain,(
    k1_tarski(k1_mcart_1('#skF_1')) = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_178,plain,(
    ! [B_43] : ~ r2_hidden(k1_mcart_1('#skF_1'),k4_xboole_0(B_43,k1_tarski('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_12])).

tff(c_182,plain,(
    ! [B_5] :
      ( k1_mcart_1('#skF_1') = '#skF_2'
      | ~ r2_hidden(k1_mcart_1('#skF_1'),B_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_178])).

tff(c_185,plain,(
    ! [B_5] : ~ r2_hidden(k1_mcart_1('#skF_1'),B_5) ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_182])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_77])).

tff(c_188,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_228,plain,(
    ! [A_60,C_61,B_62] :
      ( r2_hidden(k2_mcart_1(A_60),C_61)
      | ~ r2_hidden(A_60,k2_zfmisc_1(B_62,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_230,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_228])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.22  
% 1.83/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.83/1.23  
% 1.83/1.23  %Foreground sorts:
% 1.83/1.23  
% 1.83/1.23  
% 1.83/1.23  %Background operators:
% 1.83/1.23  
% 1.83/1.23  
% 1.83/1.23  %Foreground operators:
% 1.83/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.83/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.23  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.83/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.23  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.83/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.23  
% 1.83/1.24  tff(f_61, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.83/1.24  tff(f_40, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.83/1.24  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.83/1.24  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.83/1.24  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.83/1.24  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.83/1.24  tff(f_33, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.83/1.24  tff(c_26, plain, (~r2_hidden(k2_mcart_1('#skF_1'), '#skF_3') | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.24  tff(c_41, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 1.83/1.24  tff(c_10, plain, (![A_4, B_5, C_6]: (r2_hidden(A_4, k4_xboole_0(B_5, k1_tarski(C_6))) | C_6=A_4 | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.24  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.24  tff(c_28, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.24  tff(c_74, plain, (![A_32, B_33, C_34]: (r2_hidden(k1_mcart_1(A_32), B_33) | ~r2_hidden(A_32, k2_zfmisc_1(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.83/1.24  tff(c_77, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_74])).
% 1.83/1.24  tff(c_48, plain, (![A_23, B_24]: (m1_subset_1(k1_tarski(A_23), k1_zfmisc_1(B_24)) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.24  tff(c_18, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.83/1.24  tff(c_52, plain, (![A_23, B_24]: (r1_tarski(k1_tarski(A_23), B_24) | ~r2_hidden(A_23, B_24))), inference(resolution, [status(thm)], [c_48, c_18])).
% 1.83/1.24  tff(c_58, plain, (![B_30, A_31]: (k1_tarski(B_30)=A_31 | k1_xboole_0=A_31 | ~r1_tarski(A_31, k1_tarski(B_30)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.83/1.24  tff(c_90, plain, (![B_41, A_42]: (k1_tarski(B_41)=k1_tarski(A_42) | k1_tarski(A_42)=k1_xboole_0 | ~r2_hidden(A_42, k1_tarski(B_41)))), inference(resolution, [status(thm)], [c_52, c_58])).
% 1.83/1.24  tff(c_94, plain, (k1_tarski(k1_mcart_1('#skF_1'))=k1_tarski('#skF_2') | k1_tarski(k1_mcart_1('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_77, c_90])).
% 1.83/1.24  tff(c_95, plain, (k1_tarski(k1_mcart_1('#skF_1'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_94])).
% 1.83/1.24  tff(c_12, plain, (![C_6, B_5]: (~r2_hidden(C_6, k4_xboole_0(B_5, k1_tarski(C_6))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.24  tff(c_116, plain, (![B_5]: (~r2_hidden(k1_mcart_1('#skF_1'), k4_xboole_0(B_5, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_95, c_12])).
% 1.83/1.24  tff(c_131, plain, (![B_5]: (~r2_hidden(k1_mcart_1('#skF_1'), B_5))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_116])).
% 1.83/1.24  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_77])).
% 1.83/1.24  tff(c_138, plain, (k1_tarski(k1_mcart_1('#skF_1'))=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_94])).
% 1.83/1.24  tff(c_178, plain, (![B_43]: (~r2_hidden(k1_mcart_1('#skF_1'), k4_xboole_0(B_43, k1_tarski('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_138, c_12])).
% 1.83/1.24  tff(c_182, plain, (![B_5]: (k1_mcart_1('#skF_1')='#skF_2' | ~r2_hidden(k1_mcart_1('#skF_1'), B_5))), inference(resolution, [status(thm)], [c_10, c_178])).
% 1.83/1.24  tff(c_185, plain, (![B_5]: (~r2_hidden(k1_mcart_1('#skF_1'), B_5))), inference(negUnitSimplification, [status(thm)], [c_41, c_182])).
% 1.83/1.24  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_77])).
% 1.83/1.24  tff(c_188, plain, (~r2_hidden(k2_mcart_1('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 1.83/1.24  tff(c_228, plain, (![A_60, C_61, B_62]: (r2_hidden(k2_mcart_1(A_60), C_61) | ~r2_hidden(A_60, k2_zfmisc_1(B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.83/1.24  tff(c_230, plain, (r2_hidden(k2_mcart_1('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_28, c_228])).
% 1.83/1.24  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_230])).
% 1.83/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.24  
% 1.83/1.24  Inference rules
% 1.83/1.24  ----------------------
% 1.83/1.24  #Ref     : 0
% 1.83/1.24  #Sup     : 46
% 1.83/1.24  #Fact    : 0
% 1.83/1.24  #Define  : 0
% 1.83/1.24  #Split   : 2
% 1.83/1.24  #Chain   : 0
% 2.06/1.24  #Close   : 0
% 2.06/1.24  
% 2.06/1.24  Ordering : KBO
% 2.06/1.24  
% 2.06/1.24  Simplification rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Subsume      : 4
% 2.06/1.24  #Demod        : 17
% 2.06/1.24  #Tautology    : 23
% 2.06/1.24  #SimpNegUnit  : 4
% 2.06/1.24  #BackRed      : 3
% 2.06/1.24  
% 2.06/1.24  #Partial instantiations: 0
% 2.06/1.24  #Strategies tried      : 1
% 2.06/1.24  
% 2.06/1.24  Timing (in seconds)
% 2.06/1.24  ----------------------
% 2.06/1.25  Preprocessing        : 0.26
% 2.06/1.25  Parsing              : 0.14
% 2.06/1.25  CNF conversion       : 0.02
% 2.06/1.25  Main loop            : 0.17
% 2.06/1.25  Inferencing          : 0.07
% 2.06/1.25  Reduction            : 0.05
% 2.06/1.25  Demodulation         : 0.04
% 2.06/1.25  BG Simplification    : 0.01
% 2.06/1.25  Subsumption          : 0.03
% 2.06/1.25  Abstraction          : 0.01
% 2.06/1.25  MUC search           : 0.00
% 2.06/1.25  Cooper               : 0.00
% 2.06/1.25  Total                : 0.47
% 2.06/1.25  Index Insertion      : 0.00
% 2.06/1.25  Index Deletion       : 0.00
% 2.06/1.25  Index Matching       : 0.00
% 2.06/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
