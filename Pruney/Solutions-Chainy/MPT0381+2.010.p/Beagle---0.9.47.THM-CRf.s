%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:02 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   49 (  79 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 134 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_296,plain,(
    ! [A_85,B_86,C_87] :
      ( r1_tarski(k2_tarski(A_85,B_86),C_87)
      | ~ r2_hidden(B_86,C_87)
      | ~ r2_hidden(A_85,C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_164,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(k2_tarski(A_56,B_57),C_58)
      | ~ r2_hidden(B_57,C_58)
      | ~ r2_hidden(A_56,C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_191,plain,(
    ! [A_61,C_62] :
      ( r1_tarski(k1_tarski(A_61),C_62)
      | ~ r2_hidden(A_61,C_62)
      | ~ r2_hidden(A_61,C_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_86,plain,(
    ! [B_35,A_36] :
      ( m1_subset_1(B_35,A_36)
      | ~ v1_xboole_0(B_35)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_94,plain,
    ( ~ v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_86,c_38])).

tff(c_95,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_14,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_106,plain,(
    ! [B_39,A_40] :
      ( m1_subset_1(B_39,A_40)
      | ~ r2_hidden(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_176,plain,(
    ! [C_59,A_60] :
      ( m1_subset_1(C_59,k1_zfmisc_1(A_60))
      | v1_xboole_0(k1_zfmisc_1(A_60))
      | ~ r1_tarski(C_59,A_60) ) ),
    inference(resolution,[status(thm)],[c_14,c_106])).

tff(c_185,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_5'))
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_176,c_38])).

tff(c_190,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_185])).

tff(c_194,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_191,c_190])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_194])).

tff(c_203,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_60,plain,(
    ! [C_25,A_26] :
      ( r2_hidden(C_25,k1_zfmisc_1(A_26))
      | ~ r1_tarski(C_25,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_26,C_25] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_26))
      | ~ r1_tarski(C_25,A_26) ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_206,plain,(
    ! [C_25] : ~ r1_tarski(C_25,'#skF_5') ),
    inference(resolution,[status(thm)],[c_203,c_64])).

tff(c_312,plain,(
    ! [B_86,A_85] :
      ( ~ r2_hidden(B_86,'#skF_5')
      | ~ r2_hidden(A_85,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_296,c_206])).

tff(c_313,plain,(
    ! [A_85] : ~ r2_hidden(A_85,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_40])).

tff(c_330,plain,(
    ! [B_86] : ~ r2_hidden(B_86,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:55:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.27  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.10/1.27  
% 2.10/1.27  %Foreground sorts:
% 2.10/1.27  
% 2.10/1.27  
% 2.10/1.27  %Background operators:
% 2.10/1.27  
% 2.10/1.27  
% 2.10/1.27  %Foreground operators:
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.10/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.10/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.27  
% 2.10/1.28  tff(f_50, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.10/1.28  tff(f_68, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.10/1.28  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.10/1.28  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.10/1.28  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.10/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.10/1.28  tff(c_296, plain, (![A_85, B_86, C_87]: (r1_tarski(k2_tarski(A_85, B_86), C_87) | ~r2_hidden(B_86, C_87) | ~r2_hidden(A_85, C_87))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.28  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.28  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.28  tff(c_164, plain, (![A_56, B_57, C_58]: (r1_tarski(k2_tarski(A_56, B_57), C_58) | ~r2_hidden(B_57, C_58) | ~r2_hidden(A_56, C_58))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.28  tff(c_191, plain, (![A_61, C_62]: (r1_tarski(k1_tarski(A_61), C_62) | ~r2_hidden(A_61, C_62) | ~r2_hidden(A_61, C_62))), inference(superposition, [status(thm), theory('equality')], [c_6, c_164])).
% 2.10/1.28  tff(c_86, plain, (![B_35, A_36]: (m1_subset_1(B_35, A_36) | ~v1_xboole_0(B_35) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.10/1.28  tff(c_38, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.28  tff(c_94, plain, (~v1_xboole_0(k1_tarski('#skF_4')) | ~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_86, c_38])).
% 2.10/1.28  tff(c_95, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_94])).
% 2.10/1.28  tff(c_14, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.28  tff(c_106, plain, (![B_39, A_40]: (m1_subset_1(B_39, A_40) | ~r2_hidden(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.10/1.28  tff(c_176, plain, (![C_59, A_60]: (m1_subset_1(C_59, k1_zfmisc_1(A_60)) | v1_xboole_0(k1_zfmisc_1(A_60)) | ~r1_tarski(C_59, A_60))), inference(resolution, [status(thm)], [c_14, c_106])).
% 2.10/1.28  tff(c_185, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5')) | ~r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_176, c_38])).
% 2.10/1.28  tff(c_190, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_95, c_185])).
% 2.10/1.28  tff(c_194, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_191, c_190])).
% 2.10/1.28  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_194])).
% 2.10/1.28  tff(c_203, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_94])).
% 2.10/1.28  tff(c_60, plain, (![C_25, A_26]: (r2_hidden(C_25, k1_zfmisc_1(A_26)) | ~r1_tarski(C_25, A_26))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.28  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.28  tff(c_64, plain, (![A_26, C_25]: (~v1_xboole_0(k1_zfmisc_1(A_26)) | ~r1_tarski(C_25, A_26))), inference(resolution, [status(thm)], [c_60, c_2])).
% 2.10/1.28  tff(c_206, plain, (![C_25]: (~r1_tarski(C_25, '#skF_5'))), inference(resolution, [status(thm)], [c_203, c_64])).
% 2.10/1.28  tff(c_312, plain, (![B_86, A_85]: (~r2_hidden(B_86, '#skF_5') | ~r2_hidden(A_85, '#skF_5'))), inference(resolution, [status(thm)], [c_296, c_206])).
% 2.10/1.28  tff(c_313, plain, (![A_85]: (~r2_hidden(A_85, '#skF_5'))), inference(splitLeft, [status(thm)], [c_312])).
% 2.10/1.28  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_313, c_40])).
% 2.10/1.28  tff(c_330, plain, (![B_86]: (~r2_hidden(B_86, '#skF_5'))), inference(splitRight, [status(thm)], [c_312])).
% 2.10/1.28  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_330, c_40])).
% 2.10/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.28  
% 2.10/1.28  Inference rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Ref     : 0
% 2.10/1.28  #Sup     : 59
% 2.10/1.28  #Fact    : 0
% 2.10/1.28  #Define  : 0
% 2.10/1.28  #Split   : 2
% 2.10/1.28  #Chain   : 0
% 2.10/1.28  #Close   : 0
% 2.10/1.28  
% 2.10/1.28  Ordering : KBO
% 2.10/1.28  
% 2.10/1.28  Simplification rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Subsume      : 10
% 2.10/1.28  #Demod        : 3
% 2.10/1.28  #Tautology    : 26
% 2.10/1.28  #SimpNegUnit  : 5
% 2.10/1.28  #BackRed      : 2
% 2.10/1.28  
% 2.10/1.28  #Partial instantiations: 0
% 2.10/1.28  #Strategies tried      : 1
% 2.10/1.28  
% 2.10/1.28  Timing (in seconds)
% 2.10/1.28  ----------------------
% 2.10/1.28  Preprocessing        : 0.30
% 2.10/1.28  Parsing              : 0.16
% 2.10/1.28  CNF conversion       : 0.02
% 2.10/1.28  Main loop            : 0.20
% 2.10/1.28  Inferencing          : 0.08
% 2.10/1.28  Reduction            : 0.05
% 2.10/1.28  Demodulation         : 0.03
% 2.10/1.28  BG Simplification    : 0.02
% 2.10/1.28  Subsumption          : 0.04
% 2.10/1.28  Abstraction          : 0.01
% 2.10/1.28  MUC search           : 0.00
% 2.10/1.28  Cooper               : 0.00
% 2.10/1.28  Total                : 0.53
% 2.10/1.28  Index Insertion      : 0.00
% 2.10/1.28  Index Deletion       : 0.00
% 2.10/1.28  Index Matching       : 0.00
% 2.10/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
