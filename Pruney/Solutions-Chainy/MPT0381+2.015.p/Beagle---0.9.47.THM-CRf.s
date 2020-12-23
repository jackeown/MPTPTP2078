%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:03 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 107 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 190 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_40,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_41,plain,(
    ! [B_17,A_18] :
      ( ~ r2_hidden(B_17,A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_41])).

tff(c_62,plain,(
    ! [B_24,A_25] :
      ( m1_subset_1(B_24,A_25)
      | ~ r2_hidden(B_24,A_25)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_68,plain,
    ( m1_subset_1('#skF_4','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_62])).

tff(c_72,plain,(
    m1_subset_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_68])).

tff(c_208,plain,(
    ! [B_48,A_49] :
      ( m1_subset_1(k1_tarski(B_48),k1_zfmisc_1(A_49))
      | k1_xboole_0 = A_49
      | ~ m1_subset_1(B_48,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_208,c_38])).

tff(c_218,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_214])).

tff(c_167,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(k1_tarski(B_44),k1_zfmisc_1(A_45))
      | k1_xboole_0 = A_45
      | ~ m1_subset_1(B_44,A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_173,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_167,c_38])).

tff(c_177,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_173])).

tff(c_30,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(B_14,A_13)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(k1_tarski(A_11),B_12) = k1_xboole_0
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_100,plain,(
    ! [D_32,B_33,A_34] :
      ( ~ r2_hidden(D_32,B_33)
      | ~ r2_hidden(D_32,k4_xboole_0(A_34,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_133,plain,(
    ! [D_39,B_40,A_41] :
      ( ~ r2_hidden(D_39,B_40)
      | ~ r2_hidden(D_39,k1_xboole_0)
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_100])).

tff(c_142,plain,(
    ! [A_41] :
      ( ~ r2_hidden('#skF_4',k1_xboole_0)
      | ~ r2_hidden(A_41,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_133])).

tff(c_143,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_147,plain,
    ( ~ m1_subset_1('#skF_4',k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_143])).

tff(c_148,plain,(
    ~ m1_subset_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_181,plain,(
    ~ m1_subset_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_148])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_181])).

tff(c_189,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_222,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_189])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_222])).

tff(c_230,plain,(
    ! [A_41] : ~ r2_hidden(A_41,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:23:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.29  
% 2.07/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.29  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.07/1.29  
% 2.07/1.29  %Foreground sorts:
% 2.07/1.29  
% 2.07/1.29  
% 2.07/1.29  %Background operators:
% 2.07/1.29  
% 2.07/1.29  
% 2.07/1.29  %Foreground operators:
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.07/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.29  
% 2.07/1.30  tff(f_70, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.07/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.07/1.30  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.07/1.30  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.07/1.30  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.07/1.30  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.07/1.30  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.07/1.30  tff(c_41, plain, (![B_17, A_18]: (~r2_hidden(B_17, A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.30  tff(c_45, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_41])).
% 2.07/1.30  tff(c_62, plain, (![B_24, A_25]: (m1_subset_1(B_24, A_25) | ~r2_hidden(B_24, A_25) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.07/1.30  tff(c_68, plain, (m1_subset_1('#skF_4', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_62])).
% 2.07/1.30  tff(c_72, plain, (m1_subset_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_45, c_68])).
% 2.07/1.30  tff(c_208, plain, (![B_48, A_49]: (m1_subset_1(k1_tarski(B_48), k1_zfmisc_1(A_49)) | k1_xboole_0=A_49 | ~m1_subset_1(B_48, A_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.30  tff(c_38, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.07/1.30  tff(c_214, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_208, c_38])).
% 2.07/1.30  tff(c_218, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_214])).
% 2.07/1.30  tff(c_167, plain, (![B_44, A_45]: (m1_subset_1(k1_tarski(B_44), k1_zfmisc_1(A_45)) | k1_xboole_0=A_45 | ~m1_subset_1(B_44, A_45))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.30  tff(c_173, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_167, c_38])).
% 2.07/1.30  tff(c_177, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_173])).
% 2.07/1.30  tff(c_30, plain, (![B_14, A_13]: (r2_hidden(B_14, A_13) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.07/1.30  tff(c_26, plain, (![A_11, B_12]: (k4_xboole_0(k1_tarski(A_11), B_12)=k1_xboole_0 | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.07/1.30  tff(c_100, plain, (![D_32, B_33, A_34]: (~r2_hidden(D_32, B_33) | ~r2_hidden(D_32, k4_xboole_0(A_34, B_33)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.30  tff(c_133, plain, (![D_39, B_40, A_41]: (~r2_hidden(D_39, B_40) | ~r2_hidden(D_39, k1_xboole_0) | ~r2_hidden(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_26, c_100])).
% 2.07/1.30  tff(c_142, plain, (![A_41]: (~r2_hidden('#skF_4', k1_xboole_0) | ~r2_hidden(A_41, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_133])).
% 2.07/1.30  tff(c_143, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_142])).
% 2.07/1.30  tff(c_147, plain, (~m1_subset_1('#skF_4', k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_143])).
% 2.07/1.30  tff(c_148, plain, (~m1_subset_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_147])).
% 2.07/1.30  tff(c_181, plain, (~m1_subset_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_148])).
% 2.07/1.30  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_181])).
% 2.07/1.30  tff(c_189, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_147])).
% 2.07/1.30  tff(c_222, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_189])).
% 2.07/1.30  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_222])).
% 2.07/1.30  tff(c_230, plain, (![A_41]: (~r2_hidden(A_41, '#skF_5'))), inference(splitRight, [status(thm)], [c_142])).
% 2.07/1.30  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_40])).
% 2.07/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.30  
% 2.07/1.30  Inference rules
% 2.07/1.30  ----------------------
% 2.07/1.30  #Ref     : 0
% 2.07/1.30  #Sup     : 33
% 2.07/1.30  #Fact    : 0
% 2.07/1.30  #Define  : 0
% 2.07/1.30  #Split   : 4
% 2.07/1.30  #Chain   : 0
% 2.07/1.30  #Close   : 0
% 2.07/1.30  
% 2.07/1.30  Ordering : KBO
% 2.07/1.30  
% 2.07/1.30  Simplification rules
% 2.07/1.30  ----------------------
% 2.07/1.30  #Subsume      : 2
% 2.07/1.30  #Demod        : 23
% 2.07/1.30  #Tautology    : 11
% 2.07/1.30  #SimpNegUnit  : 5
% 2.07/1.30  #BackRed      : 17
% 2.07/1.30  
% 2.07/1.30  #Partial instantiations: 0
% 2.07/1.30  #Strategies tried      : 1
% 2.07/1.30  
% 2.07/1.30  Timing (in seconds)
% 2.07/1.30  ----------------------
% 2.07/1.30  Preprocessing        : 0.30
% 2.07/1.30  Parsing              : 0.16
% 2.07/1.30  CNF conversion       : 0.02
% 2.07/1.30  Main loop            : 0.18
% 2.07/1.30  Inferencing          : 0.07
% 2.07/1.30  Reduction            : 0.05
% 2.07/1.30  Demodulation         : 0.03
% 2.07/1.30  BG Simplification    : 0.01
% 2.07/1.30  Subsumption          : 0.04
% 2.07/1.30  Abstraction          : 0.01
% 2.07/1.30  MUC search           : 0.00
% 2.07/1.30  Cooper               : 0.00
% 2.07/1.30  Total                : 0.51
% 2.07/1.30  Index Insertion      : 0.00
% 2.07/1.30  Index Deletion       : 0.00
% 2.07/1.30  Index Matching       : 0.00
% 2.07/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
