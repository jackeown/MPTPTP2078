%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:06 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  64 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_38,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_39,plain,(
    ! [B_15,A_16] :
      ( ~ v1_xboole_0(B_15)
      | ~ r2_hidden(A_16,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_39])).

tff(c_61,plain,(
    ! [B_25,A_26] :
      ( m1_subset_1(B_25,A_26)
      | ~ r2_hidden(B_25,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_67,plain,
    ( m1_subset_1('#skF_3','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_61])).

tff(c_71,plain,(
    m1_subset_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_67])).

tff(c_107,plain,(
    ! [B_35,A_36] :
      ( m1_subset_1(k1_tarski(B_35),k1_zfmisc_1(A_36))
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(B_35,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_113,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_36])).

tff(c_117,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_113])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(k1_tarski(A_9),B_10) = k1_xboole_0
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_89,plain,(
    ! [D_29,B_30,A_31] :
      ( ~ r2_hidden(D_29,B_30)
      | ~ r2_hidden(D_29,k4_xboole_0(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [D_29,B_10,A_9] :
      ( ~ r2_hidden(D_29,B_10)
      | ~ r2_hidden(D_29,k1_xboole_0)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_89])).

tff(c_166,plain,(
    ! [D_44,B_45,A_46] :
      ( ~ r2_hidden(D_44,B_45)
      | ~ r2_hidden(D_44,'#skF_4')
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_92])).

tff(c_172,plain,(
    ! [A_46] :
      ( ~ r2_hidden('#skF_3','#skF_4')
      | ~ r2_hidden(A_46,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_166])).

tff(c_177,plain,(
    ! [A_46] : ~ r2_hidden(A_46,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_172])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n004.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:40:38 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.22  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.88/1.22  
% 1.88/1.22  %Foreground sorts:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Background operators:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Foreground operators:
% 1.88/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.88/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.22  
% 2.01/1.23  tff(f_69, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.01/1.23  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 2.01/1.23  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.01/1.23  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.01/1.23  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.01/1.23  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.01/1.23  tff(c_38, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.01/1.23  tff(c_39, plain, (![B_15, A_16]: (~v1_xboole_0(B_15) | ~r2_hidden(A_16, B_15))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.01/1.23  tff(c_43, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_39])).
% 2.01/1.23  tff(c_61, plain, (![B_25, A_26]: (m1_subset_1(B_25, A_26) | ~r2_hidden(B_25, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.23  tff(c_67, plain, (m1_subset_1('#skF_3', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_61])).
% 2.01/1.23  tff(c_71, plain, (m1_subset_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_43, c_67])).
% 2.01/1.23  tff(c_107, plain, (![B_35, A_36]: (m1_subset_1(k1_tarski(B_35), k1_zfmisc_1(A_36)) | k1_xboole_0=A_36 | ~m1_subset_1(B_35, A_36))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.01/1.23  tff(c_36, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.01/1.23  tff(c_113, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_107, c_36])).
% 2.01/1.23  tff(c_117, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_113])).
% 2.01/1.23  tff(c_24, plain, (![A_9, B_10]: (k4_xboole_0(k1_tarski(A_9), B_10)=k1_xboole_0 | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.01/1.23  tff(c_89, plain, (![D_29, B_30, A_31]: (~r2_hidden(D_29, B_30) | ~r2_hidden(D_29, k4_xboole_0(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.23  tff(c_92, plain, (![D_29, B_10, A_9]: (~r2_hidden(D_29, B_10) | ~r2_hidden(D_29, k1_xboole_0) | ~r2_hidden(A_9, B_10))), inference(superposition, [status(thm), theory('equality')], [c_24, c_89])).
% 2.01/1.23  tff(c_166, plain, (![D_44, B_45, A_46]: (~r2_hidden(D_44, B_45) | ~r2_hidden(D_44, '#skF_4') | ~r2_hidden(A_46, B_45))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_92])).
% 2.01/1.23  tff(c_172, plain, (![A_46]: (~r2_hidden('#skF_3', '#skF_4') | ~r2_hidden(A_46, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_166])).
% 2.01/1.23  tff(c_177, plain, (![A_46]: (~r2_hidden(A_46, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_172])).
% 2.01/1.23  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_38])).
% 2.01/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.23  
% 2.01/1.23  Inference rules
% 2.01/1.23  ----------------------
% 2.01/1.23  #Ref     : 0
% 2.01/1.23  #Sup     : 31
% 2.01/1.23  #Fact    : 0
% 2.01/1.23  #Define  : 0
% 2.01/1.23  #Split   : 1
% 2.01/1.23  #Chain   : 0
% 2.01/1.23  #Close   : 0
% 2.01/1.23  
% 2.01/1.23  Ordering : KBO
% 2.01/1.23  
% 2.01/1.23  Simplification rules
% 2.01/1.23  ----------------------
% 2.01/1.23  #Subsume      : 2
% 2.01/1.23  #Demod        : 6
% 2.01/1.23  #Tautology    : 13
% 2.01/1.23  #SimpNegUnit  : 2
% 2.01/1.23  #BackRed      : 4
% 2.01/1.23  
% 2.01/1.23  #Partial instantiations: 0
% 2.01/1.23  #Strategies tried      : 1
% 2.01/1.23  
% 2.01/1.23  Timing (in seconds)
% 2.01/1.23  ----------------------
% 2.01/1.24  Preprocessing        : 0.27
% 2.01/1.24  Parsing              : 0.14
% 2.01/1.24  CNF conversion       : 0.02
% 2.01/1.24  Main loop            : 0.16
% 2.01/1.24  Inferencing          : 0.06
% 2.01/1.24  Reduction            : 0.04
% 2.01/1.24  Demodulation         : 0.02
% 2.01/1.24  BG Simplification    : 0.01
% 2.01/1.24  Subsumption          : 0.04
% 2.01/1.24  Abstraction          : 0.01
% 2.01/1.24  MUC search           : 0.00
% 2.01/1.24  Cooper               : 0.00
% 2.01/1.24  Total                : 0.46
% 2.01/1.24  Index Insertion      : 0.00
% 2.01/1.24  Index Deletion       : 0.00
% 2.01/1.24  Index Matching       : 0.00
% 2.05/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
