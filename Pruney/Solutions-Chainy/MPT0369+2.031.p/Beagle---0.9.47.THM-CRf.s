%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:55 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 103 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42,plain,(
    ! [B_17,A_18] :
      ( v1_xboole_0(B_17)
      | ~ m1_subset_1(B_17,A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_42])).

tff(c_51,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_24,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_96,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k3_subset_1(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_105,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_96])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_148,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,k3_subset_1('#skF_3','#skF_4'))
      | r2_hidden(D_38,'#skF_4')
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_2])).

tff(c_32,plain,(
    ~ r2_hidden('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_160,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_32])).

tff(c_168,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_160])).

tff(c_171,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_168])).

tff(c_174,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_171])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_174])).

tff(c_178,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_20,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_185,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_178,c_20])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.30  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.96/1.30  
% 1.96/1.30  %Foreground sorts:
% 1.96/1.30  
% 1.96/1.30  
% 1.96/1.30  %Background operators:
% 1.96/1.30  
% 1.96/1.30  
% 1.96/1.30  %Foreground operators:
% 1.96/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.96/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.96/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.30  
% 1.96/1.31  tff(f_71, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 1.96/1.31  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.96/1.31  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.96/1.31  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.96/1.31  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 1.96/1.31  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.96/1.31  tff(c_36, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.96/1.31  tff(c_42, plain, (![B_17, A_18]: (v1_xboole_0(B_17) | ~m1_subset_1(B_17, A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.96/1.31  tff(c_50, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_42])).
% 1.96/1.31  tff(c_51, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 1.96/1.31  tff(c_24, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.96/1.31  tff(c_34, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.96/1.31  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.96/1.31  tff(c_96, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k3_subset_1(A_31, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.31  tff(c_105, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_96])).
% 1.96/1.31  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.31  tff(c_148, plain, (![D_38]: (r2_hidden(D_38, k3_subset_1('#skF_3', '#skF_4')) | r2_hidden(D_38, '#skF_4') | ~r2_hidden(D_38, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_2])).
% 1.96/1.31  tff(c_32, plain, (~r2_hidden('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.96/1.31  tff(c_160, plain, (r2_hidden('#skF_5', '#skF_4') | ~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_148, c_32])).
% 1.96/1.31  tff(c_168, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_160])).
% 1.96/1.31  tff(c_171, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_168])).
% 1.96/1.31  tff(c_174, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_171])).
% 1.96/1.31  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_174])).
% 1.96/1.31  tff(c_178, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 1.96/1.31  tff(c_20, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.31  tff(c_185, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_178, c_20])).
% 1.96/1.31  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_185])).
% 1.96/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.31  
% 1.96/1.31  Inference rules
% 1.96/1.31  ----------------------
% 1.96/1.31  #Ref     : 0
% 1.96/1.31  #Sup     : 29
% 1.96/1.31  #Fact    : 0
% 1.96/1.31  #Define  : 0
% 1.96/1.31  #Split   : 6
% 1.96/1.31  #Chain   : 0
% 1.96/1.31  #Close   : 0
% 1.96/1.31  
% 1.96/1.31  Ordering : KBO
% 1.96/1.31  
% 1.96/1.31  Simplification rules
% 1.96/1.31  ----------------------
% 1.96/1.31  #Subsume      : 0
% 1.96/1.31  #Demod        : 1
% 1.96/1.31  #Tautology    : 8
% 1.96/1.31  #SimpNegUnit  : 6
% 1.96/1.31  #BackRed      : 0
% 1.96/1.31  
% 1.96/1.31  #Partial instantiations: 0
% 1.96/1.31  #Strategies tried      : 1
% 1.96/1.31  
% 1.96/1.31  Timing (in seconds)
% 1.96/1.31  ----------------------
% 2.19/1.31  Preprocessing        : 0.32
% 2.19/1.31  Parsing              : 0.16
% 2.19/1.31  CNF conversion       : 0.02
% 2.19/1.31  Main loop            : 0.16
% 2.19/1.31  Inferencing          : 0.06
% 2.19/1.31  Reduction            : 0.04
% 2.19/1.31  Demodulation         : 0.03
% 2.19/1.31  BG Simplification    : 0.02
% 2.19/1.31  Subsumption          : 0.03
% 2.19/1.31  Abstraction          : 0.01
% 2.19/1.31  MUC search           : 0.00
% 2.19/1.31  Cooper               : 0.00
% 2.19/1.31  Total                : 0.51
% 2.19/1.31  Index Insertion      : 0.00
% 2.19/1.31  Index Deletion       : 0.00
% 2.19/1.31  Index Matching       : 0.00
% 2.19/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
