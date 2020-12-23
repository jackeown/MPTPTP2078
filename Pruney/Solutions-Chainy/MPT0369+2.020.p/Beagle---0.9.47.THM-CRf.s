%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:53 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   47 (  59 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 ( 109 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    m1_subset_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_57,plain,(
    ! [B_26,A_27] :
      ( v1_xboole_0(B_26)
      | ~ m1_subset_1(B_26,A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_65,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(B_14,A_13)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_147,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = k3_subset_1(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_166,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_147])).

tff(c_258,plain,(
    ! [D_50,A_51,B_52] :
      ( r2_hidden(D_50,k4_xboole_0(A_51,B_52))
      | r2_hidden(D_50,B_52)
      | ~ r2_hidden(D_50,A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_296,plain,(
    ! [D_55] :
      ( r2_hidden(D_55,k3_subset_1('#skF_5','#skF_6'))
      | r2_hidden(D_55,'#skF_6')
      | ~ r2_hidden(D_55,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_258])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_7',k3_subset_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_311,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_296,c_36])).

tff(c_320,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_311])).

tff(c_323,plain,
    ( ~ m1_subset_1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_320])).

tff(c_326,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_323])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_326])).

tff(c_330,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_51,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_4'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_337,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_330,c_55])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n007.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:20:36 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.30  
% 2.06/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.31  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.06/1.31  
% 2.06/1.31  %Foreground sorts:
% 2.06/1.31  
% 2.06/1.31  
% 2.06/1.31  %Background operators:
% 2.06/1.31  
% 2.06/1.31  
% 2.06/1.31  %Foreground operators:
% 2.06/1.31  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.06/1.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.06/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.31  
% 2.06/1.32  tff(f_81, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 2.06/1.32  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.06/1.32  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.06/1.32  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.06/1.32  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.06/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.06/1.32  tff(c_44, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.06/1.32  tff(c_40, plain, (m1_subset_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.06/1.32  tff(c_57, plain, (![B_26, A_27]: (v1_xboole_0(B_26) | ~m1_subset_1(B_26, A_27) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.32  tff(c_65, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_57])).
% 2.06/1.32  tff(c_66, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_65])).
% 2.06/1.32  tff(c_28, plain, (![B_14, A_13]: (r2_hidden(B_14, A_13) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.32  tff(c_38, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.06/1.32  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.06/1.32  tff(c_147, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=k3_subset_1(A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.06/1.32  tff(c_166, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_147])).
% 2.06/1.32  tff(c_258, plain, (![D_50, A_51, B_52]: (r2_hidden(D_50, k4_xboole_0(A_51, B_52)) | r2_hidden(D_50, B_52) | ~r2_hidden(D_50, A_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.32  tff(c_296, plain, (![D_55]: (r2_hidden(D_55, k3_subset_1('#skF_5', '#skF_6')) | r2_hidden(D_55, '#skF_6') | ~r2_hidden(D_55, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_258])).
% 2.06/1.32  tff(c_36, plain, (~r2_hidden('#skF_7', k3_subset_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.06/1.32  tff(c_311, plain, (r2_hidden('#skF_7', '#skF_6') | ~r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_296, c_36])).
% 2.06/1.32  tff(c_320, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_311])).
% 2.06/1.32  tff(c_323, plain, (~m1_subset_1('#skF_7', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_320])).
% 2.06/1.32  tff(c_326, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_323])).
% 2.06/1.32  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_326])).
% 2.06/1.32  tff(c_330, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_65])).
% 2.06/1.32  tff(c_51, plain, (![A_24]: (r2_hidden('#skF_4'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.32  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.32  tff(c_55, plain, (![A_24]: (~v1_xboole_0(A_24) | k1_xboole_0=A_24)), inference(resolution, [status(thm)], [c_51, c_2])).
% 2.06/1.32  tff(c_337, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_330, c_55])).
% 2.06/1.32  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_337])).
% 2.06/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.32  
% 2.06/1.32  Inference rules
% 2.06/1.32  ----------------------
% 2.06/1.32  #Ref     : 0
% 2.06/1.32  #Sup     : 61
% 2.06/1.32  #Fact    : 0
% 2.06/1.32  #Define  : 0
% 2.06/1.32  #Split   : 6
% 2.06/1.32  #Chain   : 0
% 2.06/1.32  #Close   : 0
% 2.06/1.32  
% 2.06/1.32  Ordering : KBO
% 2.06/1.32  
% 2.06/1.32  Simplification rules
% 2.06/1.32  ----------------------
% 2.06/1.32  #Subsume      : 5
% 2.06/1.32  #Demod        : 2
% 2.06/1.32  #Tautology    : 11
% 2.06/1.32  #SimpNegUnit  : 7
% 2.06/1.32  #BackRed      : 0
% 2.06/1.32  
% 2.06/1.32  #Partial instantiations: 0
% 2.06/1.32  #Strategies tried      : 1
% 2.06/1.32  
% 2.06/1.32  Timing (in seconds)
% 2.06/1.32  ----------------------
% 2.06/1.32  Preprocessing        : 0.31
% 2.06/1.32  Parsing              : 0.15
% 2.06/1.32  CNF conversion       : 0.02
% 2.06/1.32  Main loop            : 0.23
% 2.06/1.32  Inferencing          : 0.08
% 2.06/1.32  Reduction            : 0.06
% 2.06/1.32  Demodulation         : 0.04
% 2.06/1.32  BG Simplification    : 0.02
% 2.06/1.32  Subsumption          : 0.05
% 2.06/1.32  Abstraction          : 0.01
% 2.06/1.32  MUC search           : 0.00
% 2.06/1.32  Cooper               : 0.00
% 2.06/1.32  Total                : 0.58
% 2.06/1.32  Index Insertion      : 0.00
% 2.06/1.32  Index Deletion       : 0.00
% 2.06/1.32  Index Matching       : 0.00
% 2.06/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
