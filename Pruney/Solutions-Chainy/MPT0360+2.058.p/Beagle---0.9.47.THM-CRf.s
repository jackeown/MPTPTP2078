%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:26 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :   52 (  77 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_212,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_216,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_212])).

tff(c_24,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_xboole_0(A_11,C_13)
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_258,plain,(
    ! [A_67] :
      ( r1_xboole_0(A_67,'#skF_6')
      | ~ r1_tarski(A_67,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_24])).

tff(c_262,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_258])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_266,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_262,c_32])).

tff(c_36,plain,(
    ! [A_19,C_21,B_20] :
      ( r1_xboole_0(A_19,k4_xboole_0(C_21,B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_289,plain,(
    ! [A_68] :
      ( r1_xboole_0(A_68,'#skF_5')
      | ~ r1_tarski(A_68,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_36])).

tff(c_386,plain,(
    ! [A_75] :
      ( k4_xboole_0(A_75,'#skF_5') = A_75
      | ~ r1_tarski(A_75,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_289,c_32])).

tff(c_390,plain,(
    k4_xboole_0('#skF_5','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_386])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_543,plain,(
    ! [D_83] :
      ( ~ r2_hidden(D_83,'#skF_5')
      | ~ r2_hidden(D_83,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_4])).

tff(c_550,plain,
    ( ~ r2_hidden('#skF_3'('#skF_5'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_543])).

tff(c_554,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_550])).

tff(c_557,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_554])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_557])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:28:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.32  
% 2.39/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.39/1.32  
% 2.39/1.32  %Foreground sorts:
% 2.39/1.32  
% 2.39/1.32  
% 2.39/1.32  %Background operators:
% 2.39/1.32  
% 2.39/1.32  
% 2.39/1.32  %Foreground operators:
% 2.39/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.39/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.39/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.39/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.39/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.39/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.39/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.39/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.39/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.32  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.39/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.39/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.32  
% 2.39/1.33  tff(f_76, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 2.39/1.33  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.39/1.33  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.39/1.33  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.39/1.33  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.39/1.33  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.39/1.33  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.39/1.33  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.39/1.33  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.39/1.33  tff(c_44, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.39/1.33  tff(c_42, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.39/1.33  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.39/1.33  tff(c_212, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.33  tff(c_216, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_212])).
% 2.39/1.33  tff(c_24, plain, (![A_11, C_13, B_12]: (r1_xboole_0(A_11, C_13) | ~r1_tarski(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.39/1.33  tff(c_258, plain, (![A_67]: (r1_xboole_0(A_67, '#skF_6') | ~r1_tarski(A_67, k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_216, c_24])).
% 2.39/1.33  tff(c_262, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_258])).
% 2.39/1.33  tff(c_32, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.39/1.33  tff(c_266, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_262, c_32])).
% 2.39/1.33  tff(c_36, plain, (![A_19, C_21, B_20]: (r1_xboole_0(A_19, k4_xboole_0(C_21, B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.39/1.33  tff(c_289, plain, (![A_68]: (r1_xboole_0(A_68, '#skF_5') | ~r1_tarski(A_68, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_266, c_36])).
% 2.39/1.33  tff(c_386, plain, (![A_75]: (k4_xboole_0(A_75, '#skF_5')=A_75 | ~r1_tarski(A_75, '#skF_6'))), inference(resolution, [status(thm)], [c_289, c_32])).
% 2.39/1.33  tff(c_390, plain, (k4_xboole_0('#skF_5', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_44, c_386])).
% 2.39/1.33  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.39/1.33  tff(c_543, plain, (![D_83]: (~r2_hidden(D_83, '#skF_5') | ~r2_hidden(D_83, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_390, c_4])).
% 2.39/1.33  tff(c_550, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_20, c_543])).
% 2.39/1.33  tff(c_554, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_550])).
% 2.39/1.33  tff(c_557, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_20, c_554])).
% 2.39/1.33  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_557])).
% 2.39/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.33  
% 2.39/1.33  Inference rules
% 2.39/1.33  ----------------------
% 2.39/1.33  #Ref     : 0
% 2.39/1.33  #Sup     : 139
% 2.39/1.33  #Fact    : 0
% 2.39/1.33  #Define  : 0
% 2.39/1.33  #Split   : 0
% 2.39/1.33  #Chain   : 0
% 2.39/1.33  #Close   : 0
% 2.39/1.33  
% 2.39/1.33  Ordering : KBO
% 2.39/1.33  
% 2.39/1.33  Simplification rules
% 2.39/1.33  ----------------------
% 2.39/1.33  #Subsume      : 4
% 2.39/1.33  #Demod        : 21
% 2.39/1.33  #Tautology    : 63
% 2.39/1.33  #SimpNegUnit  : 3
% 2.39/1.33  #BackRed      : 2
% 2.39/1.33  
% 2.39/1.33  #Partial instantiations: 0
% 2.39/1.33  #Strategies tried      : 1
% 2.39/1.33  
% 2.39/1.33  Timing (in seconds)
% 2.39/1.33  ----------------------
% 2.39/1.34  Preprocessing        : 0.30
% 2.39/1.34  Parsing              : 0.16
% 2.39/1.34  CNF conversion       : 0.02
% 2.39/1.34  Main loop            : 0.26
% 2.39/1.34  Inferencing          : 0.10
% 2.39/1.34  Reduction            : 0.07
% 2.39/1.34  Demodulation         : 0.05
% 2.39/1.34  BG Simplification    : 0.02
% 2.39/1.34  Subsumption          : 0.05
% 2.39/1.34  Abstraction          : 0.01
% 2.39/1.34  MUC search           : 0.00
% 2.39/1.34  Cooper               : 0.00
% 2.39/1.34  Total                : 0.59
% 2.39/1.34  Index Insertion      : 0.00
% 2.39/1.34  Index Deletion       : 0.00
% 2.39/1.34  Index Matching       : 0.00
% 2.39/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
