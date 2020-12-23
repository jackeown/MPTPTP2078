%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:07 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   49 (  71 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  92 expanded)
%              Number of equality atoms :   20 (  39 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_17] : k1_subset_1(A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,
    ( k1_subset_1('#skF_4') != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_45,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_63,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_44,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_subset_1('#skF_4') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44])).

tff(c_64,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_46])).

tff(c_30,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_65,plain,(
    ! [A_16] : k4_xboole_0(A_16,'#skF_5') = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_30])).

tff(c_103,plain,(
    ! [D_30,B_31,A_32] :
      ( ~ r2_hidden(D_30,B_31)
      | ~ r2_hidden(D_30,k4_xboole_0(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_112,plain,(
    ! [D_33,A_34] :
      ( ~ r2_hidden(D_33,'#skF_5')
      | ~ r2_hidden(D_33,A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_103])).

tff(c_137,plain,(
    ! [B_44,A_45] :
      ( ~ r2_hidden('#skF_1'('#skF_5',B_44),A_45)
      | r1_tarski('#skF_5',B_44) ) ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_142,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_63])).

tff(c_147,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_148,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_217,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k3_subset_1(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_221,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_217])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k4_xboole_0(B_15,A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_231,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_28])).

tff(c_235,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_231])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.25  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.95/1.25  
% 1.95/1.25  %Foreground sorts:
% 1.95/1.25  
% 1.95/1.25  
% 1.95/1.25  %Background operators:
% 1.95/1.25  
% 1.95/1.25  
% 1.95/1.25  %Foreground operators:
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.95/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.95/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.25  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.95/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.95/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.25  
% 1.95/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.95/1.26  tff(f_52, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.95/1.26  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 1.95/1.26  tff(f_50, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.95/1.26  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.95/1.26  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.95/1.26  tff(f_48, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 1.95/1.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.26  tff(c_32, plain, (![A_17]: (k1_subset_1(A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.26  tff(c_38, plain, (k1_subset_1('#skF_4')!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.95/1.26  tff(c_45, plain, (k1_xboole_0!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38])).
% 1.95/1.26  tff(c_63, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_45])).
% 1.95/1.26  tff(c_44, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_subset_1('#skF_4')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.95/1.26  tff(c_46, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44])).
% 1.95/1.26  tff(c_64, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_63, c_46])).
% 1.95/1.26  tff(c_30, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.95/1.26  tff(c_65, plain, (![A_16]: (k4_xboole_0(A_16, '#skF_5')=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_30])).
% 1.95/1.26  tff(c_103, plain, (![D_30, B_31, A_32]: (~r2_hidden(D_30, B_31) | ~r2_hidden(D_30, k4_xboole_0(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.95/1.26  tff(c_112, plain, (![D_33, A_34]: (~r2_hidden(D_33, '#skF_5') | ~r2_hidden(D_33, A_34))), inference(superposition, [status(thm), theory('equality')], [c_65, c_103])).
% 1.95/1.26  tff(c_137, plain, (![B_44, A_45]: (~r2_hidden('#skF_1'('#skF_5', B_44), A_45) | r1_tarski('#skF_5', B_44))), inference(resolution, [status(thm)], [c_6, c_112])).
% 1.95/1.26  tff(c_142, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_137])).
% 1.95/1.26  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_63])).
% 1.95/1.26  tff(c_147, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_45])).
% 1.95/1.26  tff(c_148, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_45])).
% 1.95/1.26  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.95/1.26  tff(c_217, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k3_subset_1(A_69, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.26  tff(c_221, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_217])).
% 1.95/1.26  tff(c_28, plain, (![A_14, B_15]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k4_xboole_0(B_15, A_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.95/1.26  tff(c_231, plain, (k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_221, c_28])).
% 1.95/1.26  tff(c_235, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_231])).
% 1.95/1.26  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_235])).
% 1.95/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.26  
% 1.95/1.26  Inference rules
% 1.95/1.26  ----------------------
% 1.95/1.26  #Ref     : 0
% 1.95/1.26  #Sup     : 39
% 1.95/1.26  #Fact    : 0
% 1.95/1.26  #Define  : 0
% 1.95/1.26  #Split   : 2
% 1.95/1.26  #Chain   : 0
% 1.95/1.26  #Close   : 0
% 1.95/1.26  
% 1.95/1.26  Ordering : KBO
% 1.95/1.26  
% 1.95/1.26  Simplification rules
% 1.95/1.26  ----------------------
% 1.95/1.26  #Subsume      : 1
% 1.95/1.26  #Demod        : 10
% 1.95/1.26  #Tautology    : 25
% 1.95/1.26  #SimpNegUnit  : 3
% 1.95/1.26  #BackRed      : 3
% 1.95/1.26  
% 1.95/1.26  #Partial instantiations: 0
% 1.95/1.26  #Strategies tried      : 1
% 1.95/1.26  
% 1.95/1.26  Timing (in seconds)
% 1.95/1.26  ----------------------
% 1.95/1.26  Preprocessing        : 0.31
% 1.95/1.26  Parsing              : 0.16
% 1.95/1.26  CNF conversion       : 0.02
% 1.95/1.26  Main loop            : 0.15
% 1.95/1.26  Inferencing          : 0.05
% 1.95/1.26  Reduction            : 0.05
% 1.95/1.26  Demodulation         : 0.03
% 1.95/1.26  BG Simplification    : 0.01
% 1.95/1.26  Subsumption          : 0.03
% 1.95/1.26  Abstraction          : 0.01
% 1.95/1.26  MUC search           : 0.00
% 1.95/1.26  Cooper               : 0.00
% 1.95/1.26  Total                : 0.49
% 1.95/1.26  Index Insertion      : 0.00
% 1.95/1.26  Index Deletion       : 0.00
% 1.95/1.26  Index Matching       : 0.00
% 1.95/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
