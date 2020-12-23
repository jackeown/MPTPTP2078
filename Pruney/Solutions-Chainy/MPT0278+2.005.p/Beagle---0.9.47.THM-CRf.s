%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:22 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  69 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_32,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_1'(A_28,B_29),A_28)
      | r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_358,plain,(
    ! [A_68,B_69] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_68),B_69),A_68)
      | r1_tarski(k1_zfmisc_1(A_68),B_69) ) ),
    inference(resolution,[status(thm)],[c_44,c_20])).

tff(c_34,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_99,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(k2_xboole_0(A_44,C_45),B_46)
      | ~ r1_tarski(C_45,B_46)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_50,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_57,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(k2_xboole_0(A_11,B_12),A_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_50])).

tff(c_103,plain,(
    ! [B_46,C_45] :
      ( k2_xboole_0(B_46,C_45) = B_46
      | ~ r1_tarski(C_45,B_46)
      | ~ r1_tarski(B_46,B_46) ) ),
    inference(resolution,[status(thm)],[c_99,c_57])).

tff(c_110,plain,(
    ! [B_47,C_48] :
      ( k2_xboole_0(B_47,C_48) = B_47
      | ~ r1_tarski(C_48,B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_103])).

tff(c_130,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34,c_110])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,k2_xboole_0(C_10,B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_174,plain,(
    ! [A_50] :
      ( r1_tarski(A_50,'#skF_5')
      | ~ r1_tarski(A_50,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_14])).

tff(c_22,plain,(
    ! [C_20,A_16] :
      ( r2_hidden(C_20,k1_zfmisc_1(A_16))
      | ~ r1_tarski(C_20,A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ! [A_32,B_33] :
      ( ~ r2_hidden('#skF_1'(A_32,B_33),B_33)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [A_32,A_16] :
      ( r1_tarski(A_32,k1_zfmisc_1(A_16))
      | ~ r1_tarski('#skF_1'(A_32,k1_zfmisc_1(A_16)),A_16) ) ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_189,plain,(
    ! [A_32] :
      ( r1_tarski(A_32,k1_zfmisc_1('#skF_5'))
      | ~ r1_tarski('#skF_1'(A_32,k1_zfmisc_1('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_174,c_75])).

tff(c_362,plain,(
    r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_358,c_189])).

tff(c_379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.28  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.07/1.28  
% 2.07/1.28  %Foreground sorts:
% 2.07/1.28  
% 2.07/1.28  
% 2.07/1.28  %Background operators:
% 2.07/1.28  
% 2.07/1.28  
% 2.07/1.28  %Foreground operators:
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.07/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.07/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.28  
% 2.07/1.29  tff(f_62, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.07/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.07/1.29  tff(f_57, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.07/1.29  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.07/1.29  tff(f_50, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.07/1.29  tff(f_44, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.07/1.29  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.07/1.29  tff(c_32, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.07/1.29  tff(c_44, plain, (![A_28, B_29]: (r2_hidden('#skF_1'(A_28, B_29), A_28) | r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.29  tff(c_20, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.07/1.29  tff(c_358, plain, (![A_68, B_69]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_68), B_69), A_68) | r1_tarski(k1_zfmisc_1(A_68), B_69))), inference(resolution, [status(thm)], [c_44, c_20])).
% 2.07/1.29  tff(c_34, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.07/1.29  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.07/1.29  tff(c_99, plain, (![A_44, C_45, B_46]: (r1_tarski(k2_xboole_0(A_44, C_45), B_46) | ~r1_tarski(C_45, B_46) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.29  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.29  tff(c_50, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.07/1.29  tff(c_57, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(k2_xboole_0(A_11, B_12), A_11))), inference(resolution, [status(thm)], [c_16, c_50])).
% 2.07/1.29  tff(c_103, plain, (![B_46, C_45]: (k2_xboole_0(B_46, C_45)=B_46 | ~r1_tarski(C_45, B_46) | ~r1_tarski(B_46, B_46))), inference(resolution, [status(thm)], [c_99, c_57])).
% 2.07/1.29  tff(c_110, plain, (![B_47, C_48]: (k2_xboole_0(B_47, C_48)=B_47 | ~r1_tarski(C_48, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_103])).
% 2.07/1.29  tff(c_130, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_34, c_110])).
% 2.07/1.29  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, k2_xboole_0(C_10, B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.07/1.29  tff(c_174, plain, (![A_50]: (r1_tarski(A_50, '#skF_5') | ~r1_tarski(A_50, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_14])).
% 2.07/1.29  tff(c_22, plain, (![C_20, A_16]: (r2_hidden(C_20, k1_zfmisc_1(A_16)) | ~r1_tarski(C_20, A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.07/1.29  tff(c_64, plain, (![A_32, B_33]: (~r2_hidden('#skF_1'(A_32, B_33), B_33) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.29  tff(c_75, plain, (![A_32, A_16]: (r1_tarski(A_32, k1_zfmisc_1(A_16)) | ~r1_tarski('#skF_1'(A_32, k1_zfmisc_1(A_16)), A_16))), inference(resolution, [status(thm)], [c_22, c_64])).
% 2.07/1.29  tff(c_189, plain, (![A_32]: (r1_tarski(A_32, k1_zfmisc_1('#skF_5')) | ~r1_tarski('#skF_1'(A_32, k1_zfmisc_1('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_174, c_75])).
% 2.07/1.29  tff(c_362, plain, (r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_358, c_189])).
% 2.07/1.29  tff(c_379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_362])).
% 2.07/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.29  
% 2.07/1.29  Inference rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Ref     : 0
% 2.07/1.29  #Sup     : 78
% 2.07/1.29  #Fact    : 0
% 2.07/1.29  #Define  : 0
% 2.07/1.29  #Split   : 1
% 2.07/1.29  #Chain   : 0
% 2.07/1.29  #Close   : 0
% 2.07/1.29  
% 2.07/1.29  Ordering : KBO
% 2.07/1.29  
% 2.07/1.29  Simplification rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Subsume      : 8
% 2.07/1.29  #Demod        : 24
% 2.07/1.29  #Tautology    : 28
% 2.07/1.29  #SimpNegUnit  : 1
% 2.07/1.29  #BackRed      : 0
% 2.07/1.29  
% 2.07/1.29  #Partial instantiations: 0
% 2.07/1.29  #Strategies tried      : 1
% 2.07/1.29  
% 2.07/1.29  Timing (in seconds)
% 2.07/1.29  ----------------------
% 2.07/1.29  Preprocessing        : 0.28
% 2.07/1.30  Parsing              : 0.15
% 2.07/1.30  CNF conversion       : 0.02
% 2.07/1.30  Main loop            : 0.25
% 2.07/1.30  Inferencing          : 0.10
% 2.07/1.30  Reduction            : 0.07
% 2.07/1.30  Demodulation         : 0.05
% 2.07/1.30  BG Simplification    : 0.02
% 2.07/1.30  Subsumption          : 0.06
% 2.07/1.30  Abstraction          : 0.01
% 2.07/1.30  MUC search           : 0.00
% 2.07/1.30  Cooper               : 0.00
% 2.07/1.30  Total                : 0.56
% 2.07/1.30  Index Insertion      : 0.00
% 2.07/1.30  Index Deletion       : 0.00
% 2.07/1.30  Index Matching       : 0.00
% 2.07/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
