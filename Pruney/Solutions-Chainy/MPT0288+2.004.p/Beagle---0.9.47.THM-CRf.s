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
% DateTime   : Thu Dec  3 09:53:31 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  50 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_32,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_3'(A_15,B_16),A_15)
      | r1_tarski(k3_tarski(A_15),B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_73,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_73])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    ! [D_26,A_27,B_28] :
      ( r2_hidden(D_26,A_27)
      | ~ r2_hidden(D_26,k4_xboole_0(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    ! [D_32,A_33,B_34] :
      ( r2_hidden(D_32,A_33)
      | ~ r2_hidden(D_32,k3_xboole_0(A_33,B_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_101])).

tff(c_145,plain,(
    ! [D_37,A_38,B_39] :
      ( r2_hidden(D_37,A_38)
      | ~ r2_hidden(D_37,k3_xboole_0(B_39,A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_109])).

tff(c_151,plain,(
    ! [D_37] :
      ( r2_hidden(D_37,'#skF_5')
      | ~ r2_hidden(D_37,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_145])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,k3_tarski(B_14))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_221,plain,(
    ! [A_45,B_46] :
      ( ~ r1_tarski('#skF_3'(A_45,B_46),B_46)
      | r1_tarski(k3_tarski(A_45),B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_436,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k3_tarski(A_67),k3_tarski(B_68))
      | ~ r2_hidden('#skF_3'(A_67,k3_tarski(B_68)),B_68) ) ),
    inference(resolution,[status(thm)],[c_26,c_221])).

tff(c_506,plain,(
    ! [A_71] :
      ( r1_tarski(k3_tarski(A_71),k3_tarski('#skF_5'))
      | ~ r2_hidden('#skF_3'(A_71,k3_tarski('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_151,c_436])).

tff(c_510,plain,(
    r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_30,c_506])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:12:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.31  
% 2.33/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.31  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.33/1.31  
% 2.33/1.31  %Foreground sorts:
% 2.33/1.31  
% 2.33/1.31  
% 2.33/1.31  %Background operators:
% 2.33/1.31  
% 2.33/1.31  
% 2.33/1.31  %Foreground operators:
% 2.33/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.33/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.33/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.33/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.33/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.31  
% 2.33/1.32  tff(f_59, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.33/1.32  tff(f_54, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.33/1.32  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.33/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.33/1.32  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.33/1.32  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.33/1.33  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.33/1.33  tff(c_32, plain, (~r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.33  tff(c_30, plain, (![A_15, B_16]: (r2_hidden('#skF_3'(A_15, B_16), A_15) | r1_tarski(k3_tarski(A_15), B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.33/1.33  tff(c_34, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.33  tff(c_73, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.33  tff(c_81, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_73])).
% 2.33/1.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.33/1.33  tff(c_24, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.33/1.33  tff(c_101, plain, (![D_26, A_27, B_28]: (r2_hidden(D_26, A_27) | ~r2_hidden(D_26, k4_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.33/1.33  tff(c_109, plain, (![D_32, A_33, B_34]: (r2_hidden(D_32, A_33) | ~r2_hidden(D_32, k3_xboole_0(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_101])).
% 2.33/1.33  tff(c_145, plain, (![D_37, A_38, B_39]: (r2_hidden(D_37, A_38) | ~r2_hidden(D_37, k3_xboole_0(B_39, A_38)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_109])).
% 2.33/1.33  tff(c_151, plain, (![D_37]: (r2_hidden(D_37, '#skF_5') | ~r2_hidden(D_37, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_145])).
% 2.33/1.33  tff(c_26, plain, (![A_13, B_14]: (r1_tarski(A_13, k3_tarski(B_14)) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.33/1.33  tff(c_221, plain, (![A_45, B_46]: (~r1_tarski('#skF_3'(A_45, B_46), B_46) | r1_tarski(k3_tarski(A_45), B_46))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.33/1.33  tff(c_436, plain, (![A_67, B_68]: (r1_tarski(k3_tarski(A_67), k3_tarski(B_68)) | ~r2_hidden('#skF_3'(A_67, k3_tarski(B_68)), B_68))), inference(resolution, [status(thm)], [c_26, c_221])).
% 2.33/1.33  tff(c_506, plain, (![A_71]: (r1_tarski(k3_tarski(A_71), k3_tarski('#skF_5')) | ~r2_hidden('#skF_3'(A_71, k3_tarski('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_151, c_436])).
% 2.33/1.33  tff(c_510, plain, (r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_506])).
% 2.33/1.33  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_510])).
% 2.33/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.33  
% 2.33/1.33  Inference rules
% 2.33/1.33  ----------------------
% 2.33/1.33  #Ref     : 0
% 2.33/1.33  #Sup     : 124
% 2.33/1.33  #Fact    : 0
% 2.33/1.33  #Define  : 0
% 2.33/1.33  #Split   : 0
% 2.33/1.33  #Chain   : 0
% 2.33/1.33  #Close   : 0
% 2.33/1.33  
% 2.33/1.33  Ordering : KBO
% 2.33/1.33  
% 2.33/1.33  Simplification rules
% 2.33/1.33  ----------------------
% 2.33/1.33  #Subsume      : 18
% 2.33/1.33  #Demod        : 16
% 2.33/1.33  #Tautology    : 47
% 2.33/1.33  #SimpNegUnit  : 1
% 2.33/1.33  #BackRed      : 0
% 2.33/1.33  
% 2.33/1.33  #Partial instantiations: 0
% 2.33/1.33  #Strategies tried      : 1
% 2.33/1.33  
% 2.33/1.33  Timing (in seconds)
% 2.33/1.33  ----------------------
% 2.33/1.33  Preprocessing        : 0.27
% 2.33/1.33  Parsing              : 0.15
% 2.33/1.33  CNF conversion       : 0.02
% 2.33/1.33  Main loop            : 0.26
% 2.33/1.33  Inferencing          : 0.10
% 2.33/1.33  Reduction            : 0.08
% 2.33/1.33  Demodulation         : 0.06
% 2.33/1.33  BG Simplification    : 0.02
% 2.33/1.33  Subsumption          : 0.05
% 2.33/1.33  Abstraction          : 0.01
% 2.33/1.33  MUC search           : 0.00
% 2.33/1.33  Cooper               : 0.00
% 2.33/1.33  Total                : 0.56
% 2.33/1.33  Index Insertion      : 0.00
% 2.33/1.33  Index Deletion       : 0.00
% 2.33/1.33  Index Matching       : 0.00
% 2.33/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
