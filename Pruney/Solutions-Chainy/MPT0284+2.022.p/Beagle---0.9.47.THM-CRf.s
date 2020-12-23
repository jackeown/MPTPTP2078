%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:29 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   42 (  59 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  71 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_95,plain,(
    ! [A_40,B_41] : k2_xboole_0(k4_xboole_0(A_40,B_41),k4_xboole_0(B_41,A_40)) = k5_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    ! [A_40,B_41] : r1_tarski(k4_xboole_0(A_40,B_41),k5_xboole_0(A_40,B_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_12])).

tff(c_20,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k1_zfmisc_1(A_21),k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_42,B_43] : r1_tarski(k4_xboole_0(A_42,B_43),k5_xboole_0(A_42,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_12])).

tff(c_116,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),k5_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(k4_xboole_0(A_7,C_9),B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_141,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(k5_xboole_0(A_50,C_51),B_52)
      | ~ r1_tarski(C_51,B_52)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    ! [A_57,B_58,B_59] :
      ( r1_tarski(k2_xboole_0(A_57,B_58),B_59)
      | ~ r1_tarski(k4_xboole_0(B_58,A_57),B_59)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_141])).

tff(c_195,plain,(
    ! [C_60,A_61,B_62] :
      ( r1_tarski(k2_xboole_0(C_60,A_61),B_62)
      | ~ r1_tarski(C_60,B_62)
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_8,c_159])).

tff(c_22,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_202,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_195,c_22])).

tff(c_290,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_293,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_290])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_293])).

tff(c_298,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_302,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_298])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n017.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 13:48:46 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.30  
% 2.03/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.31  %$ r1_tarski > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.03/1.31  
% 2.03/1.31  %Foreground sorts:
% 2.03/1.31  
% 2.03/1.31  
% 2.03/1.31  %Background operators:
% 2.03/1.31  
% 2.03/1.31  
% 2.03/1.31  %Foreground operators:
% 2.03/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.03/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.31  
% 2.35/1.32  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.35/1.32  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.35/1.32  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.35/1.32  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.35/1.32  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 2.35/1.32  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.35/1.32  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.35/1.32  tff(f_56, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 2.35/1.32  tff(c_95, plain, (![A_40, B_41]: (k2_xboole_0(k4_xboole_0(A_40, B_41), k4_xboole_0(B_41, A_40))=k5_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.32  tff(c_12, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.35/1.32  tff(c_101, plain, (![A_40, B_41]: (r1_tarski(k4_xboole_0(A_40, B_41), k5_xboole_0(A_40, B_41)))), inference(superposition, [status(thm), theory('equality')], [c_95, c_12])).
% 2.35/1.32  tff(c_20, plain, (![A_21, B_22]: (r1_tarski(k1_zfmisc_1(A_21), k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.35/1.32  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.32  tff(c_107, plain, (![A_42, B_43]: (r1_tarski(k4_xboole_0(A_42, B_43), k5_xboole_0(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_95, c_12])).
% 2.35/1.32  tff(c_116, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), k5_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 2.35/1.32  tff(c_8, plain, (![A_7, C_9, B_8]: (r1_tarski(k4_xboole_0(A_7, C_9), B_8) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.32  tff(c_14, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.35/1.32  tff(c_141, plain, (![A_50, C_51, B_52]: (r1_tarski(k5_xboole_0(A_50, C_51), B_52) | ~r1_tarski(C_51, B_52) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.35/1.32  tff(c_159, plain, (![A_57, B_58, B_59]: (r1_tarski(k2_xboole_0(A_57, B_58), B_59) | ~r1_tarski(k4_xboole_0(B_58, A_57), B_59) | ~r1_tarski(A_57, B_59))), inference(superposition, [status(thm), theory('equality')], [c_14, c_141])).
% 2.35/1.32  tff(c_195, plain, (![C_60, A_61, B_62]: (r1_tarski(k2_xboole_0(C_60, A_61), B_62) | ~r1_tarski(C_60, B_62) | ~r1_tarski(A_61, B_62))), inference(resolution, [status(thm)], [c_8, c_159])).
% 2.35/1.32  tff(c_22, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.32  tff(c_202, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_195, c_22])).
% 2.35/1.32  tff(c_290, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_202])).
% 2.35/1.32  tff(c_293, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_290])).
% 2.35/1.32  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_293])).
% 2.35/1.32  tff(c_298, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_202])).
% 2.35/1.32  tff(c_302, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_298])).
% 2.35/1.32  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_302])).
% 2.35/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.32  
% 2.35/1.32  Inference rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Ref     : 0
% 2.35/1.32  #Sup     : 68
% 2.35/1.32  #Fact    : 0
% 2.35/1.32  #Define  : 0
% 2.35/1.32  #Split   : 1
% 2.35/1.32  #Chain   : 0
% 2.35/1.32  #Close   : 0
% 2.35/1.32  
% 2.35/1.32  Ordering : KBO
% 2.35/1.32  
% 2.35/1.32  Simplification rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Subsume      : 10
% 2.35/1.32  #Demod        : 23
% 2.35/1.32  #Tautology    : 23
% 2.35/1.32  #SimpNegUnit  : 0
% 2.35/1.32  #BackRed      : 0
% 2.35/1.32  
% 2.35/1.32  #Partial instantiations: 0
% 2.35/1.32  #Strategies tried      : 1
% 2.35/1.32  
% 2.35/1.32  Timing (in seconds)
% 2.35/1.32  ----------------------
% 2.35/1.32  Preprocessing        : 0.32
% 2.35/1.32  Parsing              : 0.17
% 2.35/1.32  CNF conversion       : 0.02
% 2.35/1.32  Main loop            : 0.23
% 2.35/1.32  Inferencing          : 0.09
% 2.35/1.32  Reduction            : 0.08
% 2.35/1.32  Demodulation         : 0.07
% 2.35/1.32  BG Simplification    : 0.01
% 2.35/1.32  Subsumption          : 0.03
% 2.35/1.32  Abstraction          : 0.01
% 2.35/1.32  MUC search           : 0.00
% 2.35/1.32  Cooper               : 0.00
% 2.35/1.32  Total                : 0.57
% 2.35/1.32  Index Insertion      : 0.00
% 2.35/1.32  Index Deletion       : 0.00
% 2.35/1.32  Index Matching       : 0.00
% 2.35/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
