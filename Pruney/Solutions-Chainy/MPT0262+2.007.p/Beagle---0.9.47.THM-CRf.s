%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:14 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 101 expanded)
%              Number of leaves         :   19 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 197 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,B)
          & ~ r2_hidden(C,B)
          & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,D)
        & r1_xboole_0(B,D)
        & r1_xboole_0(C,D) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_16,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(k1_tarski(A_15),B_16)
      | r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_39,plain,(
    ! [A_28,B_29,C_30] : k2_xboole_0(k2_xboole_0(A_28,B_29),C_30) = k2_xboole_0(A_28,k2_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [A_28,B_29,C_30] : r1_tarski(k2_xboole_0(A_28,B_29),k2_xboole_0(A_28,k2_xboole_0(B_29,C_30))) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_8])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k2_xboole_0(A_5,B_6),C_7) = k2_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( r1_xboole_0(k2_xboole_0(k2_xboole_0(A_1,B_2),C_3),D_4)
      | ~ r1_xboole_0(C_3,D_4)
      | ~ r1_xboole_0(B_2,D_4)
      | ~ r1_xboole_0(A_1,D_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( r1_xboole_0(k2_xboole_0(A_49,k2_xboole_0(B_50,C_51)),D_52)
      | ~ r1_xboole_0(C_51,D_52)
      | ~ r1_xboole_0(B_50,D_52)
      | ~ r1_xboole_0(A_49,D_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2])).

tff(c_6,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_xboole_0(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_443,plain,(
    ! [A_98,D_99,C_95,B_96,A_97] :
      ( r1_xboole_0(A_97,D_99)
      | ~ r1_tarski(A_97,k2_xboole_0(A_98,k2_xboole_0(B_96,C_95)))
      | ~ r1_xboole_0(C_95,D_99)
      | ~ r1_xboole_0(B_96,D_99)
      | ~ r1_xboole_0(A_98,D_99) ) ),
    inference(resolution,[status(thm)],[c_140,c_6])).

tff(c_487,plain,(
    ! [A_100,B_101,D_102,C_103] :
      ( r1_xboole_0(k2_xboole_0(A_100,B_101),D_102)
      | ~ r1_xboole_0(C_103,D_102)
      | ~ r1_xboole_0(B_101,D_102)
      | ~ r1_xboole_0(A_100,D_102) ) ),
    inference(resolution,[status(thm)],[c_48,c_443])).

tff(c_497,plain,(
    ! [A_104,B_105,B_106,A_107] :
      ( r1_xboole_0(k2_xboole_0(A_104,B_105),B_106)
      | ~ r1_xboole_0(B_105,B_106)
      | ~ r1_xboole_0(A_104,B_106)
      | r2_hidden(A_107,B_106) ) ),
    inference(resolution,[status(thm)],[c_12,c_487])).

tff(c_704,plain,(
    ! [A_143,B_144,B_145,A_146] :
      ( r1_xboole_0(k2_tarski(A_143,B_144),B_145)
      | ~ r1_xboole_0(k1_tarski(B_144),B_145)
      | ~ r1_xboole_0(k1_tarski(A_143),B_145)
      | r2_hidden(A_146,B_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_497])).

tff(c_14,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_725,plain,(
    ! [A_146] :
      ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_2')
      | ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2')
      | r2_hidden(A_146,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_704,c_14])).

tff(c_726,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_725])).

tff(c_729,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_726])).

tff(c_733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_729])).

tff(c_734,plain,(
    ! [A_146] :
      ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_2')
      | r2_hidden(A_146,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_725])).

tff(c_748,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_734])).

tff(c_751,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_748])).

tff(c_755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_751])).

tff(c_756,plain,(
    ! [A_146] : r2_hidden(A_146,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_734])).

tff(c_762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:32:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.42  
% 2.70/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.70/1.42  
% 2.70/1.42  %Foreground sorts:
% 2.70/1.42  
% 2.70/1.42  
% 2.70/1.42  %Background operators:
% 2.70/1.42  
% 2.70/1.42  
% 2.70/1.42  %Foreground operators:
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.42  
% 2.99/1.43  tff(f_61, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.99/1.43  tff(f_50, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 2.99/1.43  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.99/1.43  tff(f_35, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.99/1.43  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.99/1.43  tff(f_33, axiom, (![A, B, C, D]: (((r1_xboole_0(A, D) & r1_xboole_0(B, D)) & r1_xboole_0(C, D)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_xboole_1)).
% 2.99/1.43  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.99/1.43  tff(c_16, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.99/1.43  tff(c_12, plain, (![A_15, B_16]: (r1_xboole_0(k1_tarski(A_15), B_16) | r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.99/1.43  tff(c_18, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.99/1.43  tff(c_10, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.99/1.43  tff(c_39, plain, (![A_28, B_29, C_30]: (k2_xboole_0(k2_xboole_0(A_28, B_29), C_30)=k2_xboole_0(A_28, k2_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.99/1.43  tff(c_8, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.99/1.43  tff(c_48, plain, (![A_28, B_29, C_30]: (r1_tarski(k2_xboole_0(A_28, B_29), k2_xboole_0(A_28, k2_xboole_0(B_29, C_30))))), inference(superposition, [status(thm), theory('equality')], [c_39, c_8])).
% 2.99/1.43  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k2_xboole_0(A_5, B_6), C_7)=k2_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.99/1.43  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (r1_xboole_0(k2_xboole_0(k2_xboole_0(A_1, B_2), C_3), D_4) | ~r1_xboole_0(C_3, D_4) | ~r1_xboole_0(B_2, D_4) | ~r1_xboole_0(A_1, D_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.99/1.43  tff(c_140, plain, (![A_49, B_50, C_51, D_52]: (r1_xboole_0(k2_xboole_0(A_49, k2_xboole_0(B_50, C_51)), D_52) | ~r1_xboole_0(C_51, D_52) | ~r1_xboole_0(B_50, D_52) | ~r1_xboole_0(A_49, D_52))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2])).
% 2.99/1.43  tff(c_6, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_xboole_0(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.99/1.43  tff(c_443, plain, (![A_98, D_99, C_95, B_96, A_97]: (r1_xboole_0(A_97, D_99) | ~r1_tarski(A_97, k2_xboole_0(A_98, k2_xboole_0(B_96, C_95))) | ~r1_xboole_0(C_95, D_99) | ~r1_xboole_0(B_96, D_99) | ~r1_xboole_0(A_98, D_99))), inference(resolution, [status(thm)], [c_140, c_6])).
% 2.99/1.43  tff(c_487, plain, (![A_100, B_101, D_102, C_103]: (r1_xboole_0(k2_xboole_0(A_100, B_101), D_102) | ~r1_xboole_0(C_103, D_102) | ~r1_xboole_0(B_101, D_102) | ~r1_xboole_0(A_100, D_102))), inference(resolution, [status(thm)], [c_48, c_443])).
% 2.99/1.43  tff(c_497, plain, (![A_104, B_105, B_106, A_107]: (r1_xboole_0(k2_xboole_0(A_104, B_105), B_106) | ~r1_xboole_0(B_105, B_106) | ~r1_xboole_0(A_104, B_106) | r2_hidden(A_107, B_106))), inference(resolution, [status(thm)], [c_12, c_487])).
% 2.99/1.43  tff(c_704, plain, (![A_143, B_144, B_145, A_146]: (r1_xboole_0(k2_tarski(A_143, B_144), B_145) | ~r1_xboole_0(k1_tarski(B_144), B_145) | ~r1_xboole_0(k1_tarski(A_143), B_145) | r2_hidden(A_146, B_145))), inference(superposition, [status(thm), theory('equality')], [c_10, c_497])).
% 2.99/1.43  tff(c_14, plain, (~r1_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.99/1.43  tff(c_725, plain, (![A_146]: (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_2') | ~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2') | r2_hidden(A_146, '#skF_2'))), inference(resolution, [status(thm)], [c_704, c_14])).
% 2.99/1.43  tff(c_726, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_725])).
% 2.99/1.43  tff(c_729, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_12, c_726])).
% 2.99/1.43  tff(c_733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_729])).
% 2.99/1.43  tff(c_734, plain, (![A_146]: (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_2') | r2_hidden(A_146, '#skF_2'))), inference(splitRight, [status(thm)], [c_725])).
% 2.99/1.43  tff(c_748, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_734])).
% 2.99/1.43  tff(c_751, plain, (r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_12, c_748])).
% 2.99/1.43  tff(c_755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_751])).
% 2.99/1.43  tff(c_756, plain, (![A_146]: (r2_hidden(A_146, '#skF_2'))), inference(splitRight, [status(thm)], [c_734])).
% 2.99/1.43  tff(c_762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_756, c_16])).
% 2.99/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.43  
% 2.99/1.43  Inference rules
% 2.99/1.43  ----------------------
% 2.99/1.43  #Ref     : 0
% 2.99/1.43  #Sup     : 185
% 2.99/1.43  #Fact    : 0
% 2.99/1.43  #Define  : 0
% 2.99/1.43  #Split   : 2
% 2.99/1.43  #Chain   : 0
% 2.99/1.43  #Close   : 0
% 2.99/1.43  
% 2.99/1.43  Ordering : KBO
% 2.99/1.43  
% 2.99/1.43  Simplification rules
% 2.99/1.43  ----------------------
% 2.99/1.43  #Subsume      : 6
% 2.99/1.43  #Demod        : 126
% 2.99/1.43  #Tautology    : 61
% 2.99/1.43  #SimpNegUnit  : 2
% 2.99/1.43  #BackRed      : 4
% 2.99/1.43  
% 2.99/1.43  #Partial instantiations: 0
% 2.99/1.43  #Strategies tried      : 1
% 2.99/1.43  
% 2.99/1.43  Timing (in seconds)
% 2.99/1.43  ----------------------
% 2.99/1.43  Preprocessing        : 0.27
% 2.99/1.43  Parsing              : 0.15
% 2.99/1.43  CNF conversion       : 0.02
% 2.99/1.43  Main loop            : 0.40
% 2.99/1.43  Inferencing          : 0.16
% 2.99/1.43  Reduction            : 0.13
% 2.99/1.43  Demodulation         : 0.10
% 2.99/1.43  BG Simplification    : 0.02
% 2.99/1.43  Subsumption          : 0.08
% 2.99/1.44  Abstraction          : 0.02
% 2.99/1.44  MUC search           : 0.00
% 2.99/1.44  Cooper               : 0.00
% 2.99/1.44  Total                : 0.70
% 2.99/1.44  Index Insertion      : 0.00
% 2.99/1.44  Index Deletion       : 0.00
% 2.99/1.44  Index Matching       : 0.00
% 2.99/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
