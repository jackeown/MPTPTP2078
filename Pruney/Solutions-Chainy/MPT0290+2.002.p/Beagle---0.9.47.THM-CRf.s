%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:33 EST 2020

% Result     : Theorem 13.94s
% Output     : CNFRefutation 14.09s
% Verified   : 
% Statistics : Number of formulae       :   42 (  65 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 ( 112 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_56,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k3_tarski(k3_xboole_0(A,B)),k3_xboole_0(k3_tarski(A),k3_tarski(B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).

tff(c_128,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_4'(A_43,B_44),A_43)
      | r1_tarski(k3_tarski(A_43),B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_988,plain,(
    ! [A_116,B_117,B_118] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_116,B_117),B_118),A_116)
      | r1_tarski(k3_tarski(k3_xboole_0(A_116,B_117)),B_118) ) ),
    inference(resolution,[status(thm)],[c_128,c_14])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,k3_tarski(B_17))
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_119,plain,(
    ! [A_38,B_39] :
      ( ~ r1_tarski('#skF_4'(A_38,B_39),B_39)
      | r1_tarski(k3_tarski(A_38),B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_123,plain,(
    ! [A_38,B_17] :
      ( r1_tarski(k3_tarski(A_38),k3_tarski(B_17))
      | ~ r2_hidden('#skF_4'(A_38,k3_tarski(B_17)),B_17) ) ),
    inference(resolution,[status(thm)],[c_30,c_119])).

tff(c_1025,plain,(
    ! [A_116,B_117] : r1_tarski(k3_tarski(k3_xboole_0(A_116,B_117)),k3_tarski(A_116)) ),
    inference(resolution,[status(thm)],[c_988,c_123])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1029,plain,(
    ! [A_119,B_120] : r1_tarski(k3_tarski(k3_xboole_0(A_119,B_120)),k3_tarski(A_119)) ),
    inference(resolution,[status(thm)],[c_988,c_123])).

tff(c_1038,plain,(
    ! [B_2,A_1] : r1_tarski(k3_tarski(k3_xboole_0(B_2,A_1)),k3_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1029])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_124,plain,(
    ! [C_40,B_41,A_42] :
      ( r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_127,plain,(
    ! [A_3,B_4,B_41] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_41)
      | ~ r1_tarski(A_3,B_41)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_124])).

tff(c_160,plain,(
    ! [D_47,A_48,B_49] :
      ( r2_hidden(D_47,k3_xboole_0(A_48,B_49))
      | ~ r2_hidden(D_47,B_49)
      | ~ r2_hidden(D_47,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3847,plain,(
    ! [A_269,A_270,B_271] :
      ( r1_tarski(A_269,k3_xboole_0(A_270,B_271))
      | ~ r2_hidden('#skF_1'(A_269,k3_xboole_0(A_270,B_271)),B_271)
      | ~ r2_hidden('#skF_1'(A_269,k3_xboole_0(A_270,B_271)),A_270) ) ),
    inference(resolution,[status(thm)],[c_160,c_6])).

tff(c_8835,plain,(
    ! [A_423,A_424,B_425] :
      ( ~ r2_hidden('#skF_1'(A_423,k3_xboole_0(A_424,B_425)),A_424)
      | ~ r1_tarski(A_423,B_425)
      | r1_tarski(A_423,k3_xboole_0(A_424,B_425)) ) ),
    inference(resolution,[status(thm)],[c_127,c_3847])).

tff(c_9007,plain,(
    ! [A_428,B_429,B_430] :
      ( ~ r1_tarski(A_428,B_429)
      | ~ r1_tarski(A_428,B_430)
      | r1_tarski(A_428,k3_xboole_0(B_430,B_429)) ) ),
    inference(resolution,[status(thm)],[c_127,c_8835])).

tff(c_36,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_5','#skF_6')),k3_xboole_0(k3_tarski('#skF_5'),k3_tarski('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_6','#skF_5')),k3_xboole_0(k3_tarski('#skF_6'),k3_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_36])).

tff(c_9032,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_6','#skF_5')),k3_tarski('#skF_5'))
    | ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_6','#skF_5')),k3_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_9007,c_37])).

tff(c_9064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1025,c_1038,c_9032])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:41:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.94/4.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.94/4.74  
% 13.94/4.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.94/4.74  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.94/4.74  
% 13.94/4.74  %Foreground sorts:
% 13.94/4.74  
% 13.94/4.74  
% 13.94/4.74  %Background operators:
% 13.94/4.74  
% 13.94/4.74  
% 13.94/4.74  %Foreground operators:
% 13.94/4.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.94/4.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.94/4.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.94/4.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.94/4.74  tff('#skF_5', type, '#skF_5': $i).
% 13.94/4.74  tff('#skF_6', type, '#skF_6': $i).
% 13.94/4.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.94/4.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.94/4.74  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.94/4.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.94/4.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.94/4.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.94/4.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.94/4.74  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.94/4.74  
% 14.09/4.76  tff(f_56, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 14.09/4.76  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 14.09/4.76  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 14.09/4.76  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.09/4.76  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 14.09/4.76  tff(f_59, negated_conjecture, ~(![A, B]: r1_tarski(k3_tarski(k3_xboole_0(A, B)), k3_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_zfmisc_1)).
% 14.09/4.76  tff(c_128, plain, (![A_43, B_44]: (r2_hidden('#skF_4'(A_43, B_44), A_43) | r1_tarski(k3_tarski(A_43), B_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.09/4.76  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.09/4.76  tff(c_988, plain, (![A_116, B_117, B_118]: (r2_hidden('#skF_4'(k3_xboole_0(A_116, B_117), B_118), A_116) | r1_tarski(k3_tarski(k3_xboole_0(A_116, B_117)), B_118))), inference(resolution, [status(thm)], [c_128, c_14])).
% 14.09/4.76  tff(c_30, plain, (![A_16, B_17]: (r1_tarski(A_16, k3_tarski(B_17)) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.09/4.76  tff(c_119, plain, (![A_38, B_39]: (~r1_tarski('#skF_4'(A_38, B_39), B_39) | r1_tarski(k3_tarski(A_38), B_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.09/4.76  tff(c_123, plain, (![A_38, B_17]: (r1_tarski(k3_tarski(A_38), k3_tarski(B_17)) | ~r2_hidden('#skF_4'(A_38, k3_tarski(B_17)), B_17))), inference(resolution, [status(thm)], [c_30, c_119])).
% 14.09/4.76  tff(c_1025, plain, (![A_116, B_117]: (r1_tarski(k3_tarski(k3_xboole_0(A_116, B_117)), k3_tarski(A_116)))), inference(resolution, [status(thm)], [c_988, c_123])).
% 14.09/4.76  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.09/4.76  tff(c_1029, plain, (![A_119, B_120]: (r1_tarski(k3_tarski(k3_xboole_0(A_119, B_120)), k3_tarski(A_119)))), inference(resolution, [status(thm)], [c_988, c_123])).
% 14.09/4.76  tff(c_1038, plain, (![B_2, A_1]: (r1_tarski(k3_tarski(k3_xboole_0(B_2, A_1)), k3_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1029])).
% 14.09/4.76  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.09/4.76  tff(c_124, plain, (![C_40, B_41, A_42]: (r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.09/4.76  tff(c_127, plain, (![A_3, B_4, B_41]: (r2_hidden('#skF_1'(A_3, B_4), B_41) | ~r1_tarski(A_3, B_41) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_124])).
% 14.09/4.76  tff(c_160, plain, (![D_47, A_48, B_49]: (r2_hidden(D_47, k3_xboole_0(A_48, B_49)) | ~r2_hidden(D_47, B_49) | ~r2_hidden(D_47, A_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.09/4.76  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.09/4.76  tff(c_3847, plain, (![A_269, A_270, B_271]: (r1_tarski(A_269, k3_xboole_0(A_270, B_271)) | ~r2_hidden('#skF_1'(A_269, k3_xboole_0(A_270, B_271)), B_271) | ~r2_hidden('#skF_1'(A_269, k3_xboole_0(A_270, B_271)), A_270))), inference(resolution, [status(thm)], [c_160, c_6])).
% 14.09/4.76  tff(c_8835, plain, (![A_423, A_424, B_425]: (~r2_hidden('#skF_1'(A_423, k3_xboole_0(A_424, B_425)), A_424) | ~r1_tarski(A_423, B_425) | r1_tarski(A_423, k3_xboole_0(A_424, B_425)))), inference(resolution, [status(thm)], [c_127, c_3847])).
% 14.09/4.76  tff(c_9007, plain, (![A_428, B_429, B_430]: (~r1_tarski(A_428, B_429) | ~r1_tarski(A_428, B_430) | r1_tarski(A_428, k3_xboole_0(B_430, B_429)))), inference(resolution, [status(thm)], [c_127, c_8835])).
% 14.09/4.76  tff(c_36, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_5', '#skF_6')), k3_xboole_0(k3_tarski('#skF_5'), k3_tarski('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.09/4.76  tff(c_37, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_6', '#skF_5')), k3_xboole_0(k3_tarski('#skF_6'), k3_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_36])).
% 14.09/4.76  tff(c_9032, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_6', '#skF_5')), k3_tarski('#skF_5')) | ~r1_tarski(k3_tarski(k3_xboole_0('#skF_6', '#skF_5')), k3_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_9007, c_37])).
% 14.09/4.76  tff(c_9064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1025, c_1038, c_9032])).
% 14.09/4.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.09/4.76  
% 14.09/4.76  Inference rules
% 14.09/4.76  ----------------------
% 14.09/4.76  #Ref     : 0
% 14.09/4.76  #Sup     : 2318
% 14.09/4.76  #Fact    : 0
% 14.09/4.76  #Define  : 0
% 14.09/4.76  #Split   : 0
% 14.09/4.76  #Chain   : 0
% 14.09/4.76  #Close   : 0
% 14.09/4.76  
% 14.09/4.76  Ordering : KBO
% 14.09/4.76  
% 14.09/4.76  Simplification rules
% 14.09/4.76  ----------------------
% 14.09/4.76  #Subsume      : 453
% 14.09/4.76  #Demod        : 1126
% 14.09/4.76  #Tautology    : 397
% 14.09/4.76  #SimpNegUnit  : 0
% 14.09/4.76  #BackRed      : 0
% 14.09/4.76  
% 14.09/4.76  #Partial instantiations: 0
% 14.09/4.76  #Strategies tried      : 1
% 14.09/4.76  
% 14.09/4.76  Timing (in seconds)
% 14.09/4.76  ----------------------
% 14.09/4.77  Preprocessing        : 0.44
% 14.09/4.77  Parsing              : 0.22
% 14.09/4.77  CNF conversion       : 0.04
% 14.09/4.77  Main loop            : 3.40
% 14.09/4.77  Inferencing          : 0.82
% 14.09/4.77  Reduction            : 1.29
% 14.09/4.77  Demodulation         : 1.09
% 14.09/4.77  BG Simplification    : 0.12
% 14.09/4.77  Subsumption          : 0.94
% 14.09/4.77  Abstraction          : 0.14
% 14.09/4.77  MUC search           : 0.00
% 14.09/4.77  Cooper               : 0.00
% 14.09/4.77  Total                : 3.88
% 14.09/4.77  Index Insertion      : 0.00
% 14.09/4.77  Index Deletion       : 0.00
% 14.09/4.77  Index Matching       : 0.00
% 14.09/4.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
