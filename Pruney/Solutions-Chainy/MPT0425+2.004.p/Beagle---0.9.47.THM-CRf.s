%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:54 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   41 (  74 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 ( 157 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > k3_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(C,k3_tarski(k2_xboole_0(A,B)))
          & ! [D] :
              ( r2_hidden(D,B)
             => r1_xboole_0(D,C) ) )
       => r1_tarski(C,k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_xboole_0(C,B) )
     => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(c_16,plain,(
    ~ r1_tarski('#skF_5',k3_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    r1_tarski('#skF_5',k3_tarski(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(k3_tarski(A_9),k3_tarski(B_10)) = k3_tarski(k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_67,plain,(
    ! [A_33,B_34,C_35] :
      ( r1_tarski(A_33,B_34)
      | ~ r1_xboole_0(A_33,C_35)
      | ~ r1_tarski(A_33,k2_xboole_0(B_34,C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ! [A_40,A_41,B_42] :
      ( r1_tarski(A_40,k3_tarski(A_41))
      | ~ r1_xboole_0(A_40,k3_tarski(B_42))
      | ~ r1_tarski(A_40,k3_tarski(k2_xboole_0(A_41,B_42))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_109,plain,
    ( r1_tarski('#skF_5',k3_tarski('#skF_3'))
    | ~ r1_xboole_0('#skF_5',k3_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_103])).

tff(c_112,plain,(
    ~ r1_xboole_0('#skF_5',k3_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_109])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_2'(A_30,B_31),A_30)
      | r1_xboole_0(k3_tarski(A_30),B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [D_15] :
      ( r1_xboole_0(D_15,'#skF_5')
      | ~ r2_hidden(D_15,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_59,plain,(
    ! [B_32] :
      ( r1_xboole_0('#skF_2'('#skF_4',B_32),'#skF_5')
      | r1_xboole_0(k3_tarski('#skF_4'),B_32) ) ),
    inference(resolution,[status(thm)],[c_53,c_18])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,(
    ! [C_43,B_44] :
      ( ~ r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,k3_tarski('#skF_4'))
      | r1_xboole_0('#skF_2'('#skF_4',B_44),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_170,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_1'(A_50,B_51),k3_tarski('#skF_4'))
      | r1_xboole_0('#skF_2'('#skF_4',A_50),'#skF_5')
      | r1_xboole_0(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_182,plain,(
    ! [A_52] :
      ( r1_xboole_0('#skF_2'('#skF_4',A_52),'#skF_5')
      | r1_xboole_0(A_52,k3_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_170])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( ~ r1_xboole_0('#skF_2'(A_11,B_12),B_12)
      | r1_xboole_0(k3_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_187,plain,
    ( r1_xboole_0(k3_tarski('#skF_4'),'#skF_5')
    | r1_xboole_0('#skF_5',k3_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_182,c_12])).

tff(c_191,plain,(
    r1_xboole_0(k3_tarski('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_187])).

tff(c_199,plain,(
    ! [C_56] :
      ( ~ r2_hidden(C_56,'#skF_5')
      | ~ r2_hidden(C_56,k3_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_191,c_2])).

tff(c_215,plain,(
    ! [A_57] :
      ( ~ r2_hidden('#skF_1'(A_57,k3_tarski('#skF_4')),'#skF_5')
      | r1_xboole_0(A_57,k3_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_199])).

tff(c_219,plain,(
    r1_xboole_0('#skF_5',k3_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_215])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_112,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:05:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.26  
% 1.87/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > k3_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.87/1.26  
% 1.87/1.26  %Foreground sorts:
% 1.87/1.26  
% 1.87/1.26  
% 1.87/1.26  %Background operators:
% 1.87/1.26  
% 1.87/1.26  
% 1.87/1.26  %Foreground operators:
% 1.87/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.26  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.87/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.87/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.26  
% 1.87/1.27  tff(f_68, negated_conjecture, ~(![A, B, C]: ((r1_tarski(C, k3_tarski(k2_xboole_0(A, B))) & (![D]: (r2_hidden(D, B) => r1_xboole_0(D, C)))) => r1_tarski(C, k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_setfam_1)).
% 1.87/1.27  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 1.87/1.27  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 1.87/1.27  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.87/1.27  tff(f_58, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 1.87/1.27  tff(c_16, plain, (~r1_tarski('#skF_5', k3_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.87/1.27  tff(c_20, plain, (r1_tarski('#skF_5', k3_tarski(k2_xboole_0('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.87/1.27  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(k3_tarski(A_9), k3_tarski(B_10))=k3_tarski(k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.87/1.27  tff(c_67, plain, (![A_33, B_34, C_35]: (r1_tarski(A_33, B_34) | ~r1_xboole_0(A_33, C_35) | ~r1_tarski(A_33, k2_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.27  tff(c_103, plain, (![A_40, A_41, B_42]: (r1_tarski(A_40, k3_tarski(A_41)) | ~r1_xboole_0(A_40, k3_tarski(B_42)) | ~r1_tarski(A_40, k3_tarski(k2_xboole_0(A_41, B_42))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_67])).
% 1.87/1.27  tff(c_109, plain, (r1_tarski('#skF_5', k3_tarski('#skF_3')) | ~r1_xboole_0('#skF_5', k3_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_103])).
% 1.87/1.27  tff(c_112, plain, (~r1_xboole_0('#skF_5', k3_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_16, c_109])).
% 1.87/1.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.27  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.27  tff(c_53, plain, (![A_30, B_31]: (r2_hidden('#skF_2'(A_30, B_31), A_30) | r1_xboole_0(k3_tarski(A_30), B_31))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.87/1.27  tff(c_18, plain, (![D_15]: (r1_xboole_0(D_15, '#skF_5') | ~r2_hidden(D_15, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.87/1.27  tff(c_59, plain, (![B_32]: (r1_xboole_0('#skF_2'('#skF_4', B_32), '#skF_5') | r1_xboole_0(k3_tarski('#skF_4'), B_32))), inference(resolution, [status(thm)], [c_53, c_18])).
% 1.87/1.27  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.27  tff(c_113, plain, (![C_43, B_44]: (~r2_hidden(C_43, B_44) | ~r2_hidden(C_43, k3_tarski('#skF_4')) | r1_xboole_0('#skF_2'('#skF_4', B_44), '#skF_5'))), inference(resolution, [status(thm)], [c_59, c_2])).
% 1.87/1.27  tff(c_170, plain, (![A_50, B_51]: (~r2_hidden('#skF_1'(A_50, B_51), k3_tarski('#skF_4')) | r1_xboole_0('#skF_2'('#skF_4', A_50), '#skF_5') | r1_xboole_0(A_50, B_51))), inference(resolution, [status(thm)], [c_6, c_113])).
% 1.87/1.27  tff(c_182, plain, (![A_52]: (r1_xboole_0('#skF_2'('#skF_4', A_52), '#skF_5') | r1_xboole_0(A_52, k3_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_170])).
% 1.87/1.27  tff(c_12, plain, (![A_11, B_12]: (~r1_xboole_0('#skF_2'(A_11, B_12), B_12) | r1_xboole_0(k3_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.87/1.27  tff(c_187, plain, (r1_xboole_0(k3_tarski('#skF_4'), '#skF_5') | r1_xboole_0('#skF_5', k3_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_182, c_12])).
% 1.87/1.27  tff(c_191, plain, (r1_xboole_0(k3_tarski('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_112, c_187])).
% 1.87/1.27  tff(c_199, plain, (![C_56]: (~r2_hidden(C_56, '#skF_5') | ~r2_hidden(C_56, k3_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_191, c_2])).
% 1.87/1.27  tff(c_215, plain, (![A_57]: (~r2_hidden('#skF_1'(A_57, k3_tarski('#skF_4')), '#skF_5') | r1_xboole_0(A_57, k3_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_199])).
% 1.87/1.27  tff(c_219, plain, (r1_xboole_0('#skF_5', k3_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_215])).
% 1.87/1.27  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_112, c_219])).
% 1.87/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.27  
% 1.87/1.27  Inference rules
% 1.87/1.27  ----------------------
% 1.87/1.27  #Ref     : 0
% 1.87/1.27  #Sup     : 40
% 1.87/1.27  #Fact    : 0
% 1.87/1.27  #Define  : 0
% 1.87/1.27  #Split   : 1
% 1.87/1.27  #Chain   : 0
% 1.87/1.27  #Close   : 0
% 1.87/1.27  
% 1.87/1.27  Ordering : KBO
% 1.87/1.27  
% 1.87/1.27  Simplification rules
% 1.87/1.27  ----------------------
% 1.87/1.27  #Subsume      : 1
% 1.87/1.27  #Demod        : 1
% 1.87/1.27  #Tautology    : 3
% 1.87/1.27  #SimpNegUnit  : 3
% 1.87/1.27  #BackRed      : 0
% 1.87/1.27  
% 1.87/1.27  #Partial instantiations: 0
% 1.87/1.27  #Strategies tried      : 1
% 1.87/1.27  
% 1.87/1.27  Timing (in seconds)
% 1.87/1.27  ----------------------
% 1.87/1.27  Preprocessing        : 0.30
% 1.87/1.27  Parsing              : 0.16
% 1.87/1.27  CNF conversion       : 0.02
% 1.87/1.27  Main loop            : 0.22
% 1.87/1.27  Inferencing          : 0.09
% 1.87/1.27  Reduction            : 0.05
% 1.87/1.27  Demodulation         : 0.03
% 1.87/1.27  BG Simplification    : 0.01
% 1.87/1.27  Subsumption          : 0.05
% 1.87/1.27  Abstraction          : 0.01
% 1.87/1.28  MUC search           : 0.00
% 1.87/1.28  Cooper               : 0.00
% 1.87/1.28  Total                : 0.55
% 1.87/1.28  Index Insertion      : 0.00
% 1.87/1.28  Index Deletion       : 0.00
% 1.87/1.28  Index Matching       : 0.00
% 1.87/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
