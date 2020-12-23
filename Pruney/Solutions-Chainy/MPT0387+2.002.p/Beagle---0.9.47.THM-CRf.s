%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:11 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   32 (  39 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  47 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( r2_hidden(k1_xboole_0,A)
       => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(c_32,plain,(
    k1_setfam_1('#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    r2_hidden(k1_xboole_0,'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(k1_tarski(A_34),B_35) = B_35
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),B_8) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    ! [B_39,A_40] :
      ( k1_xboole_0 != B_39
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_77,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_34,c_69])).

tff(c_68,plain,(
    ! [A_34] : ~ r2_hidden(A_34,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_61,plain,(
    ! [C_36,D_37,A_38] :
      ( r2_hidden(C_36,D_37)
      | ~ r2_hidden(D_37,A_38)
      | ~ r2_hidden(C_36,k1_setfam_1(A_38))
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_67,plain,(
    ! [C_36] :
      ( r2_hidden(C_36,k1_xboole_0)
      | ~ r2_hidden(C_36,k1_setfam_1('#skF_6'))
      | k1_xboole_0 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_79,plain,(
    ! [C_41] : ~ r2_hidden(C_41,k1_setfam_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_68,c_67])).

tff(c_83,plain,(
    k1_setfam_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_79])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:07:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.21  
% 1.81/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.21  %$ r2_hidden > k2_xboole_0 > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 1.81/1.21  
% 1.81/1.21  %Foreground sorts:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Background operators:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Foreground operators:
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.81/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.81/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.81/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.81/1.21  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.81/1.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.81/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.81/1.21  
% 1.81/1.22  tff(f_69, negated_conjecture, ~(![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_setfam_1)).
% 1.81/1.22  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.81/1.22  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 1.81/1.22  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.81/1.22  tff(f_64, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 1.81/1.22  tff(c_32, plain, (k1_setfam_1('#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.81/1.22  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.81/1.22  tff(c_34, plain, (r2_hidden(k1_xboole_0, '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.81/1.22  tff(c_50, plain, (![A_34, B_35]: (k2_xboole_0(k1_tarski(A_34), B_35)=B_35 | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.81/1.22  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.81/1.22  tff(c_69, plain, (![B_39, A_40]: (k1_xboole_0!=B_39 | ~r2_hidden(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_50, c_8])).
% 1.81/1.22  tff(c_77, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_34, c_69])).
% 1.81/1.22  tff(c_68, plain, (![A_34]: (~r2_hidden(A_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_8])).
% 1.81/1.22  tff(c_61, plain, (![C_36, D_37, A_38]: (r2_hidden(C_36, D_37) | ~r2_hidden(D_37, A_38) | ~r2_hidden(C_36, k1_setfam_1(A_38)) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.81/1.22  tff(c_67, plain, (![C_36]: (r2_hidden(C_36, k1_xboole_0) | ~r2_hidden(C_36, k1_setfam_1('#skF_6')) | k1_xboole_0='#skF_6')), inference(resolution, [status(thm)], [c_34, c_61])).
% 1.81/1.22  tff(c_79, plain, (![C_41]: (~r2_hidden(C_41, k1_setfam_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_77, c_68, c_67])).
% 1.81/1.22  tff(c_83, plain, (k1_setfam_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_79])).
% 1.81/1.22  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_83])).
% 1.81/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  Inference rules
% 1.81/1.22  ----------------------
% 1.81/1.22  #Ref     : 0
% 1.81/1.22  #Sup     : 12
% 1.81/1.22  #Fact    : 0
% 1.81/1.22  #Define  : 0
% 1.81/1.22  #Split   : 0
% 1.81/1.22  #Chain   : 0
% 1.81/1.22  #Close   : 0
% 1.81/1.22  
% 1.81/1.22  Ordering : KBO
% 1.81/1.22  
% 1.81/1.22  Simplification rules
% 1.81/1.22  ----------------------
% 1.81/1.22  #Subsume      : 0
% 1.81/1.22  #Demod        : 1
% 1.81/1.22  #Tautology    : 6
% 1.81/1.22  #SimpNegUnit  : 2
% 1.81/1.22  #BackRed      : 0
% 1.81/1.22  
% 1.81/1.22  #Partial instantiations: 0
% 1.81/1.22  #Strategies tried      : 1
% 1.81/1.22  
% 1.81/1.22  Timing (in seconds)
% 1.81/1.22  ----------------------
% 1.81/1.22  Preprocessing        : 0.30
% 1.81/1.22  Parsing              : 0.16
% 1.81/1.22  CNF conversion       : 0.02
% 1.81/1.22  Main loop            : 0.11
% 1.81/1.22  Inferencing          : 0.04
% 1.81/1.22  Reduction            : 0.03
% 1.81/1.22  Demodulation         : 0.02
% 1.81/1.22  BG Simplification    : 0.01
% 1.81/1.22  Subsumption          : 0.03
% 1.81/1.22  Abstraction          : 0.01
% 1.81/1.22  MUC search           : 0.00
% 1.81/1.22  Cooper               : 0.00
% 1.81/1.22  Total                : 0.43
% 1.81/1.22  Index Insertion      : 0.00
% 1.81/1.22  Index Deletion       : 0.00
% 1.81/1.22  Index Matching       : 0.00
% 1.81/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
