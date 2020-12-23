%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:37 EST 2020

% Result     : Theorem 5.50s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :   51 (  55 expanded)
%              Number of leaves         :   29 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  58 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_75,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_54,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_130,plain,(
    ! [A_65,B_66] : k1_enumset1(A_65,A_65,B_66) = k2_tarski(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [E_17,A_11,B_12] : r2_hidden(E_17,k1_enumset1(A_11,B_12,E_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_139,plain,(
    ! [B_66,A_65] : r2_hidden(B_66,k2_tarski(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_14])).

tff(c_52,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_159,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,k3_tarski(B_73))
      | ~ r2_hidden(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5512,plain,(
    ! [A_11792,A_11793,B_11794] :
      ( r1_tarski(A_11792,k2_xboole_0(A_11793,B_11794))
      | ~ r2_hidden(A_11792,k2_tarski(A_11793,B_11794)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_159])).

tff(c_5538,plain,(
    ! [B_11942,A_11943] : r1_tarski(B_11942,k2_xboole_0(A_11943,B_11942)) ),
    inference(resolution,[status(thm)],[c_139,c_5512])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_57,plain,(
    r1_tarski(k2_xboole_0('#skF_5',k1_tarski('#skF_4')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_183,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_tarski(A_82,C_83)
      | ~ r1_tarski(B_84,C_83)
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_192,plain,(
    ! [A_82] :
      ( r1_tarski(A_82,'#skF_5')
      | ~ r1_tarski(A_82,k2_xboole_0('#skF_5',k1_tarski('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_57,c_183])).

tff(c_5584,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_5538,c_192])).

tff(c_36,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [E_17,A_11,C_13] : r2_hidden(E_17,k1_enumset1(A_11,E_17,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_148,plain,(
    ! [A_67,B_68] : r2_hidden(A_67,k2_tarski(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_16])).

tff(c_151,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_148])).

tff(c_193,plain,(
    ! [C_85,B_86,A_87] :
      ( r2_hidden(C_85,B_86)
      | ~ r2_hidden(C_85,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_210,plain,(
    ! [A_18,B_86] :
      ( r2_hidden(A_18,B_86)
      | ~ r1_tarski(k1_tarski(A_18),B_86) ) ),
    inference(resolution,[status(thm)],[c_151,c_193])).

tff(c_5595,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_5584,c_210])).

tff(c_5601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:02:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.50/2.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.08  
% 5.50/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.09  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.50/2.09  
% 5.50/2.09  %Foreground sorts:
% 5.50/2.09  
% 5.50/2.09  
% 5.50/2.09  %Background operators:
% 5.50/2.09  
% 5.50/2.09  
% 5.50/2.09  %Foreground operators:
% 5.50/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.50/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.50/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.50/2.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.50/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.50/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.50/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.50/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.50/2.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.50/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.50/2.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.50/2.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.50/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.50/2.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.50/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.50/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.50/2.09  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.50/2.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.50/2.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.50/2.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.50/2.09  
% 5.50/2.10  tff(f_80, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 5.50/2.10  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.50/2.10  tff(f_55, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.50/2.10  tff(f_75, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.50/2.10  tff(f_73, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 5.50/2.10  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.50/2.10  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.50/2.10  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.50/2.10  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.50/2.10  tff(c_54, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.50/2.10  tff(c_130, plain, (![A_65, B_66]: (k1_enumset1(A_65, A_65, B_66)=k2_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.50/2.10  tff(c_14, plain, (![E_17, A_11, B_12]: (r2_hidden(E_17, k1_enumset1(A_11, B_12, E_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.50/2.10  tff(c_139, plain, (![B_66, A_65]: (r2_hidden(B_66, k2_tarski(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_14])).
% 5.50/2.10  tff(c_52, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.50/2.10  tff(c_159, plain, (![A_72, B_73]: (r1_tarski(A_72, k3_tarski(B_73)) | ~r2_hidden(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.50/2.10  tff(c_5512, plain, (![A_11792, A_11793, B_11794]: (r1_tarski(A_11792, k2_xboole_0(A_11793, B_11794)) | ~r2_hidden(A_11792, k2_tarski(A_11793, B_11794)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_159])).
% 5.50/2.10  tff(c_5538, plain, (![B_11942, A_11943]: (r1_tarski(B_11942, k2_xboole_0(A_11943, B_11942)))), inference(resolution, [status(thm)], [c_139, c_5512])).
% 5.50/2.10  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.50/2.10  tff(c_56, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.50/2.10  tff(c_57, plain, (r1_tarski(k2_xboole_0('#skF_5', k1_tarski('#skF_4')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_56])).
% 5.50/2.10  tff(c_183, plain, (![A_82, C_83, B_84]: (r1_tarski(A_82, C_83) | ~r1_tarski(B_84, C_83) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.50/2.10  tff(c_192, plain, (![A_82]: (r1_tarski(A_82, '#skF_5') | ~r1_tarski(A_82, k2_xboole_0('#skF_5', k1_tarski('#skF_4'))))), inference(resolution, [status(thm)], [c_57, c_183])).
% 5.50/2.10  tff(c_5584, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_5538, c_192])).
% 5.50/2.10  tff(c_36, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.50/2.10  tff(c_16, plain, (![E_17, A_11, C_13]: (r2_hidden(E_17, k1_enumset1(A_11, E_17, C_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.50/2.10  tff(c_148, plain, (![A_67, B_68]: (r2_hidden(A_67, k2_tarski(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_16])).
% 5.50/2.10  tff(c_151, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_148])).
% 5.50/2.10  tff(c_193, plain, (![C_85, B_86, A_87]: (r2_hidden(C_85, B_86) | ~r2_hidden(C_85, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.50/2.10  tff(c_210, plain, (![A_18, B_86]: (r2_hidden(A_18, B_86) | ~r1_tarski(k1_tarski(A_18), B_86))), inference(resolution, [status(thm)], [c_151, c_193])).
% 5.50/2.10  tff(c_5595, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_5584, c_210])).
% 5.50/2.10  tff(c_5601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5595])).
% 5.50/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.10  
% 5.50/2.10  Inference rules
% 5.50/2.10  ----------------------
% 5.50/2.10  #Ref     : 0
% 5.50/2.10  #Sup     : 602
% 5.50/2.10  #Fact    : 18
% 5.50/2.10  #Define  : 0
% 5.50/2.10  #Split   : 0
% 5.50/2.10  #Chain   : 0
% 5.50/2.10  #Close   : 0
% 5.50/2.10  
% 5.50/2.10  Ordering : KBO
% 5.50/2.10  
% 5.50/2.10  Simplification rules
% 5.50/2.10  ----------------------
% 5.50/2.10  #Subsume      : 84
% 5.50/2.10  #Demod        : 125
% 5.50/2.10  #Tautology    : 145
% 5.50/2.10  #SimpNegUnit  : 1
% 5.50/2.10  #BackRed      : 0
% 5.50/2.10  
% 5.50/2.10  #Partial instantiations: 3645
% 5.50/2.10  #Strategies tried      : 1
% 5.50/2.10  
% 5.50/2.10  Timing (in seconds)
% 5.50/2.10  ----------------------
% 5.50/2.10  Preprocessing        : 0.34
% 5.50/2.10  Parsing              : 0.18
% 5.50/2.10  CNF conversion       : 0.03
% 5.50/2.10  Main loop            : 0.95
% 5.50/2.10  Inferencing          : 0.52
% 5.50/2.10  Reduction            : 0.22
% 5.50/2.10  Demodulation         : 0.18
% 5.50/2.10  BG Simplification    : 0.04
% 5.50/2.10  Subsumption          : 0.12
% 5.50/2.10  Abstraction          : 0.04
% 5.50/2.10  MUC search           : 0.00
% 5.50/2.10  Cooper               : 0.00
% 5.50/2.10  Total                : 1.32
% 5.50/2.10  Index Insertion      : 0.00
% 5.50/2.10  Index Deletion       : 0.00
% 5.50/2.10  Index Matching       : 0.00
% 5.50/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
