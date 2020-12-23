%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:11 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   61 (  72 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 117 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_49,axiom,(
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

tff(f_108,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_44,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_292,plain,(
    ! [A_89,B_90,C_91] :
      ( ~ r1_xboole_0(A_89,B_90)
      | ~ r2_hidden(C_91,B_90)
      | ~ r2_hidden(C_91,A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_326,plain,(
    ! [C_92] :
      ( ~ r2_hidden(C_92,'#skF_4')
      | ~ r2_hidden(C_92,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_292])).

tff(c_340,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_326])).

tff(c_182,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,k1_tarski(B_69)) = A_68
      | r2_hidden(B_69,A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_191,plain,(
    ! [A_68,B_69] :
      ( r1_xboole_0(A_68,k1_tarski(B_69))
      | r2_hidden(B_69,A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_47,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_221,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | ~ r2_hidden(C_80,k3_xboole_0(A_78,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_236,plain,(
    ! [A_78,B_79,A_5] :
      ( ~ r1_xboole_0(A_78,B_79)
      | r1_xboole_0(A_5,k3_xboole_0(A_78,B_79)) ) ),
    inference(resolution,[status(thm)],[c_8,c_221])).

tff(c_508,plain,(
    ! [A_116,B_117,C_118] :
      ( ~ r1_xboole_0(A_116,k3_xboole_0(B_117,C_118))
      | ~ r1_tarski(A_116,C_118)
      | r1_xboole_0(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_645,plain,(
    ! [A_133,B_134,A_135] :
      ( ~ r1_tarski(A_133,B_134)
      | r1_xboole_0(A_133,A_135)
      | ~ r1_xboole_0(A_135,B_134) ) ),
    inference(resolution,[status(thm)],[c_236,c_508])).

tff(c_671,plain,(
    ! [A_140] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_140)
      | ~ r1_xboole_0(A_140,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_47,c_645])).

tff(c_712,plain,(
    ! [A_141] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_141)
      | r2_hidden('#skF_6',A_141) ) ),
    inference(resolution,[status(thm)],[c_191,c_671])).

tff(c_238,plain,(
    ! [A_81,B_82] :
      ( ~ r1_xboole_0(k3_xboole_0(A_81,B_82),B_82)
      | r1_xboole_0(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_248,plain,(
    ! [A_1,B_2] :
      ( ~ r1_xboole_0(k3_xboole_0(A_1,B_2),A_1)
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_238])).

tff(c_723,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_712,c_248])).

tff(c_744,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_723])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_755,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_744,c_4])).

tff(c_58,plain,(
    ! [B_38,A_39] :
      ( r1_xboole_0(B_38,A_39)
      | ~ r1_xboole_0(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_598,plain,(
    ! [A_126,C_127,B_128] :
      ( ~ r1_xboole_0(A_126,C_127)
      | ~ r1_xboole_0(A_126,B_128)
      | r1_xboole_0(A_126,k2_xboole_0(B_128,C_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1047,plain,(
    ! [B_184,C_185,A_186] :
      ( r1_xboole_0(k2_xboole_0(B_184,C_185),A_186)
      | ~ r1_xboole_0(A_186,C_185)
      | ~ r1_xboole_0(A_186,B_184) ) ),
    inference(resolution,[status(thm)],[c_598,c_4])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1069,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1047,c_40])).

tff(c_1079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_64,c_1069])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.61  
% 3.19/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.61  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.19/1.61  
% 3.19/1.61  %Foreground sorts:
% 3.19/1.61  
% 3.19/1.61  
% 3.19/1.61  %Background operators:
% 3.19/1.61  
% 3.19/1.61  
% 3.19/1.61  %Foreground operators:
% 3.19/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.19/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.19/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.19/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.19/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.61  
% 3.58/1.62  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.58/1.62  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.58/1.62  tff(f_108, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.58/1.62  tff(f_97, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.58/1.62  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.58/1.62  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.58/1.62  tff(f_95, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.58/1.62  tff(f_87, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.58/1.62  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.58/1.62  tff(f_81, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.58/1.62  tff(c_44, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.58/1.62  tff(c_42, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.58/1.62  tff(c_292, plain, (![A_89, B_90, C_91]: (~r1_xboole_0(A_89, B_90) | ~r2_hidden(C_91, B_90) | ~r2_hidden(C_91, A_89))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.58/1.62  tff(c_326, plain, (![C_92]: (~r2_hidden(C_92, '#skF_4') | ~r2_hidden(C_92, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_292])).
% 3.58/1.62  tff(c_340, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_326])).
% 3.58/1.62  tff(c_182, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k1_tarski(B_69))=A_68 | r2_hidden(B_69, A_68))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.58/1.62  tff(c_28, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.58/1.62  tff(c_191, plain, (![A_68, B_69]: (r1_xboole_0(A_68, k1_tarski(B_69)) | r2_hidden(B_69, A_68))), inference(superposition, [status(thm), theory('equality')], [c_182, c_28])).
% 3.58/1.62  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.58/1.62  tff(c_46, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.58/1.62  tff(c_47, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 3.58/1.62  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.58/1.62  tff(c_221, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | ~r2_hidden(C_80, k3_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.58/1.62  tff(c_236, plain, (![A_78, B_79, A_5]: (~r1_xboole_0(A_78, B_79) | r1_xboole_0(A_5, k3_xboole_0(A_78, B_79)))), inference(resolution, [status(thm)], [c_8, c_221])).
% 3.58/1.62  tff(c_508, plain, (![A_116, B_117, C_118]: (~r1_xboole_0(A_116, k3_xboole_0(B_117, C_118)) | ~r1_tarski(A_116, C_118) | r1_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.58/1.62  tff(c_645, plain, (![A_133, B_134, A_135]: (~r1_tarski(A_133, B_134) | r1_xboole_0(A_133, A_135) | ~r1_xboole_0(A_135, B_134))), inference(resolution, [status(thm)], [c_236, c_508])).
% 3.58/1.62  tff(c_671, plain, (![A_140]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_140) | ~r1_xboole_0(A_140, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_47, c_645])).
% 3.58/1.62  tff(c_712, plain, (![A_141]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_141) | r2_hidden('#skF_6', A_141))), inference(resolution, [status(thm)], [c_191, c_671])).
% 3.58/1.62  tff(c_238, plain, (![A_81, B_82]: (~r1_xboole_0(k3_xboole_0(A_81, B_82), B_82) | r1_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.58/1.62  tff(c_248, plain, (![A_1, B_2]: (~r1_xboole_0(k3_xboole_0(A_1, B_2), A_1) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_238])).
% 3.58/1.62  tff(c_723, plain, (r1_xboole_0('#skF_3', '#skF_4') | r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_712, c_248])).
% 3.58/1.62  tff(c_744, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_340, c_723])).
% 3.58/1.62  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.62  tff(c_755, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_744, c_4])).
% 3.58/1.62  tff(c_58, plain, (![B_38, A_39]: (r1_xboole_0(B_38, A_39) | ~r1_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.62  tff(c_64, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_58])).
% 3.58/1.62  tff(c_598, plain, (![A_126, C_127, B_128]: (~r1_xboole_0(A_126, C_127) | ~r1_xboole_0(A_126, B_128) | r1_xboole_0(A_126, k2_xboole_0(B_128, C_127)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.58/1.62  tff(c_1047, plain, (![B_184, C_185, A_186]: (r1_xboole_0(k2_xboole_0(B_184, C_185), A_186) | ~r1_xboole_0(A_186, C_185) | ~r1_xboole_0(A_186, B_184))), inference(resolution, [status(thm)], [c_598, c_4])).
% 3.58/1.62  tff(c_40, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.58/1.62  tff(c_1069, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1047, c_40])).
% 3.58/1.62  tff(c_1079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_755, c_64, c_1069])).
% 3.58/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.62  
% 3.58/1.62  Inference rules
% 3.58/1.62  ----------------------
% 3.58/1.62  #Ref     : 0
% 3.58/1.62  #Sup     : 239
% 3.58/1.62  #Fact    : 0
% 3.58/1.62  #Define  : 0
% 3.58/1.62  #Split   : 0
% 3.58/1.62  #Chain   : 0
% 3.58/1.62  #Close   : 0
% 3.58/1.62  
% 3.58/1.62  Ordering : KBO
% 3.58/1.62  
% 3.58/1.62  Simplification rules
% 3.58/1.62  ----------------------
% 3.58/1.62  #Subsume      : 57
% 3.58/1.62  #Demod        : 26
% 3.58/1.62  #Tautology    : 50
% 3.58/1.62  #SimpNegUnit  : 1
% 3.58/1.62  #BackRed      : 0
% 3.58/1.62  
% 3.58/1.62  #Partial instantiations: 0
% 3.58/1.62  #Strategies tried      : 1
% 3.58/1.62  
% 3.58/1.62  Timing (in seconds)
% 3.58/1.62  ----------------------
% 3.58/1.62  Preprocessing        : 0.37
% 3.58/1.62  Parsing              : 0.21
% 3.58/1.62  CNF conversion       : 0.02
% 3.58/1.62  Main loop            : 0.42
% 3.58/1.62  Inferencing          : 0.15
% 3.58/1.62  Reduction            : 0.14
% 3.58/1.63  Demodulation         : 0.10
% 3.58/1.63  BG Simplification    : 0.02
% 3.58/1.63  Subsumption          : 0.09
% 3.58/1.63  Abstraction          : 0.02
% 3.58/1.63  MUC search           : 0.00
% 3.58/1.63  Cooper               : 0.00
% 3.58/1.63  Total                : 0.82
% 3.58/1.63  Index Insertion      : 0.00
% 3.58/1.63  Index Deletion       : 0.00
% 3.58/1.63  Index Matching       : 0.00
% 3.58/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
