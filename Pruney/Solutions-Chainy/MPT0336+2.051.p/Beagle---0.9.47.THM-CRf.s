%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:07 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   60 (  95 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 143 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_34,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_132,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_502,plain,(
    ! [A_83,B_84,C_85] :
      ( k3_xboole_0(A_83,k2_xboole_0(B_84,C_85)) = k3_xboole_0(A_83,C_85)
      | ~ r1_xboole_0(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_123,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_128,plain,(
    k3_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_32])).

tff(c_131,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_128])).

tff(c_520,plain,
    ( k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_131])).

tff(c_547,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2,c_520])).

tff(c_38,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_39,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(k1_tarski(A_26),B_27)
      | r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_399,plain,(
    ! [A_72,C_73,B_74] :
      ( r1_xboole_0(A_72,C_73)
      | ~ r1_xboole_0(B_74,C_73)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_883,plain,(
    ! [A_121,B_122,A_123] :
      ( r1_xboole_0(A_121,B_122)
      | ~ r1_tarski(A_121,k1_tarski(A_123))
      | r2_hidden(A_123,B_122) ) ),
    inference(resolution,[status(thm)],[c_28,c_399])).

tff(c_896,plain,(
    ! [B_125] :
      ( r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),B_125)
      | r2_hidden('#skF_5',B_125) ) ),
    inference(resolution,[status(thm)],[c_39,c_883])).

tff(c_202,plain,(
    ! [A_50,B_51] :
      ( ~ r1_xboole_0(k3_xboole_0(A_50,B_51),B_51)
      | r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_223,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(k3_xboole_0(B_2,A_1),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_202])).

tff(c_916,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_896,c_223])).

tff(c_922,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_916])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_343,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,B_66)
      | ~ r2_hidden(C_67,A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_709,plain,(
    ! [C_97,B_98,A_99] :
      ( ~ r2_hidden(C_97,B_98)
      | ~ r2_hidden(C_97,A_99)
      | k3_xboole_0(A_99,B_98) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_343])).

tff(c_718,plain,(
    ! [A_99] :
      ( ~ r2_hidden('#skF_5',A_99)
      | k3_xboole_0(A_99,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_709])).

tff(c_935,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_922,c_718])).

tff(c_948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2,c_935])).

tff(c_949,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_916])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_959,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_949,c_8])).

tff(c_966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_959])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.42  
% 2.76/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.76/1.42  
% 2.76/1.42  %Foreground sorts:
% 2.76/1.42  
% 2.76/1.42  
% 2.76/1.42  %Background operators:
% 2.76/1.42  
% 2.76/1.42  
% 2.76/1.42  %Foreground operators:
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.76/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.76/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.76/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.42  
% 2.76/1.43  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 2.76/1.43  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.76/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.76/1.43  tff(f_69, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.76/1.43  tff(f_80, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.76/1.43  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.76/1.43  tff(f_65, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.76/1.43  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.76/1.43  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.76/1.43  tff(c_34, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.76/1.43  tff(c_132, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.43  tff(c_148, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_132])).
% 2.76/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.43  tff(c_502, plain, (![A_83, B_84, C_85]: (k3_xboole_0(A_83, k2_xboole_0(B_84, C_85))=k3_xboole_0(A_83, C_85) | ~r1_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.76/1.43  tff(c_123, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.43  tff(c_32, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.76/1.43  tff(c_128, plain, (k3_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_123, c_32])).
% 2.76/1.43  tff(c_131, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_128])).
% 2.76/1.43  tff(c_520, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0 | ~r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_502, c_131])).
% 2.76/1.43  tff(c_547, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2, c_520])).
% 2.76/1.43  tff(c_38, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.76/1.43  tff(c_39, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 2.76/1.43  tff(c_28, plain, (![A_26, B_27]: (r1_xboole_0(k1_tarski(A_26), B_27) | r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.76/1.43  tff(c_399, plain, (![A_72, C_73, B_74]: (r1_xboole_0(A_72, C_73) | ~r1_xboole_0(B_74, C_73) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.76/1.43  tff(c_883, plain, (![A_121, B_122, A_123]: (r1_xboole_0(A_121, B_122) | ~r1_tarski(A_121, k1_tarski(A_123)) | r2_hidden(A_123, B_122))), inference(resolution, [status(thm)], [c_28, c_399])).
% 2.76/1.43  tff(c_896, plain, (![B_125]: (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), B_125) | r2_hidden('#skF_5', B_125))), inference(resolution, [status(thm)], [c_39, c_883])).
% 2.76/1.43  tff(c_202, plain, (![A_50, B_51]: (~r1_xboole_0(k3_xboole_0(A_50, B_51), B_51) | r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.76/1.43  tff(c_223, plain, (![B_2, A_1]: (~r1_xboole_0(k3_xboole_0(B_2, A_1), B_2) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_202])).
% 2.76/1.43  tff(c_916, plain, (r1_xboole_0('#skF_2', '#skF_3') | r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_896, c_223])).
% 2.76/1.43  tff(c_922, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_916])).
% 2.76/1.43  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.76/1.43  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.43  tff(c_343, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, B_66) | ~r2_hidden(C_67, A_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.43  tff(c_709, plain, (![C_97, B_98, A_99]: (~r2_hidden(C_97, B_98) | ~r2_hidden(C_97, A_99) | k3_xboole_0(A_99, B_98)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_343])).
% 2.76/1.43  tff(c_718, plain, (![A_99]: (~r2_hidden('#skF_5', A_99) | k3_xboole_0(A_99, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_709])).
% 2.76/1.43  tff(c_935, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_922, c_718])).
% 2.76/1.43  tff(c_948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_2, c_935])).
% 2.76/1.43  tff(c_949, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_916])).
% 2.76/1.43  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.43  tff(c_959, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_949, c_8])).
% 2.76/1.43  tff(c_966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_547, c_959])).
% 2.76/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.43  
% 2.76/1.43  Inference rules
% 2.76/1.43  ----------------------
% 2.76/1.43  #Ref     : 0
% 2.76/1.43  #Sup     : 231
% 2.76/1.43  #Fact    : 0
% 2.76/1.43  #Define  : 0
% 2.76/1.43  #Split   : 4
% 2.76/1.43  #Chain   : 0
% 2.76/1.43  #Close   : 0
% 2.76/1.43  
% 2.76/1.43  Ordering : KBO
% 2.76/1.43  
% 2.76/1.43  Simplification rules
% 2.76/1.43  ----------------------
% 2.76/1.43  #Subsume      : 55
% 2.76/1.43  #Demod        : 36
% 2.76/1.43  #Tautology    : 57
% 2.76/1.43  #SimpNegUnit  : 3
% 2.76/1.43  #BackRed      : 0
% 2.76/1.43  
% 2.76/1.43  #Partial instantiations: 0
% 2.76/1.43  #Strategies tried      : 1
% 2.76/1.43  
% 2.76/1.43  Timing (in seconds)
% 2.76/1.43  ----------------------
% 2.76/1.44  Preprocessing        : 0.29
% 3.08/1.44  Parsing              : 0.16
% 3.08/1.44  CNF conversion       : 0.02
% 3.08/1.44  Main loop            : 0.39
% 3.08/1.44  Inferencing          : 0.14
% 3.08/1.44  Reduction            : 0.12
% 3.08/1.44  Demodulation         : 0.09
% 3.08/1.44  BG Simplification    : 0.02
% 3.08/1.44  Subsumption          : 0.08
% 3.08/1.44  Abstraction          : 0.02
% 3.08/1.44  MUC search           : 0.00
% 3.08/1.44  Cooper               : 0.00
% 3.08/1.44  Total                : 0.71
% 3.08/1.44  Index Insertion      : 0.00
% 3.08/1.44  Index Deletion       : 0.00
% 3.08/1.44  Index Matching       : 0.00
% 3.08/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
